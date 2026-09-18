import JSPProblem.Ladder
import JSPProblem.TwoMin
import JSPProblem.NoConsec
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Int.Interval

/-!
# JSP-000728 — double-shift-free subsets of a matched pair of rails

For `1 ≤ m < s` and a rail pair `{r, r + m}` with `r ∈ Icc 1 (s - m)`, the
union `cls n s r ∪ cls n s (r + m)` of two residue-class "rails" carries a
ladder-shaped constraint graph for `shiftFree2 m s`:

* the `s`-shift links index `k` to index `k + 1` on the *same* rail (the
  ladder verticals);
* the `m`-shift links `(true, k)` on rail `r` to `(false, k)` on rail
  `r + m` (the ladder rungs);
* the only other possible `m`-translate inside the union would need
  `s ∣ 2m`, i.e. `s = 2m`, giving an extra *diagonal* edge `(false, k)` →
  `(true, k + 1)` — a harmless additional constraint that does not
  invalidate the `ladFree` conclusion.

Hence `T ↦ T.image (railIdx n m s r)` injects the double-shift-free
subsets of the union into `ladSets L`, where `L = ((n - r)/s).toNat` is the
length of the longer (`r`-) rail.  This yields the bound

  `card ≤ (ladSets L).card ≤ 4 * (ladSets (L + 1)).card ≤ 12 * 5 ^ (L + 1)`

(`card_powerset_filter_shiftFree2_pair_cls_le_ladSets`,
`card_powerset_filter_shiftFree2_pair_cls_le`,
`card_powerset_filter_shiftFree2_pair_cls_le_five_pow`).
-/

namespace JSP000728

/-- Membership in a residue class, as an indexed progression. -/
theorem mem_cls_iff {n : ℕ} {m r : ℤ} {x : ℤ} :
    x ∈ cls n m r ↔
      ∃ k : ℕ, k < (((n : ℤ) - r) / m).toNat ∧ x = r + m + m * (k : ℤ) := by
  rw [cls_eq_prog, prog_eq_image, Finset.mem_image]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, Finset.mem_range.mp hk, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, Finset.mem_range.mpr hk, rfl⟩

/-- The rail/index coordinates of an element of
`cls n s r ∪ cls n s (r + m)`: elements of the first rail map to
`(true, k)` and elements of the second to `(false, k)`, where `k` is the
position along the progression. -/
def railIdx (n : ℕ) (m s r : ℤ) (x : ℤ) : Bool × ℕ :=
  if x ∈ cls n s r then (true, ((x - r - s) / s).toNat)
    else (false, ((x - r - m - s) / s).toNat)

theorem railIdx_of_mem {n : ℕ} {m s r : ℤ} {x : ℤ} (hx : x ∈ cls n s r) :
    railIdx n m s r x = (true, ((x - r - s) / s).toNat) :=
  ite_eq_left hx

theorem railIdx_of_not_mem {n : ℕ} {m s r : ℤ} {x : ℤ} (hx : x ∉ cls n s r) :
    railIdx n m s r x = (false, ((x - r - m - s) / s).toNat) :=
  ite_eq_right hx

/-- The index map on the `r`-rail: `r + s + s·k ↦ (true, k)`. -/
theorem railIdx_cls {n : ℕ} {m s r : ℤ} (hs : s ≠ 0) {k : ℕ}
    (hk : r + s + s * (k : ℤ) ∈ cls n s r) :
    railIdx n m s r (r + s + s * (k : ℤ)) = (true, k) := by
  rw [railIdx_of_mem hk]
  have e : (r + s + s * (k : ℤ) - r - s) / s = (k : ℤ) := by
    rw [show r + s + s * (k : ℤ) - r - s = s * (k : ℤ) from by ring,
      mul_comm s (k : ℤ)]
    exact Int.mul_ediv_cancel _ hs
  rw [e, Int.toNat_natCast]

/-- The index map on the `(r + m)`-rail: `r + m + s + s·k ↦ (false, k)`
(the point is not on the `r`-rail since the rails are disjoint). -/
theorem railIdx_cls2 {n : ℕ} {m s r : ℤ} (hs : s ≠ 0) {k : ℕ}
    (hk : r + m + s + s * (k : ℤ) ∉ cls n s r) :
    railIdx n m s r (r + m + s + s * (k : ℤ)) = (false, k) := by
  rw [railIdx_of_not_mem hk]
  have e : (r + m + s + s * (k : ℤ) - r - m - s) / s = (k : ℤ) := by
    rw [show r + m + s + s * (k : ℤ) - r - m - s = s * (k : ℤ) from by ring,
      mul_comm s (k : ℤ)]
    exact Int.mul_ediv_cancel _ hs
  rw [e, Int.toNat_natCast]

/-- The two rails are disjoint: `r` and `r + m` are distinct residues in
`Icc 1 s` since `1 ≤ m < s` and `r + m ≤ s`. -/
theorem cls_r_not_mem_of_mem_cls_rm {n : ℕ} {m s r : ℤ}
    (hm : 1 ≤ m) (hms : m < s) (hr : 1 ≤ r) (hrsm : r ≤ s - m) {x : ℤ}
    (hx : x ∈ cls n s (r + m)) : x ∉ cls n s r := by
  have hs : 1 ≤ s := by omega
  have hd : Disjoint (cls n s r) (cls n s (r + m)) :=
    cls_pairwise (n := n) (m := s) hs
      (Finset.mem_coe.mpr (Finset.mem_Icc.mpr ⟨hr, by omega⟩))
      (Finset.mem_coe.mpr (Finset.mem_Icc.mpr ⟨by omega, by omega⟩))
      (by omega)
  exact Finset.disjoint_left.mp hd.symm hx

/-- The index map is injective on the union of the two rails. -/
theorem railIdx_injOn {n : ℕ} {m s r : ℤ} (hm : 1 ≤ m) (hms : m < s)
    (hr : 1 ≤ r) (hrsm : r ≤ s - m) :
    Set.InjOn (railIdx n m s r)
      (↑(cls n s r ∪ cls n s (r + m)) : Set ℤ) := by
  have hs : 0 < s := by omega
  have hsn : s ≠ 0 := ne_of_gt hs
  intro x hx y hy hxy
  rw [Finset.mem_coe, Finset.mem_union] at hx hy
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · obtain ⟨kx, -, rfl⟩ := mem_cls_iff.mp hx
    obtain ⟨ky, -, rfl⟩ := mem_cls_iff.mp hy
    rw [railIdx_cls hsn hx, railIdx_cls hsn hy] at hxy
    have h2 : kx = ky := (Prod.ext_iff.mp hxy).2
    rw [h2]
  · obtain ⟨kx, -, rfl⟩ := mem_cls_iff.mp hx
    obtain ⟨ky, -, rfl⟩ := mem_cls_iff.mp hy
    have hyr := cls_r_not_mem_of_mem_cls_rm hm hms hr hrsm hy
    rw [railIdx_cls hsn hx, railIdx_cls2 hsn hyr] at hxy
    exact Bool.noConfusion (Prod.ext_iff.mp hxy).1
  · obtain ⟨kx, -, rfl⟩ := mem_cls_iff.mp hx
    obtain ⟨ky, -, rfl⟩ := mem_cls_iff.mp hy
    have hxr := cls_r_not_mem_of_mem_cls_rm hm hms hr hrsm hx
    rw [railIdx_cls2 hsn hxr, railIdx_cls hsn hy] at hxy
    exact Bool.noConfusion (Prod.ext_iff.mp hxy).1
  · obtain ⟨kx, -, rfl⟩ := mem_cls_iff.mp hx
    obtain ⟨ky, -, rfl⟩ := mem_cls_iff.mp hy
    have hxr := cls_r_not_mem_of_mem_cls_rm hm hms hr hrsm hx
    have hyr := cls_r_not_mem_of_mem_cls_rm hm hms hr hrsm hy
    rw [railIdx_cls2 hsn hxr, railIdx_cls2 hsn hyr] at hxy
    have h2 : kx = ky := (Prod.ext_iff.mp hxy).2
    rw [h2]

/-- **The ladder bound.**  Double-shift-free subsets of the rail union
inject (via the index map) into the independent sets of the `2 × L`
ladder, where `L = ((n - r)/s).toNat` is the length of the `r`-rail
(the longer of the two). -/
theorem card_powerset_filter_shiftFree2_pair_cls_le_ladSets {n : ℕ} {m s r : ℤ}
    (hm : 1 ≤ m) (hms : m < s) (hr : 1 ≤ r) (hrsm : r ≤ s - m) :
    ((cls n s r ∪ cls n s (r + m)).powerset.filter (shiftFree2 m s)).card ≤
      (ladSets (((n : ℤ) - r) / s).toNat).card := by
  have hs : 0 < s := by omega
  have hsn : s ≠ 0 := ne_of_gt hs
  have hL : (((n : ℤ) - (r + m)) / s).toNat ≤ (((n : ℤ) - r) / s).toNat :=
    Int.toNat_le_toNat (Int.ediv_le_ediv hs (by omega))
  have hinj := railIdx_injOn (n := n) hm hms hr hrsm
  refine Finset.card_le_card_of_injOn (Finset.image (railIdx n m s r)) ?_ ?_
  · intro T hT
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset] at hT
    obtain ⟨hTU, hsm, hss⟩ := hT
    rw [Finset.mem_coe, mem_ladSets]
    refine ⟨?_, ?_, ?_⟩
    · -- the image lies in the `2 × L₁` vertex set
      rintro ⟨b, k⟩ hp
      rw [Finset.mem_image] at hp
      obtain ⟨x, hxT, hxeq⟩ := hp
      rw [mem_ladVert]
      have hxU := hTU hxT
      rw [Finset.mem_union] at hxU
      rcases hxU with hx | hx
      · obtain ⟨kx, hkx, rfl⟩ := mem_cls_iff.mp hx
        rw [railIdx_cls hsn hx] at hxeq
        have hk : k = kx := (Prod.ext_iff.mp hxeq).2.symm
        rw [hk]
        exact hkx
      · obtain ⟨kx, hkx, rfl⟩ := mem_cls_iff.mp hx
        have hxr := cls_r_not_mem_of_mem_cls_rm hm hms hr hrsm hx
        rw [railIdx_cls2 hsn hxr] at hxeq
        have hk : k = kx := (Prod.ext_iff.mp hxeq).2.symm
        rw [hk]
        exact lt_of_lt_of_le hkx hL
    · -- no rail-successor: `x ∈ T` forces `x + s ∉ T`
      intro p hp hC
      rw [Finset.mem_image] at hp hC
      obtain ⟨x, hxT, hpx⟩ := hp
      obtain ⟨y, hyT, hpy⟩ := hC
      have hxU := hTU hxT
      have hyU := hTU hyT
      rw [Finset.mem_union] at hxU hyU
      rcases hxU with hx | hx
      · obtain ⟨kx, -, rfl⟩ := mem_cls_iff.mp hx
        rw [railIdx_cls hsn hx] at hpx
        rw [← hpx] at hpy
        rcases hyU with hy | hy
        · obtain ⟨ky, -, rfl⟩ := mem_cls_iff.mp hy
          rw [railIdx_cls hsn hy] at hpy
          have hky : ky = kx + 1 := congrArg Prod.snd hpy
          have hEq : r + s + s * (ky : ℤ) = (r + s + s * (kx : ℤ)) + s := by
            rw [hky]; push_cast; ring
          rw [hEq] at hyT
          exact hss _ hxT hyT
        · obtain ⟨ky, -, rfl⟩ := mem_cls_iff.mp hy
          have hyr := cls_r_not_mem_of_mem_cls_rm hm hms hr hrsm hy
          rw [railIdx_cls2 hsn hyr] at hpy
          exact Bool.noConfusion (Prod.ext_iff.mp hpy).1
      · obtain ⟨kx, -, rfl⟩ := mem_cls_iff.mp hx
        have hxr := cls_r_not_mem_of_mem_cls_rm hm hms hr hrsm hx
        rw [railIdx_cls2 hsn hxr] at hpx
        rw [← hpx] at hpy
        rcases hyU with hy | hy
        · obtain ⟨ky, -, rfl⟩ := mem_cls_iff.mp hy
          rw [railIdx_cls hsn hy] at hpy
          exact Bool.noConfusion (Prod.ext_iff.mp hpy).1
        · obtain ⟨ky, -, rfl⟩ := mem_cls_iff.mp hy
          have hyr := cls_r_not_mem_of_mem_cls_rm hm hms hr hrsm hy
          rw [railIdx_cls2 hsn hyr] at hpy
          have hky : ky = kx + 1 := congrArg Prod.snd hpy
          have hEq : r + m + s + s * (ky : ℤ) = (r + m + s + s * (kx : ℤ)) + s := by
            rw [hky]; push_cast; ring
          rw [hEq] at hyT
          exact hss _ hxT hyT
    · -- no rung-mate: `x ∈ T` on rail `r` forces `x + m ∉ T` on rail `r+m`
      intro p hp hC
      rw [Finset.mem_image] at hp hC
      obtain ⟨x, hxT, hpx⟩ := hp
      obtain ⟨y, hyT, hpy⟩ := hC
      have hxU := hTU hxT
      have hyU := hTU hyT
      rw [Finset.mem_union] at hxU hyU
      rcases hxU with hx | hx
      · obtain ⟨kx, -, rfl⟩ := mem_cls_iff.mp hx
        rw [railIdx_cls hsn hx] at hpx
        rw [← hpx] at hpy
        rcases hyU with hy | hy
        · obtain ⟨ky, -, rfl⟩ := mem_cls_iff.mp hy
          rw [railIdx_cls hsn hy] at hpy
          exact Bool.noConfusion (Prod.ext_iff.mp hpy).1
        · obtain ⟨ky, -, rfl⟩ := mem_cls_iff.mp hy
          have hyr := cls_r_not_mem_of_mem_cls_rm hm hms hr hrsm hy
          rw [railIdx_cls2 hsn hyr] at hpy
          have hky : ky = kx := congrArg Prod.snd hpy
          have hEq : r + m + s + s * (ky : ℤ) = (r + s + s * (kx : ℤ)) + m := by
            rw [hky]; ring
          rw [hEq] at hyT
          exact hsm _ hxT hyT
      · obtain ⟨kx, -, rfl⟩ := mem_cls_iff.mp hx
        have hxr := cls_r_not_mem_of_mem_cls_rm hm hms hr hrsm hx
        rw [railIdx_cls2 hsn hxr] at hpx
        rw [← hpx] at hpy
        rcases hyU with hy | hy
        · obtain ⟨ky, -, rfl⟩ := mem_cls_iff.mp hy
          rw [railIdx_cls hsn hy] at hpy
          have hky : ky = kx := congrArg Prod.snd hpy
          have hEq : (r + s + s * (ky : ℤ)) + m = r + m + s + s * (kx : ℤ) := by
            rw [hky]; ring
          rw [← hEq] at hxT
          exact hsm _ hyT hxT
        · obtain ⟨ky, -, rfl⟩ := mem_cls_iff.mp hy
          have hyr := cls_r_not_mem_of_mem_cls_rm hm hms hr hrsm hy
          rw [railIdx_cls2 hsn hyr] at hpy
          exact Bool.noConfusion (Prod.ext_iff.mp hpy).1
  · -- `T ↦ T.image railIdx` is injective on subsets of the rail union
    intro T₁ hT₁ T₂ hT₂ h
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset] at hT₁ hT₂
    ext x
    constructor
    · intro hx
      have hxU : x ∈ cls n s r ∪ cls n s (r + m) := hT₁.1 hx
      have hmem : railIdx n m s r x ∈ T₂.image (railIdx n m s r) := by
        rw [← h]
        exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
      obtain ⟨y, hyT, hyeq⟩ := Finset.mem_image.mp hmem
      have hyU : y ∈ cls n s r ∪ cls n s (r + m) := hT₂.1 hyT
      have hxy : x = y := hinj hxU hyU hyeq.symm
      rwa [hxy]
    · intro hx
      have hxU : x ∈ cls n s r ∪ cls n s (r + m) := hT₂.1 hx
      have hmem : railIdx n m s r x ∈ T₁.image (railIdx n m s r) := by
        rw [h]
        exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
      obtain ⟨y, hyT, hyeq⟩ := Finset.mem_image.mp hmem
      have hyU : y ∈ cls n s r ∪ cls n s (r + m) := hT₁.1 hyT
      have hxy : x = y := hinj hxU hyU hyeq.symm
      rwa [hxy]

/-- **Rail-pair bound** (the promised form): at most `4` times the count
of independent sets of the `2 × (L+1)` ladder.  In fact the sharper
`≤ (ladSets L).card` above holds; the extra factor absorbs the
`ladSets_mono` step. -/
theorem card_powerset_filter_shiftFree2_pair_cls_le {n : ℕ} {m s r : ℤ}
    (hm : 1 ≤ m) (hms : m < s) (hr : 1 ≤ r) (hrsm : r ≤ s - m) :
    ((cls n s r ∪ cls n s (r + m)).powerset.filter (shiftFree2 m s)).card ≤
      4 * (ladSets ((((n : ℤ) - r) / s).toNat + 1)).card := by
  refine (card_powerset_filter_shiftFree2_pair_cls_le_ladSets hm hms hr hrsm).trans ?_
  calc (ladSets (((n : ℤ) - r) / s).toNat).card
      ≤ (ladSets ((((n : ℤ) - r) / s).toNat + 1)).card :=
        Finset.card_le_card (ladSets_mono _)
    _ ≤ 4 * (ladSets ((((n : ℤ) - r) / s).toNat + 1)).card :=
        Nat.le_mul_of_pos_left _ (by norm_num)

/-- **Power-of-5 corollary** for product assembly:
`card ≤ 12 * 5 ^ (L + 1)`. -/
theorem card_powerset_filter_shiftFree2_pair_cls_le_five_pow {n : ℕ} {m s r : ℤ}
    (hm : 1 ≤ m) (hms : m < s) (hr : 1 ≤ r) (hrsm : r ≤ s - m) :
    ((cls n s r ∪ cls n s (r + m)).powerset.filter (shiftFree2 m s)).card ≤
      12 * 5 ^ ((((n : ℤ) - r) / s).toNat + 1) := by
  refine (card_powerset_filter_shiftFree2_pair_cls_le hm hms hr hrsm).trans ?_
  calc 4 * (ladSets ((((n : ℤ) - r) / s).toNat + 1)).card
      ≤ 4 * (3 * 5 ^ ((((n : ℤ) - r) / s).toNat + 1)) :=
        Nat.mul_le_mul (le_refl 4) (ladSets_card_le_three_mul_five_pow _)
    _ = 12 * 5 ^ ((((n : ℤ) - r) / s).toNat + 1) := by ring

end JSP000728
