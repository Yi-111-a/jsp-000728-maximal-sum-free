import JSPProblem.StairLadder
import JSPProblem.TwoMin
import JSPProblem.NoConsec

/-!
# JSP-000728 — the unified block-parity staircase matching

For `s = m + k` with `1 ≤ k < m` (i.e. `m < s < 2m`) the mod-`m` rails
carry the *same* `2 × L` staircase graph on every pair `{r, r + k}`: the
`s`-shift maps rail `r` to rail `r + k` one level up (an ascending
staircase rung) while the `m`-shift is vertical.  The near-diagonal
regime `2s ≤ 3m` of `StairLadder.lean` paired `r ∈ Icc 1 (s-m)` with
`r + (s-m)` only once; here the pairing is iterated along each
arithmetic progression `r, r + k, r + 2k, …`: residues are grouped into
*blocks* of size `k` (block index `(r-1)/k`), and each element of an
*even* block is paired with its translate in the next (odd) block.

* `stairBases m k` : `r ∈ [1, m-k]` with even block index `(r-1)/k`;
  `stairPartners m k` is their `+k` image.  Partners have odd block
  index, hence `stairBases_partners_disjoint`, and pairs for distinct
  bases are disjoint (`stairMatch_pairwiseDisjoint`) — the matching is
  a genuine partial involution on the residues `Icc 1 m`.
* `stairLeftover m k` : the uncovered residues — elements of the top
  interval `(m-k, m]` lying in even blocks (at most `k` of them; for
  `k ≥ m/2` this collapses to `Icc (m-k+1) k`, recovering exactly the
  `(3m/2, 2m)` non-wrap matching bases `[1, 2m-s]`, partners
  `[s-m+1, m]`).
* `card_powerset_filter_shiftFree2_modm_pair_le'` : the generalised
  per-pair staircase bound under the sole hypothesis `r + s - m ≤ m`
  (the `2s ≤ 3m` assumption of
  `card_powerset_filter_shiftFree2_modm_pair_cls_le` was only used to
  derive that bound).  Also `..._le_five_pow'` for `4·5^L`.
* `Icc_subset_biUnion_stairMatchCls` : the matching cover of
  `Icc (m+1) n` — every residue `ρ ∈ Icc 1 m` is a base (even block,
  `ρ ≤ m-k`), a partner (odd block, since `block(ρ-k) = block(ρ)-1`),
  or a leftover (even block, `ρ > m-k`).
* `card_powerset_filter_shiftFree2_Icc_le_stairMatchProd` : the product
  bound `∏_{r ∈ bases} a(L_r) · ∏_{ρ ∈ leftover} F_{L_ρ+2}`.
* `card_powerset_filter_shiftFree2_Icc_le_stairMatchClosed` : the
  closed form `4^{(m-k)₊} · (5^{(n-m)₊} · 2^{k₊})`.
-/

namespace JSP000728

/-! ### The generalised per-pair bound (`r + s - m ≤ m`) -/

/-- Disjointness of the mod-`m` rails `r` and `r + s - m` under the sole
hypothesis `r + s - m ≤ m` (generalising
`cls_r_not_mem_of_mem_cls_rsm`, which derived the same membership bound
from `r ≤ s - m` and `2s ≤ 3m`). -/
theorem cls_r_not_mem_of_mem_cls_rsm' {n : ℕ} {m s r : ℤ}
    (hm : 1 ≤ m) (hms : m < s) (hrsm : r + s - m ≤ m) (hr : 1 ≤ r)
    {x : ℤ} (hx : x ∈ cls n m (r + s - m)) :
    x ∉ cls n m r := by
  have hd : Disjoint (cls n m r) (cls n m (r + s - m)) :=
    cls_pairwise (n := n) (m := m) hm
      (Finset.mem_coe.mpr (Finset.mem_Icc.mpr ⟨hr, by omega⟩))
      (Finset.mem_coe.mpr (Finset.mem_Icc.mpr ⟨by omega, by omega⟩))
      (by omega)
  exact Finset.disjoint_left.mp hd.symm hx

/-- The index map is injective on the union of the two rails (weak
hypothesis version). -/
theorem stairIdx_injOn' {n : ℕ} {m s r : ℤ} (hm : 1 ≤ m) (hms : m < s)
    (hrsm : r + s - m ≤ m) (hr : 1 ≤ r) :
    Set.InjOn (stairIdx n m s r)
      (↑(cls n m r ∪ cls n m (r + s - m)) : Set ℤ) := by
  have hm0 : m ≠ 0 := by omega
  intro x hx y hy hxy
  rw [Finset.mem_coe, Finset.mem_union] at hx hy
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · obtain ⟨kx, -, rfl⟩ := stair_mem_cls_iff.mp hx
    obtain ⟨ky, -, rfl⟩ := stair_mem_cls_iff.mp hy
    rw [stairIdx_cls hm0 hx, stairIdx_cls hm0 hy] at hxy
    have h2 : kx = ky := (Prod.ext_iff.mp hxy).2
    rw [h2]
  · obtain ⟨kx, -, rfl⟩ := stair_mem_cls_iff.mp hx
    obtain ⟨ky, -, rfl⟩ := stair_mem_cls_iff.mp hy
    have hyr := cls_r_not_mem_of_mem_cls_rsm' hm hms hrsm hr hy
    rw [stairIdx_cls hm0 hx, stairIdx_cls2 hm0 hyr] at hxy
    exact Bool.noConfusion (Prod.ext_iff.mp hxy).1
  · obtain ⟨kx, -, rfl⟩ := stair_mem_cls_iff.mp hx
    obtain ⟨ky, -, rfl⟩ := stair_mem_cls_iff.mp hy
    have hxr := cls_r_not_mem_of_mem_cls_rsm' hm hms hrsm hr hx
    rw [stairIdx_cls2 hm0 hxr, stairIdx_cls hm0 hy] at hxy
    exact Bool.noConfusion (Prod.ext_iff.mp hxy).1
  · obtain ⟨kx, -, rfl⟩ := stair_mem_cls_iff.mp hx
    obtain ⟨ky, -, rfl⟩ := stair_mem_cls_iff.mp hy
    have hxr := cls_r_not_mem_of_mem_cls_rsm' hm hms hrsm hr hx
    have hyr := cls_r_not_mem_of_mem_cls_rsm' hm hms hrsm hr hy
    rw [stairIdx_cls2 hm0 hxr, stairIdx_cls2 hm0 hyr] at hxy
    have h2 : kx = ky := (Prod.ext_iff.mp hxy).2
    rw [h2]

/-- **The generalised staircase bound.**  For `r + s - m ≤ m` (i.e. the
partner residue stays inside `Icc 1 m`), double-shift-free subsets of
the mod-`m` rail pair inject into the independent sets of the `2 × L`
staircase, exactly as in
`card_powerset_filter_shiftFree2_modm_pair_cls_le` — whose `2s ≤ 3m`
hypothesis was only ever used to obtain `r + s - m ≤ m`. -/
theorem card_powerset_filter_shiftFree2_modm_pair_le' {n : ℕ} {m s r : ℤ}
    (hm : 1 ≤ m) (hms : m < s) (hrsm : r + s - m ≤ m) (hr : 1 ≤ r) :
    ((cls n m r ∪ cls n m (r + s - m)).powerset.filter
        (shiftFree2 m s)).card ≤
      (stairSets (((n : ℤ) - r) / m).toNat).card := by
  have hmpos : 0 < m := by omega
  have hm0 : m ≠ 0 := ne_of_gt hmpos
  have hL : (((n : ℤ) - (r + s - m)) / m).toNat ≤
      (((n : ℤ) - r) / m).toNat :=
    Int.toNat_le_toNat (Int.ediv_le_ediv hmpos (by omega))
  have hinj := stairIdx_injOn' (n := n) hm hms hrsm hr
  refine Finset.card_le_card_of_injOn (Finset.image (stairIdx n m s r))
    ?_ ?_
  · intro T hT
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset] at hT
    obtain ⟨hTU, hsmT, hssT⟩ := hT
    rw [Finset.mem_coe, mem_stairSets]
    refine ⟨?_, ?_, ?_⟩
    · -- the image lies in the `2 × L` vertex set
      rintro ⟨b, k⟩ hp
      rw [Finset.mem_image] at hp
      obtain ⟨x, hxT, hxeq⟩ := hp
      rw [mem_stairVert]
      have hxU := hTU hxT
      rw [Finset.mem_union] at hxU
      rcases hxU with hx | hx
      · obtain ⟨kx, hkx, rfl⟩ := stair_mem_cls_iff.mp hx
        rw [stairIdx_cls hm0 hx] at hxeq
        have hk : k = kx := (Prod.ext_iff.mp hxeq).2.symm
        rw [hk]
        exact hkx
      · obtain ⟨kx, hkx, rfl⟩ := stair_mem_cls_iff.mp hx
        have hxr := cls_r_not_mem_of_mem_cls_rsm' hm hms hrsm hr hx
        rw [stairIdx_cls2 hm0 hxr] at hxeq
        have hk : k = kx := (Prod.ext_iff.mp hxeq).2.symm
        rw [hk]
        exact lt_of_lt_of_le hkx hL
    · -- no rail-successor: `x ∈ T` forces `x + m ∉ T`
      intro p hp hC
      rw [Finset.mem_image] at hp hC
      obtain ⟨x, hxT, hpx⟩ := hp
      obtain ⟨y, hyT, hpy⟩ := hC
      have hxU := hTU hxT
      have hyU := hTU hyT
      rw [Finset.mem_union] at hxU hyU
      rcases hxU with hx | hx
      · obtain ⟨kx, -, rfl⟩ := stair_mem_cls_iff.mp hx
        rw [stairIdx_cls hm0 hx] at hpx
        rw [← hpx] at hpy
        rcases hyU with hy | hy
        · obtain ⟨ky, -, rfl⟩ := stair_mem_cls_iff.mp hy
          rw [stairIdx_cls hm0 hy] at hpy
          have hky : ky = kx + 1 := congrArg Prod.snd hpy
          have hEq : r + m + m * (ky : ℤ) =
              (r + m + m * (kx : ℤ)) + m := by
            rw [hky]; push_cast; ring
          rw [hEq] at hyT
          exact hsmT _ hxT hyT
        · obtain ⟨ky, -, rfl⟩ := stair_mem_cls_iff.mp hy
          have hyr := cls_r_not_mem_of_mem_cls_rsm' hm hms hrsm hr hy
          rw [stairIdx_cls2 hm0 hyr] at hpy
          exact Bool.noConfusion (Prod.ext_iff.mp hpy).1
      · obtain ⟨kx, -, rfl⟩ := stair_mem_cls_iff.mp hx
        have hxr := cls_r_not_mem_of_mem_cls_rsm' hm hms hrsm hr hx
        rw [stairIdx_cls2 hm0 hxr] at hpx
        rw [← hpx] at hpy
        rcases hyU with hy | hy
        · obtain ⟨ky, -, rfl⟩ := stair_mem_cls_iff.mp hy
          rw [stairIdx_cls hm0 hy] at hpy
          exact Bool.noConfusion (Prod.ext_iff.mp hpy).1
        · obtain ⟨ky, -, rfl⟩ := stair_mem_cls_iff.mp hy
          have hyr := cls_r_not_mem_of_mem_cls_rsm' hm hms hrsm hr hy
          rw [stairIdx_cls2 hm0 hyr] at hpy
          have hky : ky = kx + 1 := congrArg Prod.snd hpy
          have hEq : (r + s - m) + m + m * (ky : ℤ) =
              ((r + s - m) + m + m * (kx : ℤ)) + m := by
            rw [hky]; push_cast; ring
          rw [hEq] at hyT
          exact hsmT _ hxT hyT
    · -- no ascending rung: `x ∈ T` on rail `r` forces `x + s ∉ T`
      intro p hp hpf hC
      rw [Finset.mem_image] at hp hC
      obtain ⟨x, hxT, hpx⟩ := hp
      obtain ⟨y, hyT, hpy⟩ := hC
      have hxU := hTU hxT
      have hyU := hTU hyT
      rw [Finset.mem_union] at hxU hyU
      rcases hxU with hx | hx
      · obtain ⟨kx, -, rfl⟩ := stair_mem_cls_iff.mp hx
        rw [stairIdx_cls hm0 hx] at hpx
        rw [← hpx] at hpy
        rcases hyU with hy | hy
        · obtain ⟨ky, -, rfl⟩ := stair_mem_cls_iff.mp hy
          rw [stairIdx_cls hm0 hy] at hpy
          exact Bool.noConfusion (Prod.ext_iff.mp hpy).1
        · obtain ⟨ky, -, rfl⟩ := stair_mem_cls_iff.mp hy
          have hyr := cls_r_not_mem_of_mem_cls_rsm' hm hms hrsm hr hy
          rw [stairIdx_cls2 hm0 hyr] at hpy
          have hky : ky = kx + 1 := congrArg Prod.snd hpy
          have hEq : (r + s - m) + m + m * (ky : ℤ) =
              (r + m + m * (kx : ℤ)) + s := by
            rw [hky]; push_cast; ring
          rw [hEq] at hyT
          exact hssT _ hxT hyT
      · -- `p.1 = true` contradicts `hpf : p.1 = false`
        obtain ⟨kx, -, rfl⟩ := stair_mem_cls_iff.mp hx
        have hxr := cls_r_not_mem_of_mem_cls_rsm' hm hms hrsm hr hx
        rw [stairIdx_cls2 hm0 hxr] at hpx
        rw [← hpx] at hpf
        exact Bool.noConfusion hpf
  · -- `T ↦ T.image stairIdx` is injective on subsets of the rail union
    intro T₁ hT₁ T₂ hT₂ h
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset] at hT₁ hT₂
    ext x
    constructor
    · intro hx
      have hxU : x ∈ cls n m r ∪ cls n m (r + s - m) := hT₁.1 hx
      have hmem : stairIdx n m s r x ∈ T₂.image (stairIdx n m s r) := by
        rw [← h]
        exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
      obtain ⟨y, hyT, hyeq⟩ := Finset.mem_image.mp hmem
      have hyU : y ∈ cls n m r ∪ cls n m (r + s - m) := hT₂.1 hyT
      have hxy : x = y := hinj hxU hyU hyeq.symm
      rwa [hxy]
    · intro hx
      have hxU : x ∈ cls n m r ∪ cls n m (r + s - m) := hT₂.1 hx
      have hmem : stairIdx n m s r x ∈ T₁.image (stairIdx n m s r) := by
        rw [h]
        exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
      obtain ⟨y, hyT, hyeq⟩ := Finset.mem_image.mp hmem
      have hyU : y ∈ cls n m r ∪ cls n m (r + s - m) := hT₁.1 hyT
      have hxy : x = y := hinj hxU hyU hyeq.symm
      rwa [hxy]

/-- **Power-of-5 corollary** (weak hypothesis version): the pair factor
is at most `4 * 5 ^ L` where `L` is the `r`-rail length. -/
theorem card_powerset_filter_shiftFree2_modm_pair_le_five_pow' {n : ℕ}
    {m s r : ℤ} (hm : 1 ≤ m) (hms : m < s) (hrsm : r + s - m ≤ m)
    (hr : 1 ≤ r) :
    ((cls n m r ∪ cls n m (r + s - m)).powerset.filter
        (shiftFree2 m s)).card ≤
      4 * 5 ^ (((n : ℤ) - r) / m).toNat :=
  (card_powerset_filter_shiftFree2_modm_pair_le' hm hms hrsm hr).trans
    (stairSets_card_le_four_mul_five_pow _)

/-! ### The block-parity matching on the residues `Icc 1 m` -/

/-- The *staircase bases*: residues `r ∈ [1, m-k]` whose block index
`(r-1)/k` is even.  For `s = m + k` the `s`-shift sends rail `r` to rail
`r + k`; pairing each base with its `+k` translate covers `[1, m]` up to
an even-block leftover. -/
def stairBases (m k : ℤ) : Finset ℤ :=
  (Finset.Icc 1 (m - k)).filter fun r => ((r - 1) / k) % 2 = 0

/-- The staircase partners: the bases shifted up by one block step `k`
(elements of odd blocks). -/
def stairPartners (m k : ℤ) : Finset ℤ :=
  (stairBases m k).image fun r => r + k

/-- The leftover residues: elements of the top interval `(m-k, m]`
whose block index is even (at most `k` of them). -/
def stairLeftover (m k : ℤ) : Finset ℤ :=
  (Finset.Icc (m - k + 1) m).filter fun r => ((r - 1) / k) % 2 = 0

/-- Membership in `stairBases m k`. -/
theorem mem_stairBases {m k r : ℤ} :
    r ∈ stairBases m k ↔
      1 ≤ r ∧ r ≤ m - k ∧ ((r - 1) / k) % 2 = 0 := by
  rw [stairBases, Finset.mem_filter, Finset.mem_Icc, and_assoc]

/-- Membership in `stairPartners m k`: `ρ` is a partner iff `ρ - k` is a
base. -/
theorem mem_stairPartners {m k ρ : ℤ} :
    ρ ∈ stairPartners m k ↔ ∃ r ∈ stairBases m k, r + k = ρ := by
  simp [stairPartners]

/-- Membership in `stairLeftover m k`. -/
theorem mem_stairLeftover {m k ρ : ℤ} :
    ρ ∈ stairLeftover m k ↔
      m - k + 1 ≤ ρ ∧ ρ ≤ m ∧ ((ρ - 1) / k) % 2 = 0 := by
  rw [stairLeftover, Finset.mem_filter, Finset.mem_Icc, and_assoc]

/-- The block index of `r + k` is one more than that of `r`. -/
theorem stair_block_add {r k : ℤ} (hk : 1 ≤ k) :
    (r + k - 1) / k = (r - 1) / k + 1 := by
  have e : r + k - 1 = (r - 1) + k * 1 := by ring
  rw [e, Int.add_mul_ediv_left _ _ (by omega : k ≠ 0)]

/-- The block index of `r - k` is one less than that of `r`. -/
theorem stair_block_sub {r k : ℤ} (hk : 1 ≤ k) :
    (r - k - 1) / k = (r - 1) / k - 1 := by
  have e : r - k - 1 = (r - 1) + k * (-1) := by ring
  rw [e, Int.add_mul_ediv_left _ _ (by omega : k ≠ 0)]
  ring

/-- Bases and partners are disjoint: a base has even block index while
its partner's block index is odd. -/
theorem stairBases_partners_disjoint {m k : ℤ} (hk : 1 ≤ k) :
    Disjoint (stairBases m k) (stairPartners m k) := by
  rw [Finset.disjoint_left]
  intro ρ hρb hρp
  rw [mem_stairPartners] at hρp
  obtain ⟨r, hr, rfl⟩ := hρp
  rw [mem_stairBases] at hr hρb
  obtain ⟨hr1, -, hpar⟩ := hr
  obtain ⟨-, -, hparρ⟩ := hρb
  rw [stair_block_add hk] at hparρ
  have hq : Even ((r - 1) / k) := Int.even_iff.mpr hpar
  have h1 : ((r - 1) / k + 1) % 2 = 1 := Int.odd_iff.mp hq.add_one
  omega

/-- The staircase matching is a genuine partial involution: the rail
pairs `{r, r + k}` for distinct bases `r` are pairwise disjoint. -/
theorem stairMatch_pairwiseDisjoint {n : ℕ} {m k : ℤ} (hk : 1 ≤ k) :
    (↑(stairBases m k) : Set ℤ).PairwiseDisjoint
      fun r => cls n m r ∪ cls n m (r + k) := by
  intro r₁ hr₁ r₂ hr₂ hne
  show Disjoint (cls n m r₁ ∪ cls n m (r₁ + k))
    (cls n m r₂ ∪ cls n m (r₂ + k))
  rw [Finset.mem_coe, mem_stairBases] at hr₁
  rw [Finset.mem_coe, mem_stairBases] at hr₂
  obtain ⟨hr₁1, hr₁m, hr₁p⟩ := hr₁
  obtain ⟨hr₂1, hr₂m, hr₂p⟩ := hr₂
  have hm : 1 ≤ m := by omega
  have hd := stairBases_partners_disjoint (m := m) hk
  have h12 : r₁ ≠ r₂ + k := by
    intro h
    have hp : r₁ ∈ stairPartners m k := by
      rw [mem_stairPartners]
      exact ⟨r₂, by
        rw [mem_stairBases]; exact ⟨hr₂1, hr₂m, hr₂p⟩, h.symm⟩
    exact Finset.disjoint_left.mp hd
      (mem_stairBases.mpr ⟨hr₁1, hr₁m, hr₁p⟩) hp
  have h21 : r₂ ≠ r₁ + k := by
    intro h
    have hp : r₂ ∈ stairPartners m k := by
      rw [mem_stairPartners]
      exact ⟨r₁, by
        rw [mem_stairBases]; exact ⟨hr₁1, hr₁m, hr₁p⟩, h.symm⟩
    exact Finset.disjoint_left.mp hd
      (mem_stairBases.mpr ⟨hr₂1, hr₂m, hr₂p⟩) hp
  have hkk : r₁ + k ≠ r₂ + k := by omega
  have d11 := cls_pairwise (n := n) (m := m) hm
    (Finset.mem_coe.mpr (Finset.mem_Icc.mpr ⟨hr₁1, by omega⟩))
    (Finset.mem_coe.mpr (Finset.mem_Icc.mpr ⟨hr₂1, by omega⟩)) hne
  have d12 := cls_pairwise (n := n) (m := m) hm
    (Finset.mem_coe.mpr (Finset.mem_Icc.mpr ⟨hr₁1, by omega⟩))
    (Finset.mem_coe.mpr (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)) h12
  have d21 := cls_pairwise (n := n) (m := m) hm
    (Finset.mem_coe.mpr (Finset.mem_Icc.mpr ⟨by omega, by omega⟩))
    (Finset.mem_coe.mpr (Finset.mem_Icc.mpr ⟨hr₂1, by omega⟩))
    h21.symm
  have d22 := cls_pairwise (n := n) (m := m) hm
    (Finset.mem_coe.mpr (Finset.mem_Icc.mpr ⟨by omega, by omega⟩))
    (Finset.mem_coe.mpr (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)) hkk
  rw [Finset.disjoint_union_left, Finset.disjoint_union_right,
    Finset.disjoint_union_right]
  exact ⟨⟨d11, d12⟩, ⟨d21, d22⟩⟩

/-- **The staircase matching cover.**  Every `x ∈ Icc (m+1) n` lies in a
residue class `cls n m ρ` with `ρ ∈ Icc 1 m`; writing `q = (ρ-1)/k` for
the block index: if `q` is even then `ρ` is a base (`ρ ≤ m-k`) or a
leftover (`ρ > m-k`), and if `q` is odd then `q ≥ 1` so `ρ - k` is a
base of even block index `q - 1` and `ρ = (ρ - k) + k` is its partner. -/
theorem Icc_subset_biUnion_stairMatchCls {n : ℕ} {m k : ℤ} (hm : 1 ≤ m)
    (hk : 1 ≤ k) :
    Finset.Icc (m + 1) (n : ℤ) ⊆
      (stairBases m k).biUnion
          (fun r => cls n m r ∪ cls n m (r + k)) ∪
        (stairLeftover m k).biUnion (cls n m) := by
  intro x hx
  obtain ⟨ρ, hρ, hxρ⟩ :=
    Finset.mem_biUnion.mp (Icc_subset_biUnion_cls (n := n) (m := m) hm hx)
  rw [Finset.mem_Icc] at hρ
  obtain ⟨hρ1, hρm⟩ := hρ
  rw [Finset.mem_union, Finset.mem_biUnion, Finset.mem_biUnion]
  rcases Int.even_or_odd ((ρ - 1) / k) with hpar | hpar
  · -- even block: base if `ρ ≤ m - k`, leftover otherwise
    have hpar0 : ((ρ - 1) / k) % 2 = 0 := Int.even_iff.mp hpar
    rcases lt_or_ge (m - k) ρ with hgt | hle
    · exact Or.inr ⟨ρ, mem_stairLeftover.mpr ⟨by omega, hρm, hpar0⟩,
        hxρ⟩
    · exact Or.inl ⟨ρ, mem_stairBases.mpr ⟨hρ1, hle, hpar0⟩,
        Finset.mem_union.mpr (Or.inl hxρ)⟩
  · -- odd block: `ρ - k` is a base and `ρ` its partner
    have hpar1 : ((ρ - 1) / k) % 2 = 1 := Int.odd_iff.mp hpar
    have hq1 : 1 ≤ (ρ - 1) / k := by
      have h0 : 0 ≤ (ρ - 1) / k := Int.ediv_nonneg (by omega) (by omega)
      rcases lt_or_eq_of_le h0 with h | h
      · exact h
      · rw [← h] at hpar1
        exact absurd hpar1 (by norm_num)
    have hrk : k ≤ ρ - 1 := by
      have h := (Int.le_ediv_iff_mul_le (by omega : 0 < k)).mp hq1
      omega
    have hbmem : ρ - k ∈ stairBases m k := by
      rw [mem_stairBases]
      refine ⟨by omega, by omega, ?_⟩
      rw [stair_block_sub hk]
      have hqodd : Odd ((ρ - 1) / k) := hpar
      have hqev : Even ((ρ - 1) / k - 1) := hqodd.sub_odd odd_one
      exact Int.even_iff.mp hqev
    refine Or.inl ⟨ρ - k, hbmem, ?_⟩
    rw [Finset.mem_union]
    refine Or.inr ?_
    have e2 : ρ - k + k = ρ := by ring
    rwa [e2]

/-- **The staircase matching product bound.**  For `s = m + k`,
`1 ≤ k`, the double-shift-free subsets of `Icc (m+1) n` are bounded by
the product of the staircase counts over the base pairs times the
Fibonacci counts of the leftover rails (which retain only the `m`-shift
constraint `shiftFree2.1`). -/
theorem card_powerset_filter_shiftFree2_Icc_le_stairMatchProd {n : ℕ}
    {m k : ℤ} (hm : 1 ≤ m) (hk : 1 ≤ k) (_hkm : k < m) :
    ((Finset.Icc (m + 1) (n : ℤ)).powerset.filter
        (shiftFree2 m (m + k))).card ≤
      (∏ r ∈ stairBases m k,
          (stairSets (((n : ℤ) - r) / m).toNat).card) *
        ∏ ρ ∈ stairLeftover m k,
          Nat.fib ((((n : ℤ) - ρ) / m).toNat + 2) := by
  have hms : m < m + k := by omega
  have hT := Icc_subset_biUnion_stairMatchCls (n := n) hm hk
  have hA := card_powerset_filter_shiftFree2_le_prod (m := m)
    (s := m + k) (stairBases m k)
    (fun r => cls n m r ∪ cls n m (r + k)) _ Finset.Subset.rfl
  have hB := card_powerset_filter_shiftFree2_le_prod (m := m)
    (s := m + k) (stairLeftover m k) (cls n m) _ Finset.Subset.rfl
  have hpair : ∀ r ∈ stairBases m k,
      ((cls n m r ∪ cls n m (r + k)).powerset.filter
          (shiftFree2 m (m + k))).card ≤
        (stairSets (((n : ℤ) - r) / m).toNat).card := by
    intro r hr
    rw [mem_stairBases] at hr
    obtain ⟨hr1, hrm, -⟩ := hr
    have hb := card_powerset_filter_shiftFree2_modm_pair_le' (n := n)
      (m := m) (s := m + k) (r := r) hm hms (by omega) hr1
    have e : r + (m + k) - m = r + k := by ring
    rwa [e] at hb
  have hA' : (((stairBases m k).biUnion
        (fun r => cls n m r ∪ cls n m (r + k))).powerset.filter
        (shiftFree2 m (m + k))).card ≤
      ∏ r ∈ stairBases m k,
        (stairSets (((n : ℤ) - r) / m).toNat).card :=
    hA.trans (Finset.prod_le_prod fun r hr => hpair r hr)
  have hB' : (((stairLeftover m k).biUnion (cls n m)).powerset.filter
        (shiftFree2 m (m + k))).card ≤
      ∏ ρ ∈ stairLeftover m k,
        Nat.fib ((((n : ℤ) - ρ) / m).toNat + 2) := by
    refine hB.trans (Finset.prod_le_prod fun ρ hρ => ?_)
    have hmono : (cls n m ρ).powerset.filter (shiftFree2 m (m + k)) ⊆
        (cls n m ρ).powerset.filter (shiftFree m) := by
      intro t ht
      rw [Finset.mem_filter] at ht ⊢
      exact ⟨ht.1, ht.2.1⟩
    exact (Finset.card_le_card hmono).trans
      (le_of_eq (card_powerset_filter_shiftFree_cls (n := n) (m := m)
        (r := ρ) hm))
  exact (card_powerset_filter_shiftFree2_le_mul hT).trans
    (Nat.mul_le_mul hA' hB')

/-- `F_{L+2} ≤ 2^{L+1}` (a local copy of the `RailPairing` lemma, kept
to minimise the import list). -/
theorem fib_add_two_le_two_pow' (L : ℕ) : Nat.fib (L + 2) ≤ 2 ^ (L + 1) := by
  induction L using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more k ih ih1 =>
      show Nat.fib (k + 2 + 2) ≤ 2 ^ (k + 2 + 1)
      rw [Nat.fib_add_two]
      calc Nat.fib (k + 2) + Nat.fib (k + 2 + 1)
          ≤ 2 ^ (k + 1) + 2 ^ (k + 1 + 1) := add_le_add ih ih1
        _ = 3 * 2 ^ (k + 1) := by rw [pow_succ']; ring
        _ ≤ 4 * 2 ^ (k + 1) := by omega
        _ = 2 ^ (k + 2 + 1) := by
            rw [show k + 2 + 1 = k + 1 + 2 from rfl, pow_add]
            ring

/-- **Closed form of the staircase matching bound.**  Each pair factor
contributes `4·5^{L_r}` and each leftover rail `2^{L_ρ + 1}`; since the
bases number at most `m - k`, the leftovers at most `k`, and the rail
lengths `Σ L` over `bases ∪ leftover ⊆ Icc 1 m` sum to at most
`(n - m)₊`, the count is at most
`4^{(m-k)₊} · (5^{(n-m)₊} · 2^{k₊})`. -/
theorem card_powerset_filter_shiftFree2_Icc_le_stairMatchClosed {n : ℕ}
    {m k : ℤ} (hm : 1 ≤ m) (hk : 1 ≤ k) (hkm : k < m) :
    ((Finset.Icc (m + 1) (n : ℤ)).powerset.filter
        (shiftFree2 m (m + k))).card ≤
      4 ^ (m - k).toNat *
        (5 ^ ((n : ℤ) - m).toNat * 2 ^ k.toNat) := by
  have hprod := card_powerset_filter_shiftFree2_Icc_le_stairMatchProd
    (n := n) hm hk hkm
  have hcardB : (stairBases m k).card ≤ (m - k).toNat := by
    calc (stairBases m k).card
        ≤ (Finset.Icc 1 (m - k)).card :=
          Finset.card_le_card (Finset.filter_subset _ _)
      _ = (m - k).toNat := by rw [Int.card_Icc]; congr 1; omega
  have hcardL : (stairLeftover m k).card ≤ k.toNat := by
    calc (stairLeftover m k).card
        ≤ (Finset.Icc (m - k + 1) m).card :=
          Finset.card_le_card (Finset.filter_subset _ _)
      _ = k.toNat := by rw [Int.card_Icc]; congr 1; omega
  have hdisj : Disjoint (stairBases m k) (stairLeftover m k) := by
    rw [Finset.disjoint_left]
    intro x hxb hxl
    rw [mem_stairBases] at hxb
    rw [mem_stairLeftover] at hxl
    omega
  have hsub : stairBases m k ∪ stairLeftover m k ⊆ Finset.Icc 1 m := by
    intro x hx
    rw [Finset.mem_union] at hx
    rcases hx with hx | hx
    · rw [mem_stairBases] at hx
      rw [Finset.mem_Icc]
      omega
    · rw [mem_stairLeftover] at hx
      rw [Finset.mem_Icc]
      omega
  have hsum : (∑ r ∈ stairBases m k, (((n : ℤ) - r) / m).toNat) +
        (∑ ρ ∈ stairLeftover m k, (((n : ℤ) - ρ) / m).toNat) ≤
        ((n : ℤ) - m).toNat := by
    rw [← Finset.sum_union hdisj]
    calc ∑ x ∈ stairBases m k ∪ stairLeftover m k,
            (((n : ℤ) - x) / m).toNat
        ≤ ∑ x ∈ Finset.Icc 1 m, (((n : ℤ) - x) / m).toNat :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun x _ _ => Nat.zero_le _)
      _ = ((n : ℤ) - m).toNat := sum_cls_card hm
  have hA2 : ∏ r ∈ stairBases m k,
          (stairSets (((n : ℤ) - r) / m).toNat).card ≤
        4 ^ (stairBases m k).card *
          5 ^ (∑ r ∈ stairBases m k, (((n : ℤ) - r) / m).toNat) := by
    calc ∏ r ∈ stairBases m k,
            (stairSets (((n : ℤ) - r) / m).toNat).card
        ≤ ∏ r ∈ stairBases m k,
            4 * 5 ^ (((n : ℤ) - r) / m).toNat :=
          Finset.prod_le_prod fun r _ =>
            stairSets_card_le_four_mul_five_pow _
      _ = 4 ^ (stairBases m k).card *
            5 ^ (∑ r ∈ stairBases m k, (((n : ℤ) - r) / m).toNat) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const,
            Finset.prod_pow_eq_pow_sum]
  have hB2 : ∏ ρ ∈ stairLeftover m k,
          Nat.fib ((((n : ℤ) - ρ) / m).toNat + 2) ≤
        2 ^ ((∑ ρ ∈ stairLeftover m k, (((n : ℤ) - ρ) / m).toNat) +
          (stairLeftover m k).card) := by
    calc ∏ ρ ∈ stairLeftover m k,
            Nat.fib ((((n : ℤ) - ρ) / m).toNat + 2)
        ≤ ∏ ρ ∈ stairLeftover m k,
            2 ^ ((((n : ℤ) - ρ) / m).toNat + 1) :=
          Finset.prod_le_prod fun ρ _ => fib_add_two_le_two_pow' _
      _ = 2 ^ ((∑ ρ ∈ stairLeftover m k, (((n : ℤ) - ρ) / m).toNat) +
            (stairLeftover m k).card) := by
          rw [Finset.prod_pow_eq_pow_sum, Finset.sum_add_distrib,
            Finset.sum_const]
          simp only [smul_eq_mul, mul_one]
  have h4B : 4 ^ (stairBases m k).card ≤ 4 ^ (m - k).toNat :=
    Nat.pow_le_pow_right (show 0 < 4 by norm_num) hcardB
  have h2L : 2 ^ ((∑ ρ ∈ stairLeftover m k,
            (((n : ℤ) - ρ) / m).toNat) + (stairLeftover m k).card) ≤
        2 ^ ((∑ ρ ∈ stairLeftover m k, (((n : ℤ) - ρ) / m).toNat) +
          k.toNat) :=
    Nat.pow_le_pow_right (show 0 < 2 by norm_num)
      (add_le_add (le_refl _) hcardL)
  have h25 : 2 ^ (∑ ρ ∈ stairLeftover m k, (((n : ℤ) - ρ) / m).toNat) ≤
        5 ^ (∑ ρ ∈ stairLeftover m k, (((n : ℤ) - ρ) / m).toNat) :=
    Nat.pow_le_pow_left (show (2 : ℕ) ≤ 5 by norm_num) _
  have h5nm : 5 ^ ((∑ r ∈ stairBases m k, (((n : ℤ) - r) / m).toNat) +
          (∑ ρ ∈ stairLeftover m k, (((n : ℤ) - ρ) / m).toNat)) ≤
        5 ^ ((n : ℤ) - m).toNat :=
    Nat.pow_le_pow_right (show 0 < 5 by norm_num) hsum
  calc ((Finset.Icc (m + 1) (n : ℤ)).powerset.filter
        (shiftFree2 m (m + k))).card
      ≤ (∏ r ∈ stairBases m k,
            (stairSets (((n : ℤ) - r) / m).toNat).card) *
          ∏ ρ ∈ stairLeftover m k,
            Nat.fib ((((n : ℤ) - ρ) / m).toNat + 2) := hprod
    _ ≤ (4 ^ (stairBases m k).card *
            5 ^ (∑ r ∈ stairBases m k, (((n : ℤ) - r) / m).toNat)) *
          2 ^ ((∑ ρ ∈ stairLeftover m k, (((n : ℤ) - ρ) / m).toNat) +
            (stairLeftover m k).card) :=
        Nat.mul_le_mul hA2 hB2
    _ ≤ (4 ^ (m - k).toNat *
            5 ^ (∑ r ∈ stairBases m k, (((n : ℤ) - r) / m).toNat)) *
          2 ^ ((∑ ρ ∈ stairLeftover m k, (((n : ℤ) - ρ) / m).toNat) +
            k.toNat) :=
        Nat.mul_le_mul
          (Nat.mul_le_mul h4B (le_refl _)) h2L
    _ = 4 ^ (m - k).toNat *
          (5 ^ (∑ r ∈ stairBases m k, (((n : ℤ) - r) / m).toNat) *
            2 ^ (∑ ρ ∈ stairLeftover m k, (((n : ℤ) - ρ) / m).toNat)) *
          2 ^ k.toNat := by
        rw [pow_add]
        ring
    _ ≤ 4 ^ (m - k).toNat *
          (5 ^ (∑ r ∈ stairBases m k, (((n : ℤ) - r) / m).toNat) *
            5 ^ (∑ ρ ∈ stairLeftover m k, (((n : ℤ) - ρ) / m).toNat)) *
          2 ^ k.toNat :=
        Nat.mul_le_mul
          (Nat.mul_le_mul (le_refl _)
            (Nat.mul_le_mul (le_refl _) h25))
          (le_refl _)
    _ = 4 ^ (m - k).toNat *
          5 ^ ((∑ r ∈ stairBases m k, (((n : ℤ) - r) / m).toNat) +
            (∑ ρ ∈ stairLeftover m k, (((n : ℤ) - ρ) / m).toNat)) *
          2 ^ k.toNat := by
        rw [← pow_add]
    _ ≤ 4 ^ (m - k).toNat * 5 ^ ((n : ℤ) - m).toNat * 2 ^ k.toNat :=
        Nat.mul_le_mul
          (Nat.mul_le_mul (le_refl _) h5nm) (le_refl _)
    _ = 4 ^ (m - k).toNat *
          (5 ^ ((n : ℤ) - m).toNat * 2 ^ k.toNat) := by ring

end JSP000728
