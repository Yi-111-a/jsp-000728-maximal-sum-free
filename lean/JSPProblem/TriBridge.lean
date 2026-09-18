import JSPProblem.TriCyl
import JSPProblem.TwoMin
import JSPProblem.NoConsec
import JSPProblem.PairRails
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# JSP-000728 — the `s = 3m` cell: triple-rail wrap strip

For `1 ≤ m` and `s = 3m`, the orbits of the `+m` shift on the mod-`3m`
residues are exactly the `m` triples `{r, r+m, r+2m}` for `r ∈ Icc 1 m`.
The union

  `U_r = cls n (3m) r ∪ cls n (3m) (r+m) ∪ cls n (3m) (r+2m)`

carries a *wrap strip* constraint graph for `shiftFree2 m (3m)`:

* the `3m`-shift links `(a, j)` to `(a, j+1)` on the same rail;
* the `m`-shift links `(0, j) → (1, j)`, `(1, j) → (2, j)` and wraps
  `(2, j) → (0, j+1)`.

**Important honest note.**  The image is *not* `triFree` in general:
`x` on rail `0` and `x + 2m` on rail `2` occupy the same column `j` and
are *not* forbidden by `shiftFree2 m (3m)` (only `x + m` and `x + 3m`
are).  The honest column states are therefore the five sets
`∅, {0}, {1}, {2}, {0,2}` rather than the four of the triangle strip —
the wrap edge `(2, j) → (0, j+1)` replaces the missing triangle edge
`{0,2}` inside a column.  We formalise this family as `wSets L`
(independent sets of the wrap strip) and prove the closed bound

  `W(L) · 2^L ≤ 27 · 7^L`

via the simultaneous induction on the four avoiding families
`W, A₁, A₂, A₀₂` with weights `(27, 21, 18, 14)` (all four inequalities
are strict, e.g. `2·(27+21+18+2·14) = 188 ≤ 189`).  Since the wrap
strip's column growth `λ ≈ 3.463 < 7/2`, this gives the per-vertex rate
`(7/2)^{1/3} ≈ 1.518` on the `≈ 3L` elements of the orbit, matching the
`triSets` rate `T(L)·2^L ≤ 4·7^L` up to the worse constant.

* `triIdx n m r x` : index map `x ↦ (rail, level)` on `U_r`;
  `triIdx_injOn` injects the union into `Fin 3 × ℕ`.
* `triMSucc` : the `+m` neighbour `(a, j) ↦ (a+1, j + (a = 2))`.
* `wFree`, `wSets L`, `wAvoid S L` : the wrap-strip independent sets
  and avoiding families; `wSets_succ` decomposes `wSets (L+1)` by the
  last column over `allowedCols`.
* `card_powerset_filter_shiftFree2_tri_cls_le` : the double-shift-free
  subsets of `U_r` inject into `wSets (((n - r)/(3m)).toNat)`.
* `Icc_subset_biUnion_triCls` : `Icc (3m+1) n` is covered by the `m`
  triple unions.
* `card_powerset_filter_shiftFree2_triIcc_le` : conditional product
  bound `∏_{r ∈ Icc 1 m} (wSets L_r).card`.
* `card_powerset_filter_shiftFree2_triIcc_mul_le` : closed bound
  `card · 2^S ≤ 27^{m₊} · 7^{(n-3m)₊}` with `S = Σ_r L_r ≤ (n-3m)₊`.
-/

namespace JSP000728

/-- The rail/level coordinates of an element of
`cls n (3m) r ∪ cls n (3m) (r+m) ∪ cls n (3m) (r+2m)`: rail `k ∈ Fin 3`
and position `j` along the progression. -/
def triIdx (n : ℕ) (m r : ℤ) (x : ℤ) : Fin 3 × ℕ :=
  if x ∈ cls n (3 * m) r then (0, ((x - r - 3 * m) / (3 * m)).toNat)
    else if x ∈ cls n (3 * m) (r + m) then
      (1, ((x - r - m - 3 * m) / (3 * m)).toNat)
    else (2, ((x - r - 2 * m - 3 * m) / (3 * m)).toNat)

theorem triIdx_of_mem0 {n : ℕ} {m r : ℤ} {x : ℤ} (hx : x ∈ cls n (3 * m) r) :
    triIdx n m r x = (0, ((x - r - 3 * m) / (3 * m)).toNat) :=
  ite_eq_left hx

theorem triIdx_of_mem1 {n : ℕ} {m r : ℤ} {x : ℤ} (hx0 : x ∉ cls n (3 * m) r)
    (hx1 : x ∈ cls n (3 * m) (r + m)) :
    triIdx n m r x = (1, ((x - r - m - 3 * m) / (3 * m)).toNat) :=
  (ite_eq_right hx0).trans (ite_eq_left hx1)

theorem triIdx_of_mem2 {n : ℕ} {m r : ℤ} {x : ℤ} (hx0 : x ∉ cls n (3 * m) r)
    (hx1 : x ∉ cls n (3 * m) (r + m)) :
    triIdx n m r x = (2, ((x - r - 2 * m - 3 * m) / (3 * m)).toNat) :=
  (ite_eq_right hx0).trans (ite_eq_right hx1)

/-- The `3m`-residue classes are pairwise disjoint on `Icc 1 (3m)`. -/
theorem cls_tri_pairwise {n : ℕ} {m : ℤ} (hm : 1 ≤ m) :
    (↑(Finset.Icc 1 (3 * m)) : Set ℤ).PairwiseDisjoint (cls n (3 * m)) :=
  cls_pairwise (n := n) (m := 3 * m) (by omega)

/-- Distinct residues in `Icc 1 (3m)` have disjoint classes. -/
theorem cls_tri_nmem {n : ℕ} {m ρ σ : ℤ} (hm : 1 ≤ m)
    (hρ : ρ ∈ Finset.Icc 1 (3 * m)) (hσ : σ ∈ Finset.Icc 1 (3 * m))
    (hne : ρ ≠ σ) {x : ℤ} (hx : x ∈ cls n (3 * m) ρ) :
    x ∉ cls n (3 * m) σ :=
  Finset.disjoint_left.mp
    (cls_tri_pairwise (n := n) hm (Finset.mem_coe.mpr hρ)
      (Finset.mem_coe.mpr hσ) hne) hx

/-- The index map on rail `0`: `r + 3m + 3m·k ↦ (0, k)`. -/
theorem triIdx_cls0 {n : ℕ} {m r : ℤ} (hs : 3 * m ≠ 0) {k : ℕ}
    (hk : r + 3 * m + 3 * m * (k : ℤ) ∈ cls n (3 * m) r) :
    triIdx n m r (r + 3 * m + 3 * m * (k : ℤ)) = (0, k) := by
  rw [triIdx_of_mem0 hk]
  have e : (r + 3 * m + 3 * m * (k : ℤ) - r - 3 * m) / (3 * m) = (k : ℤ) := by
    rw [show r + 3 * m + 3 * m * (k : ℤ) - r - 3 * m = 3 * m * (k : ℤ) from by ring,
      mul_comm (3 * m) (k : ℤ)]
    exact Int.mul_ediv_cancel _ hs
  rw [e, Int.toNat_natCast]

/-- The index map on rail `1`: `r + m + 3m + 3m·k ↦ (1, k)`. -/
theorem triIdx_cls1 {n : ℕ} {m r : ℤ} (hs : 3 * m ≠ 0) {k : ℕ}
    (hk0 : r + m + 3 * m + 3 * m * (k : ℤ) ∉ cls n (3 * m) r)
    (hk1 : r + m + 3 * m + 3 * m * (k : ℤ) ∈ cls n (3 * m) (r + m)) :
    triIdx n m r (r + m + 3 * m + 3 * m * (k : ℤ)) = (1, k) := by
  rw [triIdx_of_mem1 hk0 hk1]
  have e : (r + m + 3 * m + 3 * m * (k : ℤ) - r - m - 3 * m) / (3 * m)
      = (k : ℤ) := by
    rw [show r + m + 3 * m + 3 * m * (k : ℤ) - r - m - 3 * m
        = 3 * m * (k : ℤ) from by ring,
      mul_comm (3 * m) (k : ℤ)]
    exact Int.mul_ediv_cancel _ hs
  rw [e, Int.toNat_natCast]

/-- The index map on rail `2`: `r + 2m + 3m + 3m·k ↦ (2, k)`. -/
theorem triIdx_cls2 {n : ℕ} {m r : ℤ} (hs : 3 * m ≠ 0) {k : ℕ}
    (hk0 : r + 2 * m + 3 * m + 3 * m * (k : ℤ) ∉ cls n (3 * m) r)
    (hk1 : r + 2 * m + 3 * m + 3 * m * (k : ℤ) ∉ cls n (3 * m) (r + m)) :
    triIdx n m r (r + 2 * m + 3 * m + 3 * m * (k : ℤ)) = (2, k) := by
  rw [triIdx_of_mem2 hk0 hk1]
  have e : (r + 2 * m + 3 * m + 3 * m * (k : ℤ) - r - 2 * m - 3 * m) / (3 * m)
      = (k : ℤ) := by
    rw [show r + 2 * m + 3 * m + 3 * m * (k : ℤ) - r - 2 * m - 3 * m
        = 3 * m * (k : ℤ) from by ring,
      mul_comm (3 * m) (k : ℤ)]
    exact Int.mul_ediv_cancel _ hs
  rw [e, Int.toNat_natCast]

/-- The index map is injective on the union of the three rails. -/
theorem triIdx_injOn {n : ℕ} {m r : ℤ} (hm : 1 ≤ m) (hr : 1 ≤ r) (hrm : r ≤ m) :
    Set.InjOn (triIdx n m r)
      (↑(cls n (3 * m) r ∪ cls n (3 * m) (r + m) ∪ cls n (3 * m) (r + 2 * m)) :
        Set ℤ) := by
  have h3m : 0 < 3 * m := by omega
  have hsn : 3 * m ≠ 0 := ne_of_gt h3m
  have hr0 : r ∈ Finset.Icc 1 (3 * m) := by
    rw [Finset.mem_Icc]; omega
  have hr1 : r + m ∈ Finset.Icc 1 (3 * m) := by
    rw [Finset.mem_Icc]; omega
  have hr2 : r + 2 * m ∈ Finset.Icc 1 (3 * m) := by
    rw [Finset.mem_Icc]; omega
  intro x hx y hy hxy
  rw [Finset.mem_coe, Finset.mem_union, Finset.mem_union] at hx hy
  rcases hx with (hx | hx) | hx <;> rcases hy with (hy | hy) | hy
  · obtain ⟨kx, -, rfl⟩ := mem_cls_iff.mp hx
    obtain ⟨ky, -, rfl⟩ := mem_cls_iff.mp hy
    rw [triIdx_cls0 hsn hx, triIdx_cls0 hsn hy] at hxy
    have h2 : kx = ky := (Prod.ext_iff.mp hxy).2
    rw [h2]
  · obtain ⟨kx, -, rfl⟩ := mem_cls_iff.mp hx
    obtain ⟨ky, -, rfl⟩ := mem_cls_iff.mp hy
    have hyr := cls_tri_nmem hm hr1 hr0 (by omega) hy
    rw [triIdx_cls0 hsn hx, triIdx_cls1 hsn hyr hy] at hxy
    simp only [Prod.mk.injEq] at hxy
    exact absurd hxy.1 (by decide)
  · obtain ⟨kx, -, rfl⟩ := mem_cls_iff.mp hx
    obtain ⟨ky, -, rfl⟩ := mem_cls_iff.mp hy
    have hyr := cls_tri_nmem hm hr2 hr0 (by omega) hy
    have hyr1 := cls_tri_nmem hm hr2 hr1 (by omega) hy
    rw [triIdx_cls0 hsn hx, triIdx_cls2 hsn hyr hyr1] at hxy
    simp only [Prod.mk.injEq] at hxy
    exact absurd hxy.1 (by decide)
  · obtain ⟨kx, -, rfl⟩ := mem_cls_iff.mp hx
    obtain ⟨ky, -, rfl⟩ := mem_cls_iff.mp hy
    have hxr := cls_tri_nmem hm hr1 hr0 (by omega) hx
    rw [triIdx_cls1 hsn hxr hx, triIdx_cls0 hsn hy] at hxy
    simp only [Prod.mk.injEq] at hxy
    exact absurd hxy.1 (by decide)
  · obtain ⟨kx, -, rfl⟩ := mem_cls_iff.mp hx
    obtain ⟨ky, -, rfl⟩ := mem_cls_iff.mp hy
    have hxr := cls_tri_nmem hm hr1 hr0 (by omega) hx
    have hyr := cls_tri_nmem hm hr1 hr0 (by omega) hy
    rw [triIdx_cls1 hsn hxr hx, triIdx_cls1 hsn hyr hy] at hxy
    have h2 : kx = ky := (Prod.ext_iff.mp hxy).2
    rw [h2]
  · obtain ⟨kx, -, rfl⟩ := mem_cls_iff.mp hx
    obtain ⟨ky, -, rfl⟩ := mem_cls_iff.mp hy
    have hxr := cls_tri_nmem hm hr1 hr0 (by omega) hx
    have hyr := cls_tri_nmem hm hr2 hr0 (by omega) hy
    have hyr1 := cls_tri_nmem hm hr2 hr1 (by omega) hy
    rw [triIdx_cls1 hsn hxr hx, triIdx_cls2 hsn hyr hyr1] at hxy
    simp only [Prod.mk.injEq] at hxy
    exact absurd hxy.1 (by decide)
  · obtain ⟨kx, -, rfl⟩ := mem_cls_iff.mp hx
    obtain ⟨ky, -, rfl⟩ := mem_cls_iff.mp hy
    have hxr := cls_tri_nmem hm hr2 hr0 (by omega) hx
    have hxr1 := cls_tri_nmem hm hr2 hr1 (by omega) hx
    rw [triIdx_cls2 hsn hxr hxr1, triIdx_cls0 hsn hy] at hxy
    simp only [Prod.mk.injEq] at hxy
    exact absurd hxy.1 (by decide)
  · obtain ⟨kx, -, rfl⟩ := mem_cls_iff.mp hx
    obtain ⟨ky, -, rfl⟩ := mem_cls_iff.mp hy
    have hxr := cls_tri_nmem hm hr2 hr0 (by omega) hx
    have hxr1 := cls_tri_nmem hm hr2 hr1 (by omega) hx
    have hyr := cls_tri_nmem hm hr1 hr0 (by omega) hy
    rw [triIdx_cls2 hsn hxr hxr1, triIdx_cls1 hsn hyr hy] at hxy
    simp only [Prod.mk.injEq] at hxy
    exact absurd hxy.1 (by decide)
  · obtain ⟨kx, -, rfl⟩ := mem_cls_iff.mp hx
    obtain ⟨ky, -, rfl⟩ := mem_cls_iff.mp hy
    have hxr := cls_tri_nmem hm hr2 hr0 (by omega) hx
    have hxr1 := cls_tri_nmem hm hr2 hr1 (by omega) hx
    have hyr := cls_tri_nmem hm hr2 hr0 (by omega) hy
    have hyr1 := cls_tri_nmem hm hr2 hr1 (by omega) hy
    rw [triIdx_cls2 hsn hxr hxr1, triIdx_cls2 hsn hyr hyr1] at hxy
    have h2 : kx = ky := (Prod.ext_iff.mp hxy).2
    rw [h2]

/-- The `+m` neighbour of a strip vertex: the next rail cyclically,
wrapping to level `j+1` on the last rail. -/
def triMSucc (p : Fin 3 × ℕ) : Fin 3 × ℕ :=
  (p.1 + 1, p.2 + if p.1 = 2 then 1 else 0)

theorem triMSucc_zero (j : ℕ) : triMSucc (0, j) = (1, j) := by
  refine Prod.ext_iff.mpr ⟨?_, ?_⟩
  · show (0 : Fin 3) + 1 = 1
    decide
  · show j + (if (0 : Fin 3) = 2 then 1 else 0) = j
    rw [ite_eq_right (by decide), add_zero]

theorem triMSucc_one (j : ℕ) : triMSucc (1, j) = (2, j) := by
  refine Prod.ext_iff.mpr ⟨?_, ?_⟩
  · show (1 : Fin 3) + 1 = 2
    decide
  · show j + (if (1 : Fin 3) = 2 then 1 else 0) = j
    rw [ite_eq_right (by decide), add_zero]

theorem triMSucc_two (j : ℕ) : triMSucc (2, j) = (0, j + 1) := by
  refine Prod.ext_iff.mpr ⟨?_, ?_⟩
  · show (2 : Fin 3) + 1 = 0
    decide
  · show j + (if (2 : Fin 3) = 2 then 1 else 0) = j + 1
    rw [ite_eq_left (by decide)]

/-- `t` is an *independent set* of the wrap strip: no cell carries its
rail-successor `(a, j+1)` (the `3m`-shift) and no cell carries its
`+m`-neighbour `triMSucc p` (`(0,j)→(1,j)`, `(1,j)→(2,j)`,
`(2,j)→(0,j+1)`). -/
def wFree (t : Finset (Fin 3 × ℕ)) : Prop :=
  (∀ p ∈ t, (p.1, p.2 + 1) ∉ t) ∧ ∀ p ∈ t, triMSucc p ∉ t

instance decidableWFree (t : Finset (Fin 3 × ℕ)) : Decidable (wFree t) := by
  unfold wFree; infer_instance

theorem wFree.mono {t u : Finset (Fin 3 × ℕ)} (ht : wFree t) (hu : u ⊆ t) :
    wFree u :=
  ⟨fun p hp hC => ht.1 p (hu hp) (hu hC),
   fun p hp hC => ht.2 p (hu hp) (hu hC)⟩

/-- The family of independent sets of the wrap strip of length `L`. -/
def wSets (L : ℕ) : Finset (Finset (Fin 3 × ℕ)) :=
  (triVert L).powerset.filter wFree

theorem mem_wSets {L : ℕ} {t : Finset (Fin 3 × ℕ)} :
    t ∈ wSets L ↔ t ⊆ triVert L ∧ wFree t := by
  simp [wSets]

/-- The independent sets whose last column avoids the rails of `S`. -/
def wAvoid (S : Finset (Fin 3)) (L : ℕ) : Finset (Finset (Fin 3 × ℕ)) :=
  (wSets L).filter fun t => ∀ a ∈ S, (a, L - 1) ∉ t

theorem mem_wAvoid {S : Finset (Fin 3)} {L : ℕ} {t : Finset (Fin 3 × ℕ)} :
    t ∈ wAvoid S L ↔ t ∈ wSets L ∧ ∀ a ∈ S, (a, L - 1) ∉ t :=
  Finset.mem_filter

/-- The rails a column-`L` occupant set `u` forbids at level `L - 1`:
itself (same-rail successors) together with rail `2` when `0 ∈ u`
(the wrap edge `(2, L-1) → (0, L)`). -/
def wForbid (u : Finset (Fin 3)) : Finset (Fin 3) :=
  u ∪ if (0 : Fin 3) ∈ u then {(2 : Fin 3)} else ∅

/-- The vertices of column `L` occupied by the rail set `u`. -/
def wColAt (u : Finset (Fin 3)) (L : ℕ) : Finset (Fin 3 × ℕ) :=
  u.image fun a => (a, L)

/-- The allowed column states: `∅`, the three singletons and `{0, 2}`
(the pairs `{0,1}` and `{1,2}` are `+m`-edges, hence forbidden). -/
def allowedCols : Finset (Finset (Fin 3)) := {∅, {0}, {1}, {2}, {0, 2}}

/-- Any member of `allowedCols` is free of the two forbidden pairs. -/
theorem allowedCols_spec {u : Finset (Fin 3)} (hu : u ∈ allowedCols) :
    ¬((0 : Fin 3) ∈ u ∧ (1 : Fin 3) ∈ u) ∧
      ¬((1 : Fin 3) ∈ u ∧ (2 : Fin 3) ∈ u) := by
  simp only [allowedCols, Finset.mem_insert, Finset.mem_singleton] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl <;> decide

/-- A rail set outside `allowedCols` contains a forbidden pair. -/
theorem not_mem_allowedCols {u : Finset (Fin 3)} (hu : u ∉ allowedCols) :
    ((0 : Fin 3) ∈ u ∧ (1 : Fin 3) ∈ u) ∨
      ((1 : Fin 3) ∈ u ∧ (2 : Fin 3) ∈ u) := by
  have hmem : u ∈ (Finset.univ : Finset (Fin 3)).powerset.filter
      (fun v => v ∉ allowedCols) :=
    Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr (Finset.subset_univ u), hu⟩
  have hf : (Finset.univ : Finset (Fin 3)).powerset.filter
      (fun v => v ∉ allowedCols) =
      ({{(0 : Fin 3), (1 : Fin 3)}, {(1 : Fin 3), (2 : Fin 3)},
        {(0 : Fin 3), (1 : Fin 3), (2 : Fin 3)}} :
        Finset (Finset (Fin 3))) := by
    decide
  rw [hf] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl <;> decide

/-- Filtering the union `t ∪ wColAt u L` (with `t ⊆ triVert L`) at level
`L` recovers the column. -/
theorem filter_union_wColAt_eq_self {t : Finset (Fin 3 × ℕ)}
    {u : Finset (Fin 3)} {L : ℕ} (ht : t ⊆ triVert L) :
    (t ∪ wColAt u L).filter (fun p => p.2 = L) = wColAt u L := by
  rw [Finset.filter_union]
  have h1 : t.filter (fun p => p.2 = L) = ∅ := by
    apply Finset.filter_false_of_mem
    rintro ⟨a, j⟩ hp
    have hv := ht hp
    rw [mem_triVert] at hv
    omega
  have h2 : (wColAt u L).filter (fun p => p.2 = L) = wColAt u L := by
    apply Finset.filter_eq_self.mpr
    rintro ⟨a, j⟩ hp
    rw [wColAt, Finset.mem_image] at hp
    obtain ⟨b, -, hb⟩ := hp
    exact (Prod.ext_iff.mp hb).2.symm
  rw [h1, h2, Finset.empty_union]

/-- Filtering the union `t ∪ wColAt u L` (with `t ⊆ triVert L`) below
level `L` recovers `t`. -/
theorem filter_union_wColAt_lt_self {t : Finset (Fin 3 × ℕ)}
    {u : Finset (Fin 3)} {L : ℕ} (ht : t ⊆ triVert L) :
    (t ∪ wColAt u L).filter (fun p => p.2 < L) = t := by
  rw [Finset.filter_union]
  have h1 : t.filter (fun p => p.2 < L) = t := by
    apply Finset.filter_eq_self.mpr
    rintro ⟨a, j⟩ hp
    have hv := ht hp
    rw [mem_triVert] at hv
    exact hv
  have h2 : (wColAt u L).filter (fun p => p.2 < L) = ∅ := by
    apply Finset.filter_false_of_mem
    rintro ⟨a, j⟩ hp
    rw [wColAt, Finset.mem_image] at hp
    obtain ⟨b, -, hb⟩ := hp
    have hjl : j = L := (Prod.ext_iff.mp hb).2.symm
    omega
  rw [h1, h2, Finset.union_empty]

/-- The column map `u ↦ wColAt u L` is injective. -/
theorem wColAt_inj {u u' : Finset (Fin 3)} {L : ℕ}
    (h : wColAt u L = wColAt u' L) : u = u' := by
  ext a
  constructor
  · intro ha
    have hmem : (a, L) ∈ wColAt u L := Finset.mem_image.mpr ⟨a, ha, rfl⟩
    rw [h] at hmem
    obtain ⟨b, hb, hbeq⟩ := Finset.mem_image.mp hmem
    have hab : a = b := (Prod.ext_iff.mp hbeq).1.symm
    rwa [hab]
  · intro ha
    have hmem : (a, L) ∈ wColAt u' L := Finset.mem_image.mpr ⟨a, ha, rfl⟩
    rw [← h] at hmem
    obtain ⟨b, hb, hbeq⟩ := Finset.mem_image.mp hmem
    have hab : a = b := (Prod.ext_iff.mp hbeq).1.symm
    rwa [hab]

/-- **Column decomposition.**  `wSets (L+1)` splits over the last
column's state `u ∈ allowedCols`; the remaining part is an independent
set of length `L` avoiding `wForbid u` at level `L-1`. -/
theorem wSets_succ (L : ℕ) :
    wSets (L + 1) = allowedCols.biUnion fun u =>
      (wAvoid (wForbid u) L).image fun t => t ∪ wColAt u L := by
  ext t
  rw [mem_wSets, Finset.mem_biUnion]
  constructor
  · rintro ⟨hsub, hfree⟩
    set u := (Finset.univ : Finset (Fin 3)).filter fun a => (a, L) ∈ t
      with hu_def
    have hu_mem : ∀ a : Fin 3, a ∈ u ↔ (a, L) ∈ t := fun a =>
      (Finset.mem_filter.trans (and_iff_right (Finset.mem_univ a)))
    have hu_allowed : u ∈ allowedCols := by
      by_contra hC
      obtain (⟨h0, h1⟩ | ⟨h1, h2⟩) := not_mem_allowedCols hC
      · have h0L : (0, L) ∈ t := (hu_mem 0).mp h0
        have h1L : (1, L) ∈ t := (hu_mem 1).mp h1
        have hs : triMSucc (0, L) ∉ t := hfree.2 (0, L) h0L
        rw [triMSucc_zero] at hs
        exact hs h1L
      · have h1L : (1, L) ∈ t := (hu_mem 1).mp h1
        have h2L : (2, L) ∈ t := (hu_mem 2).mp h2
        have hs : triMSucc (1, L) ∉ t := hfree.2 (1, L) h1L
        rw [triMSucc_one] at hs
        exact hs h2L
    refine ⟨u, hu_allowed, ?_⟩
    set rest := t.filter fun p => p.2 < L with hrest_def
    have hrest_t : rest ⊆ t := Finset.filter_subset _ _
    have hrest_wSets : rest ∈ wSets L := by
      rw [mem_wSets]
      refine ⟨?_, hfree.mono hrest_t⟩
      rintro ⟨a, j⟩ hp
      rw [mem_triVert]
      exact (Finset.mem_filter.mp hp).2
    have hrest_avoid : ∀ a ∈ wForbid u, (a, L - 1) ∉ rest := by
      intro a ha hcontra
      have hmem := (Finset.mem_filter.mp hcontra).1
      have hlt : L - 1 < L := by
        rw [mem_wSets] at hrest_wSets
        have hv := hrest_wSets.1 hcontra
        rw [mem_triVert] at hv
        exact hv
      have hL : 0 < L := by omega
      have hL1 : L - 1 + 1 = L := by omega
      rw [wForbid, Finset.mem_union] at ha
      rcases ha with ha | ha
      · have haL : (a, L) ∈ t := (hu_mem a).mp ha
        have hs : (a, L - 1 + 1) ∉ t := hfree.1 (a, L - 1) hmem
        rw [hL1] at hs
        exact hs haL
      · by_cases h0 : (0 : Fin 3) ∈ u
        · rw [ite_eq_left h0, Finset.mem_singleton] at ha
          subst ha
          have h0L : (0, L) ∈ t := (hu_mem 0).mp h0
          have hs : triMSucc (2, L - 1) ∉ t := hfree.2 (2, L - 1) hmem
          rw [triMSucc_two, hL1] at hs
          exact hs h0L
        · rw [ite_eq_right h0] at ha
          exact absurd ha (Finset.notMem_empty _)
    have hteq : t = rest ∪ wColAt u L := by
      ext ⟨a, j⟩
      rw [Finset.mem_union]
      constructor
      · intro hp
        have hvt := hsub hp
        rw [mem_triVert] at hvt
        by_cases hj : j < L
        · exact Or.inl (Finset.mem_filter.mpr ⟨hp, hj⟩)
        · have hjL : j = L := by omega
          subst hjL
          refine Or.inr ?_
          rw [wColAt, Finset.mem_image]
          exact ⟨a, (hu_mem a).mpr hp, rfl⟩
      · rintro (hp | hp)
        · exact (Finset.mem_filter.mp hp).1
        · rw [wColAt, Finset.mem_image] at hp
          obtain ⟨b, hb, hbeq⟩ := hp
          obtain ⟨hab, hjl⟩ := Prod.ext_iff.mp hbeq
          subst hab
          subst hjl
          exact (hu_mem b).mp hb
    rw [Finset.mem_image]
    exact ⟨rest, mem_wAvoid.mpr ⟨hrest_wSets, hrest_avoid⟩, hteq.symm⟩
  · rintro ⟨u, hu, hmem⟩
    rw [Finset.mem_image] at hmem
    obtain ⟨t', ht', rfl⟩ := hmem
    rw [mem_wAvoid, mem_wSets] at ht'
    obtain ⟨⟨hsub', hfree'⟩, havoid⟩ := ht'
    obtain ⟨hallow1, hallow2⟩ := allowedCols_spec hu
    refine ⟨?_, ⟨?_, ?_⟩⟩
    · rintro ⟨a, j⟩ hp
      rw [Finset.mem_union] at hp
      rw [mem_triVert]
      rcases hp with hp | hp
      · have hv := hsub' hp
        rw [mem_triVert] at hv
        omega
      · rw [wColAt, Finset.mem_image] at hp
        obtain ⟨b, -, hb⟩ := hp
        have hjl : j = L := (Prod.ext_iff.mp hb).2.symm
        rw [hjl]
        exact Nat.lt_succ_self L
    · rintro ⟨a, j⟩ hp hC
      rw [Finset.mem_union] at hp hC
      rcases hp with hp | hp
      · rcases hC with hC | hC
        · exact hfree'.1 (a, j) hp hC
        · rw [wColAt, Finset.mem_image] at hC
          obtain ⟨b, hb, hbeq⟩ := hC
          have hba : b = a := (Prod.ext_iff.mp hbeq).1
          have hjb : L = j + 1 := (Prod.ext_iff.mp hbeq).2
          have hja : j = L - 1 := by omega
          have hau : a ∈ u := hba ▸ hb
          have hF : a ∈ wForbid u := Finset.mem_union_left _ hau
          have hp2 : (a, L - 1) ∈ t' := hja ▸ hp
          exact havoid a hF hp2
      · rw [wColAt, Finset.mem_image] at hp
        obtain ⟨b, hb, hbeq⟩ := hp
        have hba : b = a := (Prod.ext_iff.mp hbeq).1
        have hjb : L = j := (Prod.ext_iff.mp hbeq).2
        subst hba
        subst hjb
        rcases hC with hC | hC
        · have hv := hsub' hC
          rw [mem_triVert] at hv
          have hv2 : L + 1 < L := hv
          omega
        · rw [wColAt, Finset.mem_image] at hC
          obtain ⟨c, -, hceq⟩ := hC
          have hll : L = L + 1 := (Prod.ext_iff.mp hceq).2
          omega
    · rintro ⟨a, j⟩ hp hC
      rw [Finset.mem_union] at hp hC
      rcases hp with hp | hp
      · rcases hC with hC | hC
        · exact hfree'.2 (a, j) hp hC
        · rw [wColAt, Finset.mem_image] at hC
          obtain ⟨b, hb, hbeq⟩ := hC
          have hl := hsub' hp
          rw [mem_triVert] at hl
          rcases (show ∀ a : Fin 3, a = 0 ∨ a = 1 ∨ a = 2 from by decide) a
            with rfl | rfl | rfl
          · rw [triMSucc_zero] at hbeq
            have hjl : j = L := (Prod.ext_iff.mp hbeq).2.symm
            omega
          · rw [triMSucc_one] at hbeq
            have hjl : j = L := (Prod.ext_iff.mp hbeq).2.symm
            omega
          · rw [triMSucc_two] at hbeq
            have hb0 : b = 0 := (Prod.ext_iff.mp hbeq).1
            have hjL : L = j + 1 := (Prod.ext_iff.mp hbeq).2
            have h0u : (0 : Fin 3) ∈ u := hb0 ▸ hb
            have hF : (2 : Fin 3) ∈ wForbid u := by
              have h2mem : (2 : Fin 3) ∈
                  (if (0 : Fin 3) ∈ u then {(2 : Fin 3)}
                    else (∅ : Finset (Fin 3))) := by
                rw [ite_eq_left h0u]
                exact Finset.mem_singleton_self _
              exact Finset.mem_union_right _ h2mem
            have hj : j = L - 1 := by omega
            have hp2 : (2, L - 1) ∈ t' := hj ▸ hp
            exact havoid 2 hF hp2
      · rw [wColAt, Finset.mem_image] at hp
        obtain ⟨c, hc, hceq⟩ := hp
        have hca : c = a := (Prod.ext_iff.mp hceq).1
        have hcL : L = j := (Prod.ext_iff.mp hceq).2
        subst hca
        subst hcL
        rcases hC with hC | hC
        · have hv := hsub' hC
          rw [mem_triVert] at hv
          rcases (show ∀ c : Fin 3, c = 0 ∨ c = 1 ∨ c = 2 from by decide) c
            with rfl | rfl | rfl
          · rw [triMSucc_zero] at hv
            have hv2 : L < L := hv
            omega
          · rw [triMSucc_one] at hv
            have hv2 : L < L := hv
            omega
          · rw [triMSucc_two] at hv
            have hv2 : L + 1 < L := hv
            omega
        · rw [wColAt, Finset.mem_image] at hC
          obtain ⟨d, hd, hdeq⟩ := hC
          rcases (show ∀ c : Fin 3, c = 0 ∨ c = 1 ∨ c = 2 from by decide) c
            with rfl | rfl | rfl
          · rw [triMSucc_zero] at hdeq
            have hd1e : d = 1 := (Prod.ext_iff.mp hdeq).1
            have hd1 : (1 : Fin 3) ∈ u := hd1e ▸ hd
            exact hallow1 ⟨hc, hd1⟩
          · rw [triMSucc_one] at hdeq
            have hd2e : d = 2 := (Prod.ext_iff.mp hdeq).1
            have hd2 : (2 : Fin 3) ∈ u := hd2e ▸ hd
            exact hallow2 ⟨hc, hd2⟩
          · rw [triMSucc_two] at hdeq
            have hll : L = L + 1 := (Prod.ext_iff.mp hdeq).2
            omega

/-- The pieces of the column decomposition are pairwise disjoint:
the column-`L` part of `t ∪ wColAt u L` is exactly `u`. -/
theorem wSets_succ_disj (L : ℕ) :
    (↑allowedCols : Set (Finset (Fin 3))).PairwiseDisjoint fun u =>
      (wAvoid (wForbid u) L).image fun t => t ∪ wColAt u L := by
  rintro u - u' - huu'
  show Disjoint _ _
  rw [Finset.disjoint_left]
  intro t ht ht'
  rw [Finset.mem_image] at ht ht'
  obtain ⟨t₁, ht₁, rfl⟩ := ht
  obtain ⟨t₂, ht₂, hteq⟩ := ht'
  rw [mem_wAvoid, mem_wSets] at ht₁ ht₂
  have e := congrArg (Finset.filter fun p => p.2 = L) hteq.symm
  rw [filter_union_wColAt_eq_self ht₁.1.1, filter_union_wColAt_eq_self ht₂.1.1]
    at e
  exact huu' (wColAt_inj e)

/-- Inserting the column `wColAt u L` is injective on the avoiding
family (the part below level `L` is recoverable by filtering). -/
theorem card_wAvoid_image_union (S u : Finset (Fin 3)) (L : ℕ) :
    ((wAvoid S L).image fun t => t ∪ wColAt u L).card =
      (wAvoid S L).card := by
  apply Finset.card_image_of_injOn
  intro t₁ ht₁ t₂ ht₂ h
  rw [Finset.mem_coe, mem_wAvoid, mem_wSets] at ht₁ ht₂
  have e := congrArg (Finset.filter fun p => p.2 < L) h
  rw [filter_union_wColAt_lt_self ht₁.1.1, filter_union_wColAt_lt_self ht₂.1.1]
    at e
  exact e

/-- `wAvoid ∅` is the whole family. -/
theorem wAvoid_empty (L : ℕ) : wAvoid ∅ L = wSets L := by
  ext t
  rw [mem_wAvoid]
  simp

/-- `W(L+1) = W + A₁ + A₂ + 2·A₀₂`. -/
theorem card_wSets_succ (L : ℕ) :
    (wSets (L + 1)).card = (wSets L).card + (wAvoid {(1 : Fin 3)} L).card +
      (wAvoid {(2 : Fin 3)} L).card +
        2 * (wAvoid {(0 : Fin 3), (2 : Fin 3)} L).card := by
  rw [wSets_succ, Finset.card_biUnion (wSets_succ_disj L)]
  rw [Finset.sum_congr rfl (fun u _ => card_wAvoid_image_union _ _ L)]
  rw [show allowedCols = {∅, {0}, {1}, {2}, {0, 2}} from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  rw [show wForbid (∅ : Finset (Fin 3)) = ∅ from by decide,
    show wForbid {(0 : Fin 3)} = {(0 : Fin 3), (2 : Fin 3)} from by decide,
    show wForbid {(1 : Fin 3)} = {(1 : Fin 3)} from by decide,
    show wForbid {(2 : Fin 3)} = {(2 : Fin 3)} from by decide,
    show wForbid {(0 : Fin 3), (2 : Fin 3)} = {(0 : Fin 3), (2 : Fin 3)}
      from by decide,
    wAvoid_empty]
  ring

/-- **Avoiding decomposition.**  The avoiding family at level `L+1`
splits over the last-column states disjoint from `S`. -/
theorem wAvoid_succ (S : Finset (Fin 3)) (L : ℕ) :
    wAvoid S (L + 1) = (allowedCols.filter fun u => ∀ a ∈ S, a ∉ u).biUnion
      fun u => (wAvoid (wForbid u) L).image fun t => t ∪ wColAt u L := by
  ext t
  rw [mem_wAvoid, wSets_succ, Finset.mem_biUnion, Finset.mem_biUnion]
  simp only [Nat.add_sub_cancel]
  constructor
  · rintro ⟨⟨u, hu, hmem⟩, havoid⟩
    refine ⟨u, Finset.mem_filter.mpr ⟨hu, ?_⟩, hmem⟩
    intro a haS hau
    rw [Finset.mem_image] at hmem
    obtain ⟨rest, hrest, rfl⟩ := hmem
    have haL : (a, L) ∈ rest ∪ wColAt u L :=
      Finset.mem_union_right _ (Finset.mem_image.mpr ⟨a, hau, rfl⟩)
    exact havoid a haS haL
  · rintro ⟨u, hu, hmem⟩
    rw [Finset.mem_filter] at hu
    obtain ⟨hu, hdisj⟩ := hu
    refine ⟨⟨u, hu, hmem⟩, ?_⟩
    rw [Finset.mem_image] at hmem
    obtain ⟨rest, hrest, rfl⟩ := hmem
    rw [mem_wAvoid] at hrest
    intro a haS hcontra
    rw [Finset.mem_union] at hcontra
    rcases hcontra with hcontra | hcontra
    · rw [mem_wSets] at hrest
      have hv := hrest.1.1 hcontra
      rw [mem_triVert] at hv
      have hv2 : L < L := hv
      omega
    · rw [wColAt, Finset.mem_image] at hcontra
      obtain ⟨b, hb, hbeq⟩ := hcontra
      have hab : a = b := (Prod.ext_iff.mp hbeq).1.symm
      subst hab
      exact hdisj a haS hb

/-- Cardinal form of the avoiding decomposition. -/
theorem card_wAvoid_succ (S : Finset (Fin 3)) (L : ℕ) :
    (wAvoid S (L + 1)).card =
      ∑ u ∈ allowedCols.filter (fun u => ∀ a ∈ S, a ∉ u),
        (wAvoid (wForbid u) L).card := by
  rw [wAvoid_succ, Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro u _
    exact card_wAvoid_image_union _ _ L
  · intro u hu u' hu' huu'
    rw [Finset.mem_coe, Finset.mem_filter] at hu hu'
    exact wSets_succ_disj L hu.1 hu'.1 huu'

/-- `A₁(L+1) = W + A₂ + 2·A₀₂`. -/
theorem card_wAvoid_one_succ (L : ℕ) :
    (wAvoid {(1 : Fin 3)} (L + 1)).card = (wSets L).card +
      (wAvoid {(2 : Fin 3)} L).card +
        2 * (wAvoid {(0 : Fin 3), (2 : Fin 3)} L).card := by
  rw [card_wAvoid_succ]
  have hf : allowedCols.filter (fun u => ∀ a ∈ ({(1 : Fin 3)} : Finset (Fin 3)),
      a ∉ u) = {∅, {0}, {2}, {0, 2}} := by
    decide
  rw [hf, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [show wForbid (∅ : Finset (Fin 3)) = ∅ from by decide,
    show wForbid {(0 : Fin 3)} = {(0 : Fin 3), (2 : Fin 3)} from by decide,
    show wForbid {(2 : Fin 3)} = {(2 : Fin 3)} from by decide,
    show wForbid {(0 : Fin 3), (2 : Fin 3)} = {(0 : Fin 3), (2 : Fin 3)}
      from by decide,
    wAvoid_empty]
  ring

/-- `A₂(L+1) = W + A₁ + A₀₂`. -/
theorem card_wAvoid_two_succ (L : ℕ) :
    (wAvoid {(2 : Fin 3)} (L + 1)).card = (wSets L).card +
      (wAvoid {(1 : Fin 3)} L).card +
        (wAvoid {(0 : Fin 3), (2 : Fin 3)} L).card := by
  rw [card_wAvoid_succ]
  have hf : allowedCols.filter (fun u => ∀ a ∈ ({(2 : Fin 3)} : Finset (Fin 3)),
      a ∉ u) = {∅, {0}, {1}} := by
    decide
  rw [hf, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  rw [show wForbid (∅ : Finset (Fin 3)) = ∅ from by decide,
    show wForbid {(0 : Fin 3)} = {(0 : Fin 3), (2 : Fin 3)} from by decide,
    show wForbid {(1 : Fin 3)} = {(1 : Fin 3)} from by decide,
    wAvoid_empty]
  ring

/-- `A₀₂(L+1) = W + A₁`. -/
theorem card_wAvoid_zero_two_succ (L : ℕ) :
    (wAvoid {(0 : Fin 3), (2 : Fin 3)} (L + 1)).card = (wSets L).card +
      (wAvoid {(1 : Fin 3)} L).card := by
  rw [card_wAvoid_succ]
  have hf : allowedCols.filter
      (fun u => ∀ a ∈ ({(0 : Fin 3), (2 : Fin 3)} : Finset (Fin 3)), a ∉ u) =
      {∅, {1}} := by
    decide
  rw [hf, Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [show wForbid (∅ : Finset (Fin 3)) = ∅ from by decide,
    show wForbid {(1 : Fin 3)} = {(1 : Fin 3)} from by decide,
    wAvoid_empty]

/-- Base family: `wSets 0 = {∅}`. -/
theorem wSets_zero : wSets 0 = {∅} := by
  ext t
  rw [mem_wSets, triVert_zero, Finset.subset_empty, Finset.mem_singleton]
  refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
  subst h
  exact ⟨fun p hp => absurd hp (Finset.notMem_empty _),
    fun p hp => absurd hp (Finset.notMem_empty _)⟩

/-- Every avoiding family at level `0` is `{∅}`. -/
theorem wAvoid_zero (S : Finset (Fin 3)) : wAvoid S 0 = {∅} := by
  ext t
  rw [mem_wAvoid, wSets_zero, Finset.mem_singleton]
  refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
  subst h
  intro a _
  exact Finset.notMem_empty _

/-- **The strip bound.**  Simultaneous induction on the four families
with weights `(27, 21, 18, 14)`: the recurrences give
`2·(27+21+18+2·14) = 188 ≤ 189 = 7·27`,
`2·(27+18+2·14) = 146 ≤ 147 = 7·21`,
`2·(27+21+14) = 124 ≤ 126 = 7·18`, and
`2·(27+21) = 96 ≤ 98 = 7·14`. -/
theorem wSets_card_mul_two_pow_le_aux (L : ℕ) :
    (wSets L).card * 2 ^ L ≤ 27 * 7 ^ L ∧
      (wAvoid {(1 : Fin 3)} L).card * 2 ^ L ≤ 21 * 7 ^ L ∧
        (wAvoid {(2 : Fin 3)} L).card * 2 ^ L ≤ 18 * 7 ^ L ∧
          (wAvoid {(0 : Fin 3), (2 : Fin 3)} L).card * 2 ^ L ≤ 14 * 7 ^ L := by
  induction L with
  | zero =>
      rw [wSets_zero, wAvoid_zero, wAvoid_zero, wAvoid_zero,
        Finset.card_singleton]
      norm_num
  | succ L ih =>
      obtain ⟨ihW, ih1, ih2, ih02⟩ := ih
      have e2 : (2 : ℕ) ^ (L + 1) = 2 * 2 ^ L := pow_succ' _ _
      have e7 : (7 : ℕ) ^ (L + 1) = 7 * 7 ^ L := pow_succ' _ _
      rw [card_wSets_succ, card_wAvoid_one_succ, card_wAvoid_two_succ,
        card_wAvoid_zero_two_succ]
      refine ⟨?_, ?_, ?_, ?_⟩
      · calc ((wSets L).card + (wAvoid {(1 : Fin 3)} L).card +
                (wAvoid {(2 : Fin 3)} L).card +
                  2 * (wAvoid {(0 : Fin 3), (2 : Fin 3)} L).card) * 2 ^ (L + 1)
            = 2 * ((wSets L).card * 2 ^ L + (wAvoid {(1 : Fin 3)} L).card * 2 ^ L
                + (wAvoid {(2 : Fin 3)} L).card * 2 ^ L +
                  2 * ((wAvoid {(0 : Fin 3), (2 : Fin 3)} L).card * 2 ^ L)) := by
              rw [e2]; ring
          _ ≤ 2 * (27 * 7 ^ L + 21 * 7 ^ L + 18 * 7 ^ L + 2 * (14 * 7 ^ L)) :=
              Nat.mul_le_mul (le_refl 2)
                (add_le_add (add_le_add (add_le_add ihW ih1) ih2)
                  (Nat.mul_le_mul (le_refl 2) ih02))
          _ = 188 * 7 ^ L := by ring
          _ ≤ 27 * 7 ^ (L + 1) := by
              rw [e7]
              calc 188 * 7 ^ L ≤ 189 * 7 ^ L :=
                    Nat.mul_le_mul (by norm_num) (le_refl _)
                _ = 27 * (7 * 7 ^ L) := by ring
      · calc ((wSets L).card + (wAvoid {(2 : Fin 3)} L).card +
                2 * (wAvoid {(0 : Fin 3), (2 : Fin 3)} L).card) * 2 ^ (L + 1)
            = 2 * ((wSets L).card * 2 ^ L + (wAvoid {(2 : Fin 3)} L).card * 2 ^ L
                + 2 * ((wAvoid {(0 : Fin 3), (2 : Fin 3)} L).card * 2 ^ L)) := by
              rw [e2]; ring
          _ ≤ 2 * (27 * 7 ^ L + 18 * 7 ^ L + 2 * (14 * 7 ^ L)) :=
              Nat.mul_le_mul (le_refl 2)
                (add_le_add (add_le_add ihW ih2)
                  (Nat.mul_le_mul (le_refl 2) ih02))
          _ = 146 * 7 ^ L := by ring
          _ ≤ 21 * 7 ^ (L + 1) := by
              rw [e7]
              calc 146 * 7 ^ L ≤ 147 * 7 ^ L :=
                    Nat.mul_le_mul (by norm_num) (le_refl _)
                _ = 21 * (7 * 7 ^ L) := by ring
      · calc ((wSets L).card + (wAvoid {(1 : Fin 3)} L).card +
                (wAvoid {(0 : Fin 3), (2 : Fin 3)} L).card) * 2 ^ (L + 1)
            = 2 * ((wSets L).card * 2 ^ L + (wAvoid {(1 : Fin 3)} L).card * 2 ^ L
                + (wAvoid {(0 : Fin 3), (2 : Fin 3)} L).card * 2 ^ L) := by
              rw [e2]; ring
          _ ≤ 2 * (27 * 7 ^ L + 21 * 7 ^ L + 14 * 7 ^ L) :=
              Nat.mul_le_mul (le_refl 2)
                (add_le_add (add_le_add ihW ih1) ih02)
          _ = 124 * 7 ^ L := by ring
          _ ≤ 18 * 7 ^ (L + 1) := by
              rw [e7]
              calc 124 * 7 ^ L ≤ 126 * 7 ^ L :=
                    Nat.mul_le_mul (by norm_num) (le_refl _)
                _ = 18 * (7 * 7 ^ L) := by ring
      · calc ((wSets L).card + (wAvoid {(1 : Fin 3)} L).card) * 2 ^ (L + 1)
            = 2 * ((wSets L).card * 2 ^ L +
                (wAvoid {(1 : Fin 3)} L).card * 2 ^ L) := by
              rw [e2]; ring
          _ ≤ 2 * (27 * 7 ^ L + 21 * 7 ^ L) :=
              Nat.mul_le_mul (le_refl 2) (add_le_add ihW ih1)
          _ = 96 * 7 ^ L := by ring
          _ ≤ 14 * 7 ^ (L + 1) := by
              rw [e7]
              calc 96 * 7 ^ L ≤ 98 * 7 ^ L :=
                    Nat.mul_le_mul (by norm_num) (le_refl _)
                _ = 14 * (7 * 7 ^ L) := by ring

/-- **Integer-normalised bound.**  `W(L)·2^L ≤ 27·7^L`, i.e.
`W(L) ≤ 27·(7/2)^L`. -/
theorem wSets_card_mul_two_pow_le (L : ℕ) :
    (wSets L).card * 2 ^ L ≤ 27 * 7 ^ L :=
  (wSets_card_mul_two_pow_le_aux L).1

/-- **The wrap-strip bound.**  Double-shift-free subsets of the triple
union `U_r` inject (via `triIdx`) into the independent sets of the wrap
strip of length `L = ((n - r)/(3m)).toNat`, the longest rail. -/
theorem card_powerset_filter_shiftFree2_tri_cls_le {n : ℕ} {m r : ℤ}
    (hm : 1 ≤ m) (hr : 1 ≤ r) (hrm : r ≤ m) :
    ((cls n (3 * m) r ∪ cls n (3 * m) (r + m) ∪
        cls n (3 * m) (r + 2 * m)).powerset.filter
          (shiftFree2 m (3 * m))).card ≤
      (wSets (((n : ℤ) - r) / (3 * m)).toNat).card := by
  have h3m : 0 < 3 * m := by omega
  have hsn : 3 * m ≠ 0 := ne_of_gt h3m
  have hL1 : (((n : ℤ) - (r + m)) / (3 * m)).toNat ≤
      (((n : ℤ) - r) / (3 * m)).toNat :=
    Int.toNat_le_toNat (Int.ediv_le_ediv h3m (by omega))
  have hL2 : (((n : ℤ) - (r + 2 * m)) / (3 * m)).toNat ≤
      (((n : ℤ) - r) / (3 * m)).toNat :=
    Int.toNat_le_toNat (Int.ediv_le_ediv h3m (by omega))
  have hr0 : r ∈ Finset.Icc 1 (3 * m) := by rw [Finset.mem_Icc]; omega
  have hr1 : r + m ∈ Finset.Icc 1 (3 * m) := by rw [Finset.mem_Icc]; omega
  have hr2 : r + 2 * m ∈ Finset.Icc 1 (3 * m) := by rw [Finset.mem_Icc]; omega
  have hinj := triIdx_injOn (n := n) hm hr hrm
  refine Finset.card_le_card_of_injOn (Finset.image (triIdx n m r)) ?_ ?_
  · intro T hT
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset] at hT
    obtain ⟨hTU, hsm, hss⟩ := hT
    rw [Finset.mem_coe, mem_wSets]
    refine ⟨?_, ⟨?_, ?_⟩⟩
    · rintro ⟨a, j⟩ hp
      rw [Finset.mem_image] at hp
      obtain ⟨x, hxT, hxeq⟩ := hp
      rw [mem_triVert]
      have hxU := hTU hxT
      rw [Finset.mem_union, Finset.mem_union] at hxU
      rcases hxU with (hx | hx) | hx
      · obtain ⟨kx, hkx, rfl⟩ := mem_cls_iff.mp hx
        rw [triIdx_cls0 hsn hx] at hxeq
        have hk : j = kx := (Prod.ext_iff.mp hxeq).2.symm
        rw [hk]
        exact hkx
      · obtain ⟨kx, hkx, rfl⟩ := mem_cls_iff.mp hx
        have hxr := cls_tri_nmem hm hr1 hr0 (by omega) hx
        rw [triIdx_cls1 hsn hxr hx] at hxeq
        have hk : j = kx := (Prod.ext_iff.mp hxeq).2.symm
        rw [hk]
        exact lt_of_lt_of_le hkx hL1
      · obtain ⟨kx, hkx, rfl⟩ := mem_cls_iff.mp hx
        have hxr := cls_tri_nmem hm hr2 hr0 (by omega) hx
        have hxr1 := cls_tri_nmem hm hr2 hr1 (by omega) hx
        rw [triIdx_cls2 hsn hxr hxr1] at hxeq
        have hk : j = kx := (Prod.ext_iff.mp hxeq).2.symm
        rw [hk]
        exact lt_of_lt_of_le hkx hL2
    · -- no rail-successor: `x ∈ T` forces `x + 3m ∉ T` on the same rail
      intro p hp hC
      rw [Finset.mem_image] at hp hC
      obtain ⟨x, hxT, hpx⟩ := hp
      obtain ⟨y, hyT, hpy⟩ := hC
      have hxU := hTU hxT
      have hyU := hTU hyT
      rw [Finset.mem_union, Finset.mem_union] at hxU hyU
      rcases hxU with (hx | hx) | hx
      · obtain ⟨kx, -, rfl⟩ := mem_cls_iff.mp hx
        rw [triIdx_cls0 hsn hx] at hpx
        have hp' : (p.1, p.2 + 1) = (0, kx + 1) := by rw [← hpx]
        rw [hp'] at hpy
        rcases hyU with (hy | hy) | hy
        · obtain ⟨ky, -, rfl⟩ := mem_cls_iff.mp hy
          rw [triIdx_cls0 hsn hy] at hpy
          have hky : ky = kx + 1 := (Prod.ext_iff.mp hpy).2
          have hEq : r + 3 * m + 3 * m * (ky : ℤ) =
              (r + 3 * m + 3 * m * (kx : ℤ)) + 3 * m := by
            rw [hky]; push_cast; ring
          rw [hEq] at hyT
          exact hss _ hxT hyT
        · obtain ⟨ky, -, rfl⟩ := mem_cls_iff.mp hy
          have hyr := cls_tri_nmem hm hr1 hr0 (by omega) hy
          rw [triIdx_cls1 hsn hyr hy] at hpy
          simp only [Prod.mk.injEq] at hpy
          exact absurd hpy.1 (by decide)
        · obtain ⟨ky, -, rfl⟩ := mem_cls_iff.mp hy
          have hyr := cls_tri_nmem hm hr2 hr0 (by omega) hy
          have hyr1 := cls_tri_nmem hm hr2 hr1 (by omega) hy
          rw [triIdx_cls2 hsn hyr hyr1] at hpy
          simp only [Prod.mk.injEq] at hpy
          exact absurd hpy.1 (by decide)
      · obtain ⟨kx, -, rfl⟩ := mem_cls_iff.mp hx
        have hxr := cls_tri_nmem hm hr1 hr0 (by omega) hx
        rw [triIdx_cls1 hsn hxr hx] at hpx
        have hp' : (p.1, p.2 + 1) = (1, kx + 1) := by rw [← hpx]
        rw [hp'] at hpy
        rcases hyU with (hy | hy) | hy
        · obtain ⟨ky, -, rfl⟩ := mem_cls_iff.mp hy
          rw [triIdx_cls0 hsn hy] at hpy
          simp only [Prod.mk.injEq] at hpy
          exact absurd hpy.1 (by decide)
        · obtain ⟨ky, -, rfl⟩ := mem_cls_iff.mp hy
          have hyr := cls_tri_nmem hm hr1 hr0 (by omega) hy
          rw [triIdx_cls1 hsn hyr hy] at hpy
          have hky : ky = kx + 1 := (Prod.ext_iff.mp hpy).2
          have hEq : r + m + 3 * m + 3 * m * (ky : ℤ) =
              (r + m + 3 * m + 3 * m * (kx : ℤ)) + 3 * m := by
            rw [hky]; push_cast; ring
          rw [hEq] at hyT
          exact hss _ hxT hyT
        · obtain ⟨ky, -, rfl⟩ := mem_cls_iff.mp hy
          have hyr := cls_tri_nmem hm hr2 hr0 (by omega) hy
          have hyr1 := cls_tri_nmem hm hr2 hr1 (by omega) hy
          rw [triIdx_cls2 hsn hyr hyr1] at hpy
          simp only [Prod.mk.injEq] at hpy
          exact absurd hpy.1 (by decide)
      · obtain ⟨kx, -, rfl⟩ := mem_cls_iff.mp hx
        have hxr := cls_tri_nmem hm hr2 hr0 (by omega) hx
        have hxr1 := cls_tri_nmem hm hr2 hr1 (by omega) hx
        rw [triIdx_cls2 hsn hxr hxr1] at hpx
        have hp' : (p.1, p.2 + 1) = (2, kx + 1) := by rw [← hpx]
        rw [hp'] at hpy
        rcases hyU with (hy | hy) | hy
        · obtain ⟨ky, -, rfl⟩ := mem_cls_iff.mp hy
          rw [triIdx_cls0 hsn hy] at hpy
          simp only [Prod.mk.injEq] at hpy
          exact absurd hpy.1 (by decide)
        · obtain ⟨ky, -, rfl⟩ := mem_cls_iff.mp hy
          have hyr := cls_tri_nmem hm hr1 hr0 (by omega) hy
          rw [triIdx_cls1 hsn hyr hy] at hpy
          simp only [Prod.mk.injEq] at hpy
          exact absurd hpy.1 (by decide)
        · obtain ⟨ky, -, rfl⟩ := mem_cls_iff.mp hy
          have hyr := cls_tri_nmem hm hr2 hr0 (by omega) hy
          have hyr1 := cls_tri_nmem hm hr2 hr1 (by omega) hy
          rw [triIdx_cls2 hsn hyr hyr1] at hpy
          have hky : ky = kx + 1 := (Prod.ext_iff.mp hpy).2
          have hEq : r + 2 * m + 3 * m + 3 * m * (ky : ℤ) =
              (r + 2 * m + 3 * m + 3 * m * (kx : ℤ)) + 3 * m := by
            rw [hky]; push_cast; ring
          rw [hEq] at hyT
          exact hss _ hxT hyT
    · -- no `+m`-neighbour: `x ∈ T` forces `x + m ∉ T`
      intro p hp hC
      rw [Finset.mem_image] at hp hC
      obtain ⟨x, hxT, hpx⟩ := hp
      obtain ⟨y, hyT, hpy⟩ := hC
      have hxU := hTU hxT
      have hyU := hTU hyT
      rw [Finset.mem_union, Finset.mem_union] at hxU hyU
      rcases hxU with (hx | hx) | hx
      · -- rail 0: `triMSucc (0, kx) = (1, kx)` forces `y` on rail 1
        obtain ⟨kx, -, rfl⟩ := mem_cls_iff.mp hx
        rw [triIdx_cls0 hsn hx] at hpx
        rw [← hpx, triMSucc_zero] at hpy
        rcases hyU with (hy | hy) | hy
        · obtain ⟨ky, -, rfl⟩ := mem_cls_iff.mp hy
          rw [triIdx_cls0 hsn hy] at hpy
          simp only [Prod.mk.injEq] at hpy
          exact absurd hpy.1 (by decide)
        · obtain ⟨ky, -, rfl⟩ := mem_cls_iff.mp hy
          have hyr := cls_tri_nmem hm hr1 hr0 (by omega) hy
          rw [triIdx_cls1 hsn hyr hy] at hpy
          have hky : ky = kx := (Prod.ext_iff.mp hpy).2
          have hEq : r + m + 3 * m + 3 * m * (ky : ℤ) =
              (r + 3 * m + 3 * m * (kx : ℤ)) + m := by
            rw [hky]; ring
          rw [hEq] at hyT
          exact hsm _ hxT hyT
        · obtain ⟨ky, -, rfl⟩ := mem_cls_iff.mp hy
          have hyr := cls_tri_nmem hm hr2 hr0 (by omega) hy
          have hyr1 := cls_tri_nmem hm hr2 hr1 (by omega) hy
          rw [triIdx_cls2 hsn hyr hyr1] at hpy
          simp only [Prod.mk.injEq] at hpy
          exact absurd hpy.1 (by decide)
      · -- rail 1: `triMSucc (1, kx) = (2, kx)` forces `y` on rail 2
        obtain ⟨kx, -, rfl⟩ := mem_cls_iff.mp hx
        have hxr := cls_tri_nmem hm hr1 hr0 (by omega) hx
        rw [triIdx_cls1 hsn hxr hx] at hpx
        rw [← hpx, triMSucc_one] at hpy
        rcases hyU with (hy | hy) | hy
        · obtain ⟨ky, -, rfl⟩ := mem_cls_iff.mp hy
          rw [triIdx_cls0 hsn hy] at hpy
          simp only [Prod.mk.injEq] at hpy
          exact absurd hpy.1 (by decide)
        · obtain ⟨ky, -, rfl⟩ := mem_cls_iff.mp hy
          have hyr := cls_tri_nmem hm hr1 hr0 (by omega) hy
          rw [triIdx_cls1 hsn hyr hy] at hpy
          simp only [Prod.mk.injEq] at hpy
          exact absurd hpy.1 (by decide)
        · obtain ⟨ky, -, rfl⟩ := mem_cls_iff.mp hy
          have hyr := cls_tri_nmem hm hr2 hr0 (by omega) hy
          have hyr1 := cls_tri_nmem hm hr2 hr1 (by omega) hy
          rw [triIdx_cls2 hsn hyr hyr1] at hpy
          have hky : ky = kx := (Prod.ext_iff.mp hpy).2
          have hEq : r + 2 * m + 3 * m + 3 * m * (ky : ℤ) =
              (r + m + 3 * m + 3 * m * (kx : ℤ)) + m := by
            rw [hky]; ring
          rw [hEq] at hyT
          exact hsm _ hxT hyT
      · -- rail 2: `triMSucc (2, kx) = (0, kx+1)` forces `y` on rail 0
        obtain ⟨kx, -, rfl⟩ := mem_cls_iff.mp hx
        have hxr := cls_tri_nmem hm hr2 hr0 (by omega) hx
        have hxr1 := cls_tri_nmem hm hr2 hr1 (by omega) hx
        rw [triIdx_cls2 hsn hxr hxr1] at hpx
        rw [← hpx, triMSucc_two] at hpy
        rcases hyU with (hy | hy) | hy
        · obtain ⟨ky, -, rfl⟩ := mem_cls_iff.mp hy
          rw [triIdx_cls0 hsn hy] at hpy
          have hky : ky = kx + 1 := (Prod.ext_iff.mp hpy).2
          have hEq : r + 3 * m + 3 * m * (ky : ℤ) =
              (r + 2 * m + 3 * m + 3 * m * (kx : ℤ)) + m := by
            rw [hky]; push_cast; ring
          rw [hEq] at hyT
          exact hsm _ hxT hyT
        · obtain ⟨ky, -, rfl⟩ := mem_cls_iff.mp hy
          have hyr := cls_tri_nmem hm hr1 hr0 (by omega) hy
          rw [triIdx_cls1 hsn hyr hy] at hpy
          simp only [Prod.mk.injEq] at hpy
          exact absurd hpy.1 (by decide)
        · obtain ⟨ky, -, rfl⟩ := mem_cls_iff.mp hy
          have hyr := cls_tri_nmem hm hr2 hr0 (by omega) hy
          have hyr1 := cls_tri_nmem hm hr2 hr1 (by omega) hy
          rw [triIdx_cls2 hsn hyr hyr1] at hpy
          simp only [Prod.mk.injEq] at hpy
          exact absurd hpy.1 (by decide)
  · -- `T ↦ T.image triIdx` is injective on subsets of the rail union
    intro T₁ hT₁ T₂ hT₂ h
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset] at hT₁ hT₂
    ext x
    constructor
    · intro hx
      have hxU : x ∈ cls n (3 * m) r ∪ cls n (3 * m) (r + m) ∪
          cls n (3 * m) (r + 2 * m) := hT₁.1 hx
      have hmem : triIdx n m r x ∈ T₂.image (triIdx n m r) := by
        rw [← h]
        exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
      obtain ⟨y, hyT, hyeq⟩ := Finset.mem_image.mp hmem
      have hyU : y ∈ cls n (3 * m) r ∪ cls n (3 * m) (r + m) ∪
          cls n (3 * m) (r + 2 * m) := hT₂.1 hyT
      have hxy : x = y := hinj hxU hyU hyeq.symm
      rwa [hxy]
    · intro hx
      have hxU : x ∈ cls n (3 * m) r ∪ cls n (3 * m) (r + m) ∪
          cls n (3 * m) (r + 2 * m) := hT₂.1 hx
      have hmem : triIdx n m r x ∈ T₁.image (triIdx n m r) := by
        rw [h]
        exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
      obtain ⟨y, hyT, hyeq⟩ := Finset.mem_image.mp hmem
      have hyU : y ∈ cls n (3 * m) r ∪ cls n (3 * m) (r + m) ∪
          cls n (3 * m) (r + 2 * m) := hT₁.1 hyT
      have hxy : x = y := hinj hxU hyU hyeq.symm
      rwa [hxy]

/-- **Normalised triple bound.**  The double-shift-free count of `U_r`
times `2^{L_r}` is at most `27·7^{L_r}`. -/
theorem card_powerset_filter_shiftFree2_tri_cls_mul_le {n : ℕ} {m r : ℤ}
    (hm : 1 ≤ m) (hr : 1 ≤ r) (hrm : r ≤ m) :
    ((cls n (3 * m) r ∪ cls n (3 * m) (r + m) ∪
        cls n (3 * m) (r + 2 * m)).powerset.filter
          (shiftFree2 m (3 * m))).card *
        2 ^ (((n : ℤ) - r) / (3 * m)).toNat ≤
      27 * 7 ^ (((n : ℤ) - r) / (3 * m)).toNat :=
  (Nat.mul_le_mul
    (card_powerset_filter_shiftFree2_tri_cls_le hm hr hrm) (le_refl _)).trans
    (wSets_card_mul_two_pow_le _)

/-- **Triple cover.**  Every `x ∈ Icc (3m+1) n` lies in a class
`cls n (3m) ρ` with `ρ ∈ Icc 1 (3m)`; writing `ρ = r + a·m` with
`r ∈ Icc 1 m` and `a ∈ {0,1,2}` places `x` in the `r`-th triple
union. -/
theorem Icc_subset_biUnion_triCls {n : ℕ} {m : ℤ} (hm : 1 ≤ m) :
    Finset.Icc (3 * m + 1) (n : ℤ) ⊆ (Finset.Icc 1 m).biUnion
      (fun r => cls n (3 * m) r ∪ cls n (3 * m) (r + m) ∪
        cls n (3 * m) (r + 2 * m)) := by
  have h3m : 1 ≤ 3 * m := by omega
  intro x hx
  obtain ⟨ρ, hρ, hxρ⟩ := Finset.mem_biUnion.mp (Icc_subset_biUnion_cls h3m hx)
  rw [Finset.mem_Icc] at hρ
  rw [Finset.mem_biUnion]
  rcases lt_or_ge m ρ with h | h
  · -- `m < ρ`
    rcases lt_or_ge (2 * m) ρ with h2 | h2
    · -- `2 * m < ρ`
      refine ⟨ρ - 2 * m, by rw [Finset.mem_Icc]; omega, ?_⟩
      rw [Finset.mem_union]
      refine Or.inr ?_
      have e : ρ - 2 * m + 2 * m = ρ := by omega
      rwa [e]
    · -- `m < ρ ≤ 2 * m`
      refine ⟨ρ - m, by rw [Finset.mem_Icc]; omega, ?_⟩
      rw [Finset.mem_union]
      refine Or.inl ?_
      rw [Finset.mem_union]
      refine Or.inr ?_
      have e : ρ - m + m = ρ := by omega
      rwa [e]
  · -- `ρ ≤ m`
    exact ⟨ρ, by rw [Finset.mem_Icc]; omega,
      Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl hxρ)))⟩

/-- **Conditional product bound.**  The double-shift-free subsets of
`Icc (3m+1) n` are at most the product over the `m` orbits of their
wrap-strip counts. -/
theorem card_powerset_filter_shiftFree2_triIcc_le {n : ℕ} {m : ℤ}
    (hm : 1 ≤ m) :
    ((Finset.Icc (3 * m + 1) (n : ℤ)).powerset.filter
        (shiftFree2 m (3 * m))).card ≤
      ∏ r ∈ Finset.Icc 1 m,
        (wSets (((n : ℤ) - r) / (3 * m)).toNat).card :=
  (card_powerset_filter_shiftFree2_le_prod (Finset.Icc 1 m)
    (fun r => cls n (3 * m) r ∪ cls n (3 * m) (r + m) ∪
      cls n (3 * m) (r + 2 * m)) _
    (Icc_subset_biUnion_triCls hm)).trans
      (Finset.prod_le_prod fun _r hr =>
        card_powerset_filter_shiftFree2_tri_cls_le hm
          (Finset.mem_Icc.mp hr).1 (Finset.mem_Icc.mp hr).2)

/-- The orbit length sum is bounded by `n - 3m`: the longest rails are
only a third of the `3m` residue classes. -/
theorem sum_triCls_len_le {n : ℕ} {m : ℤ} (hm : 1 ≤ m) :
    ∑ r ∈ Finset.Icc 1 m, (((n : ℤ) - r) / (3 * m)).toNat ≤
      ((n : ℤ) - 3 * m).toNat := by
  have h3m : 1 ≤ 3 * m := by omega
  have hsub : Finset.Icc 1 m ⊆ Finset.Icc 1 (3 * m) := by
    intro x hx
    rw [Finset.mem_Icc] at hx ⊢
    omega
  calc ∑ r ∈ Finset.Icc 1 m, (((n : ℤ) - r) / (3 * m)).toNat
      ≤ ∑ r ∈ Finset.Icc 1 (3 * m), (((n : ℤ) - r) / (3 * m)).toNat :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun r _ _ => Nat.zero_le _)
    _ = ((n : ℤ) - 3 * m).toNat := sum_cls_card h3m

/-- **Closed bound.**  Combining the orbit product with the per-orbit
normalised estimate `card · 2^{L_r} ≤ 27·7^{L_r}`: writing
`S = Σ_{r=1}^{m} L_r ≤ (n-3m)₊`, the double-shift-free count satisfies
`card · 2^S ≤ 27^{m₊} · 7^{(n-3m)₊}` — i.e. per triple-column the rate
`7/2` (per vertex `(7/2)^{1/3} ≈ 1.518`) with slack `27^{m₊}`. -/
theorem card_powerset_filter_shiftFree2_triIcc_mul_le {n : ℕ} {m : ℤ}
    (hm : 1 ≤ m) :
    ((Finset.Icc (3 * m + 1) (n : ℤ)).powerset.filter
        (shiftFree2 m (3 * m))).card *
        2 ^ (∑ r ∈ Finset.Icc 1 m, (((n : ℤ) - r) / (3 * m)).toNat) ≤
      27 ^ m.toNat * 7 ^ ((n : ℤ) - 3 * m).toNat := by
  have hcard : (Finset.Icc 1 m).card = m.toNat := by
    rw [Int.card_Icc]
    congr 1
    omega
  have hprod := card_powerset_filter_shiftFree2_triIcc_le (n := n) hm
  have hstep :
      (∏ r ∈ Finset.Icc 1 m, (wSets (((n : ℤ) - r) / (3 * m)).toNat).card) *
          2 ^ (∑ r ∈ Finset.Icc 1 m, (((n : ℤ) - r) / (3 * m)).toNat) ≤
        27 ^ m.toNat * 7 ^ ((n : ℤ) - 3 * m).toNat := by
    calc (∏ r ∈ Finset.Icc 1 m,
            (wSets (((n : ℤ) - r) / (3 * m)).toNat).card) *
          2 ^ (∑ r ∈ Finset.Icc 1 m, (((n : ℤ) - r) / (3 * m)).toNat)
        = ∏ r ∈ Finset.Icc 1 m,
            ((wSets (((n : ℤ) - r) / (3 * m)).toNat).card *
              2 ^ (((n : ℤ) - r) / (3 * m)).toNat) := by
          rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
      _ ≤ ∏ r ∈ Finset.Icc 1 m,
            27 * 7 ^ (((n : ℤ) - r) / (3 * m)).toNat :=
          Finset.prod_le_prod fun r _ => wSets_card_mul_two_pow_le _
      _ = 27 ^ m.toNat *
            7 ^ (∑ r ∈ Finset.Icc 1 m, (((n : ℤ) - r) / (3 * m)).toNat) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, hcard,
            Finset.prod_pow_eq_pow_sum]
      _ ≤ 27 ^ m.toNat * 7 ^ ((n : ℤ) - 3 * m).toNat :=
          Nat.mul_le_mul (le_refl _)
            (pow_le_pow_right₀ (by norm_num) (sum_triCls_len_le hm))
  exact (Nat.mul_le_mul hprod (le_refl _)).trans hstep

end JSP000728
