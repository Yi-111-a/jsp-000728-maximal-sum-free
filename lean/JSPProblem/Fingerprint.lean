import JSPProblem.Extremal
import JSPProblem.ContainerReduction

/-!
# JSP-000728 — per-container counting of maximal sum-free sets

The BLST18 fingerprint bound counts, for each container `C`, how many
inclusion-maximal sum-free subsets of `{1,…,n}` the container houses.  This
file develops that per-container vocabulary:

* `IsMaxSumFreeIn C s` — `s` is inclusion-maximal among the sum-free subsets
  of the container `C` (decidable, single-obstruction formulation mirroring
  `IsMaxSumFree`).
* `maxSumFreeSetsIn n C` — the finset of all such `s`; membership is
  characterised by `mem_maxSumFreeSetsIn`.
* `isMaxSumFreeIn_of_isMaxSumFree_subset` — a maximal sum-free `M ⊆ C` with
  `C ⊆ interval n` is automatically maximal *inside* `C`, since every
  `x ∈ C` lies in `interval n` and is obstructed.
* `card_maxSumFreeSets_filter_le` and `card_maxSumFreeSetsIn_le` — the two
  per-container counts compare, and each is at most `2 ^ C.card`.
* Canonical containers: `maxSumFreeSetsIn n (odds n) = {odds n}` and
  `maxSumFreeSetsIn n (upperHalf n) = {upperHalf n}` — each canonical
  container houses exactly one maximal sum-free set — so at most two maximal
  sum-free sets are covered by the two canonical containers together.
* `maxSumFreeCount_le_sum_card_in` — a cover of the maximal sum-free sets by
  containers `C ⊆ interval n` gives
  `f(n) ≤ ∑_{C ∈ F} (maxSumFreeSetsIn n C).card`, the per-container
  decomposition into which the fingerprint bound feeds.  The variant
  `maxSumFreeCount_le_sum_card_in_inter` drops the `C ⊆ interval n`
  hypothesis at the price of intersecting each container with the interval.
* `inter_union_inter_sdiff_eq_self` — the fingerprint reconstruction
  identity: `M ⊆ C` is recovered from its trace `M ∩ B` on a fingerprint set
  `B` and its trace `M ∩ (C \ B)` off it.
-/

namespace JSP000728

/-! ## Maximality relative to a container -/

/-- `s` is an *inclusion-maximal sum-free subset of the container `C`*:
it is contained in `C`, sum-free, and adjoining any further element of `C`
destroys sum-freeness.  This is `IsMaxSumFree` with `interval n` replaced by
an arbitrary container `C`. -/
def IsMaxSumFreeIn (C s : Finset ℤ) : Prop :=
  s ⊆ C ∧ IsSumFree s ∧ ∀ x ∈ C, x ∉ s → ¬ IsSumFree (insert x s)

instance decidableIsMaxSumFreeIn (C s : Finset ℤ) :
    Decidable (IsMaxSumFreeIn C s) := by
  unfold IsMaxSumFreeIn; infer_instance

/-- The finset of all inclusion-maximal sum-free subsets of the container
`C`.  (The parameter `n` only fixes the ambient problem instance; the set
itself depends solely on `C`.) -/
def maxSumFreeSetsIn (_n : ℕ) (C : Finset ℤ) : Finset (Finset ℤ) :=
  C.powerset.filter (IsMaxSumFreeIn C)

theorem mem_maxSumFreeSetsIn {n : ℕ} {C s : Finset ℤ} :
    s ∈ maxSumFreeSetsIn n C ↔ s ⊆ C ∧ IsMaxSumFreeIn C s := by
  simp only [maxSumFreeSetsIn, Finset.mem_filter, Finset.mem_powerset]

/-- A maximal sum-free `M ⊆ {1,…,n}` contained in a container
`C ⊆ {1,…,n}` is maximal inside `C`: every `x ∈ C ∖ M` lies in `interval n`,
so the obstruction provided by `IsMaxSumFree` applies verbatim. -/
theorem isMaxSumFreeIn_of_isMaxSumFree_subset {n : ℕ} {M C : Finset ℤ}
    (hM : IsMaxSumFree n M) (hMC : M ⊆ C) (hC : C ⊆ interval n) :
    IsMaxSumFreeIn C M :=
  ⟨hMC, hM.2.1, fun x hxC hxM => hM.2.2 x (hC hxC) hxM⟩

/-! ## Per-container counts -/

/-- Every maximal sum-free subset of `{1,…,n}` housed by `C ⊆ interval n`
is maximal inside `C`. -/
theorem maxSumFreeSets_filter_subset_le {n : ℕ} {C : Finset ℤ}
    (hC : C ⊆ interval n) :
    (maxSumFreeSets n).filter (· ⊆ C) ⊆ maxSumFreeSetsIn n C := by
  intro M hM
  rw [Finset.mem_filter] at hM
  obtain ⟨hMmax, hMC⟩ := hM
  exact mem_maxSumFreeSetsIn.mpr
    ⟨hMC, isMaxSumFreeIn_of_isMaxSumFree_subset
      (mem_maxSumFreeSets.mp hMmax) hMC hC⟩

/-- Count form of `maxSumFreeSets_filter_subset_le`. -/
theorem card_maxSumFreeSets_filter_le {n : ℕ} {C : Finset ℤ}
    (hC : C ⊆ interval n) :
    ((maxSumFreeSets n).filter (· ⊆ C)).card ≤ (maxSumFreeSetsIn n C).card :=
  Finset.card_le_card (maxSumFreeSets_filter_subset_le hC)

/-- A container houses at most `2 ^ |C|` maximal-in-`C` sum-free sets. -/
theorem card_maxSumFreeSetsIn_le {n : ℕ} {C : Finset ℤ} :
    (maxSumFreeSetsIn n C).card ≤ 2 ^ C.card := by
  calc (maxSumFreeSetsIn n C).card
      ≤ C.powerset.card := Finset.card_filter_le _ _
    _ = 2 ^ C.card := Finset.card_powerset _

/-! ## The canonical containers house exactly one maximal sum-free set -/

/-- The only maximal sum-free subset of `{1,…,n}` contained in `odds n` is
`odds n` itself. -/
theorem maxSumFreeSets_filter_odds (n : ℕ) :
    (maxSumFreeSets n).filter (· ⊆ odds n) = {odds n} := by
  ext M
  simp only [Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨hM, hsub⟩
    exact eq_odds_of_isMaxSumFree_subset (mem_maxSumFreeSets.mp hM) hsub
  · rintro rfl
    exact ⟨mem_maxSumFreeSets.mpr (odds_isMaxSumFree n), Finset.Subset.refl _⟩

/-- The only maximal sum-free subset of `{1,…,n}` contained in
`upperHalf n` is `upperHalf n` itself. -/
theorem maxSumFreeSets_filter_upperHalf (n : ℕ) :
    (maxSumFreeSets n).filter (· ⊆ upperHalf n) = {upperHalf n} := by
  ext M
  simp only [Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨hM, hsub⟩
    exact eq_upperHalf_of_isMaxSumFree_subset (mem_maxSumFreeSets.mp hM) hsub
  · rintro rfl
    exact ⟨mem_maxSumFreeSets.mpr (upperHalf_isMaxSumFree n),
      Finset.Subset.refl _⟩

theorem card_maxSumFreeSets_filter_odds (n : ℕ) :
    ((maxSumFreeSets n).filter (· ⊆ odds n)).card = 1 := by
  rw [maxSumFreeSets_filter_odds, Finset.card_singleton]

theorem card_maxSumFreeSets_filter_upperHalf (n : ℕ) :
    ((maxSumFreeSets n).filter (· ⊆ upperHalf n)).card = 1 := by
  rw [maxSumFreeSets_filter_upperHalf, Finset.card_singleton]

/-- `odds n`, viewed as a container, houses exactly itself as
maximal-in-container sum-free set: any sum-free `s ⊆ odds n` missing an odd
`x` could absorb it (odds sum to evens). -/
theorem maxSumFreeSetsIn_odds (n : ℕ) :
    maxSumFreeSetsIn n (odds n) = {odds n} := by
  ext s
  rw [mem_maxSumFreeSetsIn, Finset.mem_singleton]
  constructor
  · rintro ⟨hsub, -, hsf, hmax⟩
    refine subset_antisymm hsub fun x hx => ?_
    by_contra hxs
    exact hmax x hx hxs (isSumFree_insert_odd hsf hsub (mem_odds.mp hx).2)
  · rintro rfl
    have h := isMaxSumFreeIn_of_isMaxSumFree_subset (odds_isMaxSumFree n)
      (Finset.Subset.refl _) (fun x hx => (mem_odds.mp hx).1)
    exact ⟨h.1, h⟩

/-- `upperHalf n`, viewed as a container, houses exactly itself. -/
theorem maxSumFreeSetsIn_upperHalf (n : ℕ) :
    maxSumFreeSetsIn n (upperHalf n) = {upperHalf n} := by
  ext s
  rw [mem_maxSumFreeSetsIn, Finset.mem_singleton]
  constructor
  · rintro ⟨hsub, -, hsf, hmax⟩
    refine subset_antisymm hsub fun x hx => ?_
    by_contra hxs
    have hxu := mem_upperHalf.mp hx
    exact hmax x hx hxs
      (isSumFree_insert_upperHalf hsf hsub hxu.1 hxu.2)
  · rintro rfl
    have h := isMaxSumFreeIn_of_isMaxSumFree_subset
      (upperHalf_isMaxSumFree n) (Finset.Subset.refl _)
      (fun x hx => (mem_upperHalf.mp hx).1)
    exact ⟨h.1, h⟩

theorem card_maxSumFreeSetsIn_odds (n : ℕ) :
    (maxSumFreeSetsIn n (odds n)).card = 1 := by
  rw [maxSumFreeSetsIn_odds, Finset.card_singleton]

theorem card_maxSumFreeSetsIn_upperHalf (n : ℕ) :
    (maxSumFreeSetsIn n (upperHalf n)).card = 1 := by
  rw [maxSumFreeSetsIn_upperHalf, Finset.card_singleton]

/-- The two canonical containers together cover at most two maximal sum-free
subsets of `{1,…,n}` — namely `odds n` and `upperHalf n` themselves. -/
theorem card_maxSumFreeSets_filter_odds_or_upperHalf_le (n : ℕ) :
    ((maxSumFreeSets n).filter
      fun M => M ⊆ odds n ∨ M ⊆ upperHalf n).card ≤ 2 := by
  have hsub : (maxSumFreeSets n).filter
        (fun M => M ⊆ odds n ∨ M ⊆ upperHalf n)
      ⊆ {odds n, upperHalf n} := by
    intro M hM
    rw [Finset.mem_filter] at hM
    obtain ⟨hMmax, hsub⟩ := hM
    rw [Finset.mem_insert, Finset.mem_singleton]
    rcases hsub with h | h
    · exact Or.inl
        (eq_odds_of_isMaxSumFree_subset (mem_maxSumFreeSets.mp hMmax) h)
    · exact Or.inr
        (eq_upperHalf_of_isMaxSumFree_subset (mem_maxSumFreeSets.mp hMmax) h)
  calc ((maxSumFreeSets n).filter
        fun M => M ⊆ odds n ∨ M ⊆ upperHalf n).card
      ≤ ({odds n, upperHalf n} : Finset (Finset ℤ)).card :=
        Finset.card_le_card hsub
    _ ≤ 2 := by
        have h := Finset.card_insert_le (odds n)
          ({upperHalf n} : Finset (Finset ℤ))
        rw [Finset.card_singleton] at h
        exact h

/-! ## Cover decomposition: the per-container counting hook -/

/-- **Per-container decomposition.**  If the containers `C ∈ F` all lie
inside `{1,…,n}` and cover every maximal sum-free set, then the number of
maximal sum-free sets is at most the sum over `C ∈ F` of the number of
maximal-in-`C` sum-free sets.  This is the hook the BLST18 fingerprint bound
plugs into: each factor `(maxSumFreeSetsIn n C).card` is bounded by the
fingerprint analysis. -/
theorem maxSumFreeCount_le_sum_card_in {n : ℕ} {F : Finset (Finset ℤ)}
    (hF : ∀ C ∈ F, C ⊆ interval n)
    (hcov : ∀ M ∈ maxSumFreeSets n, ∃ C ∈ F, M ⊆ C) :
    maxSumFreeCount n ≤ ∑ C ∈ F, (maxSumFreeSetsIn n C).card := by
  classical
  have hsub : maxSumFreeSets n ⊆
      F.biUnion fun C => maxSumFreeSetsIn n C := by
    intro M hM
    obtain ⟨C, hCF, hMC⟩ := hcov M hM
    rw [Finset.mem_biUnion]
    exact ⟨C, hCF, mem_maxSumFreeSetsIn.mpr
      ⟨hMC, isMaxSumFreeIn_of_isMaxSumFree_subset
        (mem_maxSumFreeSets.mp hM) hMC (hF C hCF)⟩⟩
  calc maxSumFreeCount n
      = (maxSumFreeSets n).card := rfl
    _ ≤ (F.biUnion fun C => maxSumFreeSetsIn n C).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ C ∈ F, (maxSumFreeSetsIn n C).card := Finset.card_biUnion_le

/-- Variant of `maxSumFreeCount_le_sum_card_in` for arbitrary covering
families: each container `C` is first trimmed to `C ∩ interval n`, which
still covers `M` since `M ⊆ interval n`. -/
theorem maxSumFreeCount_le_sum_card_in_inter {n : ℕ} {F : Finset (Finset ℤ)}
    (hcov : ∀ M ∈ maxSumFreeSets n, ∃ C ∈ F, M ⊆ C) :
    maxSumFreeCount n ≤
      ∑ C ∈ F, (maxSumFreeSetsIn n (C ∩ interval n)).card := by
  classical
  have hsub : maxSumFreeSets n ⊆
      F.biUnion fun C => maxSumFreeSetsIn n (C ∩ interval n) := by
    intro M hM
    obtain ⟨C, hCF, hMC⟩ := hcov M hM
    rw [Finset.mem_biUnion]
    refine ⟨C, hCF, ?_⟩
    have hMI : M ⊆ interval n := (mem_maxSumFreeSets.mp hM).1
    have hMCI : M ⊆ C ∩ interval n := Finset.subset_inter hMC hMI
    exact mem_maxSumFreeSetsIn.mpr
      ⟨hMCI, isMaxSumFreeIn_of_isMaxSumFree_subset
        (mem_maxSumFreeSets.mp hM) hMCI Finset.inter_subset_right⟩
  calc maxSumFreeCount n
      = (maxSumFreeSets n).card := rfl
    _ ≤ (F.biUnion fun C => maxSumFreeSetsIn n (C ∩ interval n)).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ C ∈ F, (maxSumFreeSetsIn n (C ∩ interval n)).card :=
        Finset.card_biUnion_le

/-! ## Fingerprint reconstruction -/

/-- **Fingerprint decomposition.**  For `M ⊆ C` and any fingerprint set `B`,
`M` splits as the disjoint union of its *fingerprint* `M ∩ B` and its trace
`M ∩ (C \ B)` off the fingerprint.  In the BLST18 argument `B ⊆ C` is small
and `M ∩ B` determines `M`, so counting pairs `(M ∩ B, M ∩ (C \ B))` bounds
`(maxSumFreeSetsIn n C).card`. -/
theorem inter_union_inter_sdiff_eq_self {M B C : Finset ℤ} (hMC : M ⊆ C) :
    M ∩ B ∪ M ∩ (C \ B) = M := by
  ext x
  simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
  constructor
  · rintro (⟨hxM, -⟩ | ⟨hxM, -, -⟩) <;> exact hxM
  · intro hxM
    by_cases hxB : x ∈ B
    · exact Or.inl ⟨hxM, hxB⟩
    · exact Or.inr ⟨hxM, hMC hxM, hxB⟩

end JSP000728
