import JSPProblem.Extremal
import JSPProblem.MinElement
import Mathlib.Data.Finset.Max
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# JSP-000728 — decomposition of maximal sum-free sets by their minimum

Every nonempty inclusion-maximal sum-free subset `M ⊆ {1,…,n}` has a
minimum `m = min M`.  Grouping the maximal sum-free sets by this minimum
gives the disjoint-union decomposition

  `maxSumFreeSets n = ⋃ m ∈ {1,…,n}, minClass n m`,

the first step of the Balogh–Liu–Sharifzadeh–Treglown structural case
analysis:

* classes with **small** minimum are bounded by
  `|minClass n m| ≤ 2 ^ (n + 1 − m)` (`minClass_card_le_two_pow`), since
  every member is a subset of `Icc m n`;
* classes with **large** minimum (`2m > n`) are *subsingletons*, because
  `M ⊆ Icc m n ⊆ upperHalf n` forces `M = upperHalf n`
  (`minClass_card_le_one_of_large`).

Combining the two gives `maxSumFreeCount_le_sum_minClass_bound`.  We also
record the translate-by-the-minimum constraint (`x, m ∈ M ⟹ x + m ∉ M`)
used later by the Fibonacci path bound.
-/

namespace JSP000728

/-- A maximal sum-free subset of `{1,…,n}` with `n ≥ 1` is nonempty: `∅` is
sum-free but not maximal, since `insert 1 ∅ = {1}` is still sum-free
(`1 + 1 = 2 ∉ {1}`). -/
theorem nonempty_of_mem_maxSumFreeSets {n : ℕ} (hn : 1 ≤ n) {M : Finset ℤ}
    (hM : M ∈ maxSumFreeSets n) : M.Nonempty := by
  rcases M.eq_empty_or_nonempty with rfl | hne
  · obtain ⟨-, -, hmax⟩ := mem_maxSumFreeSets.mp hM
    have h1 : (1 : ℤ) ∈ interval n :=
      Finset.mem_Icc.mpr ⟨le_refl 1, by exact_mod_cast hn⟩
    have hsf1 : IsSumFree (insert (1 : ℤ) ∅) := by
      intro x hx y hy hxy
      simp only [Finset.mem_insert, Finset.notMem_empty, or_false] at hx hy hxy
      subst hx; subst hy; omega
    exact (hmax 1 h1 (Finset.notMem_empty 1) hsf1).elim
  · exact hne

/-- The class of maximal sum-free subsets of `{1,…,n}` whose minimum is
exactly `m`: maximal sum-free `M` with `m ∈ M` and `m ≤ x` for all
`x ∈ M`. -/
def minClass (n : ℕ) (m : ℤ) : Finset (Finset ℤ) :=
  (maxSumFreeSets n).filter fun M => m ∈ M ∧ ∀ x ∈ M, m ≤ x

theorem mem_minClass {n : ℕ} {M : Finset ℤ} {m : ℤ} :
    M ∈ minClass n m ↔ M ∈ maxSumFreeSets n ∧ m ∈ M ∧ ∀ x ∈ M, m ≤ x :=
  Finset.mem_filter

/-- **Minimum decomposition.**  Every nonempty maximal sum-free `M` has a
minimum `M.min' ∈ M ⊆ {1,…,n}`, so `maxSumFreeSets n` is the union of the
classes `minClass n m` over `m ∈ {1,…,n}`. -/
theorem maxSumFreeSets_eq_biUnion_minClass {n : ℕ} (hn : 1 ≤ n) :
    maxSumFreeSets n = (Finset.Icc 1 (n : ℤ)).biUnion (minClass n) := by
  ext M
  simp only [Finset.mem_biUnion, mem_minClass]
  constructor
  · intro hM
    have hne := nonempty_of_mem_maxSumFreeSets hn hM
    have hsub := (mem_maxSumFreeSets.mp hM).1
    exact ⟨M.min' hne, hsub (Finset.min'_mem M hne), hM,
      Finset.min'_mem M hne, fun x hx => Finset.min'_le M x hx⟩
  · rintro ⟨m, -, hM, -, -⟩
    exact hM

/-- The classes `minClass n m` for distinct `m` are disjoint: a set `M`
cannot have two different minima. -/
theorem disjoint_minClass {n : ℕ} :
    (Finset.Icc 1 (n : ℤ) : Set ℤ).PairwiseDisjoint (minClass n) := by
  intro a _ b _ hab
  show Disjoint (minClass n a) (minClass n b)
  rw [Finset.disjoint_left]
  rintro M hMa hMb
  rw [mem_minClass] at hMa hMb
  exact hab (le_antisymm (hMa.2.2 b hMb.2.1) (hMb.2.2 a hMa.2.1))

/-- `f n` is the sum over `m ∈ {1,…,n}` of the size of the class with
minimum `m`. -/
theorem maxSumFreeCount_eq_sum_minClass {n : ℕ} (hn : 1 ≤ n) :
    maxSumFreeCount n = ∑ m ∈ Finset.Icc 1 (n : ℤ), (minClass n m).card := by
  unfold maxSumFreeCount
  rw [maxSumFreeSets_eq_biUnion_minClass hn,
    Finset.card_biUnion disjoint_minClass]

/-- Every member of `minClass n m` is a subset of `Icc m n`. -/
theorem minClass_subset_powerset_Icc (n : ℕ) (m : ℤ) :
    minClass n m ⊆ (Finset.Icc m (n : ℤ)).powerset := by
  intro M hM
  rw [mem_minClass] at hM
  obtain ⟨hmax, -, hmin⟩ := hM
  rw [Finset.mem_powerset]
  intro x hx
  rw [Finset.mem_Icc]
  exact ⟨hmin x hx, (Finset.mem_Icc.mp ((mem_maxSumFreeSets.mp hmax).1 hx)).2⟩

/-- The class with minimum `m` injects into the powerset of `Icc m n`, so
it has at most `2 ^ #(Icc m n)` elements. -/
theorem minClass_card_le (n : ℕ) (m : ℤ) :
    (minClass n m).card ≤ 2 ^ (Finset.Icc m (n : ℤ)).card :=
  calc (minClass n m).card
      ≤ ((Finset.Icc m (n : ℤ)).powerset).card :=
        Finset.card_le_card (minClass_subset_powerset_Icc n m)
    _ = 2 ^ (Finset.Icc m (n : ℤ)).card := Finset.card_powerset _

/-- Numeric form: `|minClass n m| ≤ 2 ^ (n + 1 − m)`. -/
theorem minClass_card_le_two_pow (n : ℕ) (m : ℤ) :
    (minClass n m).card ≤ 2 ^ ((n : ℤ) + 1 - m).toNat := by
  rw [← Int.card_Icc]
  exact minClass_card_le n m

/-- **Large-minimum collapse.**  If `2m > n` then every member `M` of the
class lies in `Icc m n ⊆ upperHalf n`, hence equals `upperHalf n` by
`eq_upperHalf_of_isMaxSumFree_subset`; so the class is a subsingleton. -/
theorem minClass_card_le_one_of_large {n : ℕ} {m : ℤ} (hm : (n : ℤ) < 2 * m) :
    (minClass n m).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro M hM M' hM'
  rw [mem_minClass] at hM hM'
  have hsub : ∀ ⦃N : Finset ℤ⦄, N ∈ maxSumFreeSets n →
      (∀ x ∈ N, m ≤ x) → N ⊆ upperHalf n := by
    intro N hN hle x hx
    rw [mem_upperHalf]
    exact ⟨(mem_maxSumFreeSets.mp hN).1 hx, by have := hle x hx; omega⟩
  rw [eq_upperHalf_of_isMaxSumFree_subset (mem_maxSumFreeSets.mp hM.1)
        (hsub hM.1 hM.2.2),
      eq_upperHalf_of_isMaxSumFree_subset (mem_maxSumFreeSets.mp hM'.1)
        (hsub hM'.1 hM'.2.2)]

/-- **BLST decomposition bound.**  Splitting the minimum classes into the
large-minimum ones (`2m > n`, each a subsingleton) and the small-minimum
ones (each at most `2 ^ (n + 1 − m)`) gives

  `f n ≤ #{m ∈ [1,n] : 2m > n} + ∑_{m ∈ [1,n], 2m ≤ n} 2 ^ (n + 1 − m)`. -/
theorem maxSumFreeCount_le_sum_minClass_bound {n : ℕ} (hn : 1 ≤ n) :
    maxSumFreeCount n ≤
      ((Finset.Icc 1 (n : ℤ)).filter fun m => (n : ℤ) < 2 * m).card +
        ∑ m ∈ (Finset.Icc 1 (n : ℤ)).filter (fun m => ¬ (n : ℤ) < 2 * m),
          2 ^ ((n : ℤ) + 1 - m).toNat := by
  rw [maxSumFreeCount_eq_sum_minClass hn,
    ← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 (n : ℤ))
      (fun m => (n : ℤ) < 2 * m) (fun m => (minClass n m).card)]
  refine add_le_add ?_ (Finset.sum_le_sum fun m _ => minClass_card_le_two_pow n m)
  calc ∑ m ∈ (Finset.Icc 1 (n : ℤ)).filter (fun m => (n : ℤ) < 2 * m),
          (minClass n m).card
      ≤ ∑ m ∈ (Finset.Icc 1 (n : ℤ)).filter (fun m => (n : ℤ) < 2 * m), 1 :=
        Finset.sum_le_sum fun m hm =>
          minClass_card_le_one_of_large (Finset.mem_filter.mp hm).2
    _ = ((Finset.Icc 1 (n : ℤ)).filter fun m => (n : ℤ) < 2 * m).card := by
        simp

/-- Coarse global bound: `maxSumFreeSets n ⊆ (interval n).powerset`, so
`f n ≤ 2 ^ n`. -/
theorem maxSumFreeCount_le_two_pow (n : ℕ) : maxSumFreeCount n ≤ 2 ^ n := by
  unfold maxSumFreeCount maxSumFreeSets
  calc ((interval n).powerset.filter (IsMaxSumFree n)).card
      ≤ ((interval n).powerset).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
    _ = 2 ^ n := by
        rw [Finset.card_powerset]
        congr 1
        simp [interval, Int.card_Icc]

/-- A Schur triple cannot live inside a maximal sum-free set: `x, m ∈ M`
forces `x + m ∉ M`.  This is the translate constraint behind the
Fibonacci path bound in the BLST analysis. -/
theorem not_mem_add_min_of_isMaxSumFree {n : ℕ} {M : Finset ℤ}
    (hM : IsMaxSumFree n M) {m x : ℤ} (hm : m ∈ M) (hx : x ∈ M) :
    x + m ∉ M :=
  hM.2.1 x hx m hm

/-- **Translate-by-`m` corollary.**  For `m ∈ M` maximal sum-free, the
translate by `m` of the low part `M ∩ (-∞, n−m]` lands inside
`{1,…,n} \ M`: it stays in `{1,…,n}` and is disjoint from `M` by
`disjoint_image_add_min_of_isSumFree`. -/
theorem image_add_min_subset_sdiff {n : ℕ} {M : Finset ℤ}
    (hM : IsMaxSumFree n M) {m : ℤ} (hm : m ∈ M) :
    (M.filter fun x => x ≤ (n : ℤ) - m).image (· + m) ⊆ interval n \ M := by
  intro y hy
  rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
  obtain ⟨hxM, hxle⟩ := Finset.mem_filter.mp hx
  have hxI := Finset.mem_Icc.mp (hM.1 hxM)
  have hmI := Finset.mem_Icc.mp (hM.1 hm)
  rw [Finset.mem_sdiff]
  refine ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
  have hdisj := disjoint_image_add_min_of_isSumFree hM.2.1 hm
  rw [Finset.disjoint_left] at hdisj
  exact fun hmem => hdisj hmem (Finset.mem_image.mpr ⟨x, hxM, rfl⟩)

/-- The translate `x ↦ x + m` is injective, so the low part and its
translate have the same cardinality. -/
theorem card_image_add_min (M : Finset ℤ) (m : ℤ) :
    (M.image (· + m)).card = M.card :=
  Finset.card_image_of_injective M (add_left_injective m)

/-- Consequently `|M| + |M ∩ (-∞, n−m]| ≤ n`: `M` and the translate of its
low part are disjoint subsets of `{1,…,n}`. -/
theorem card_add_card_low_le {n : ℕ} {M : Finset ℤ} (hM : IsMaxSumFree n M)
    {m : ℤ} (hm : m ∈ M) :
    M.card + (M.filter fun x => x ≤ (n : ℤ) - m).card ≤ n := by
  have hdisj : Disjoint M ((M.filter fun x => x ≤ (n : ℤ) - m).image (· + m)) :=
    (disjoint_image_add_min_of_isSumFree hM.2.1 hm).mono_right
      (Finset.image_subset_image (Finset.filter_subset _ _))
  have hunion : M ∪ (M.filter fun x => x ≤ (n : ℤ) - m).image (· + m) ⊆
      interval n :=
    Finset.union_subset hM.1
      ((image_add_min_subset_sdiff hM hm).trans Finset.sdiff_subset)
  calc M.card + (M.filter fun x => x ≤ (n : ℤ) - m).card
      = M.card + ((M.filter fun x => x ≤ (n : ℤ) - m).image (· + m)).card := by
        rw [card_image_add_min]
    _ = (M ∪ (M.filter fun x => x ≤ (n : ℤ) - m).image (· + m)).card :=
        (Finset.card_union_of_disjoint hdisj).symm
    _ ≤ (interval n).card := Finset.card_le_card hunion
    _ = n := by simp [interval, Int.card_Icc]

/-- The translate corollary specialised to the actual minimum `M.min'`. -/
theorem image_add_min'_subset_sdiff {n : ℕ} {M : Finset ℤ}
    (hM : M ∈ maxSumFreeSets n) (hne : M.Nonempty) :
    (M.filter fun x => x ≤ (n : ℤ) - M.min' hne).image (· + M.min' hne) ⊆
      interval n \ M :=
  image_add_min_subset_sdiff (mem_maxSumFreeSets.mp hM) (Finset.min'_mem M hne)

end JSP000728
