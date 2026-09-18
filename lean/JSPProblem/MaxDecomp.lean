import JSPProblem.MinDecomp
import JSPProblem.MaxCard
import JSPProblem.Obstruction
import JSPProblem.UpperHalf
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

/-!
# JSP-000728 — decomposition of maximal sum-free sets by their maximum

Dual to `JSPProblem.MinDecomp`: group the inclusion-maximal sum-free
subsets of `{1,…,n}` by their *maximum* element `t = max M`.

* `maxClass n t` — the class of maximal sum-free `M` with `max M = t`;
  `maxSumFreeSets_eq_biUnion_maxClass` is the disjoint-union decomposition
  and `maxSumFreeCount_eq_sum_maxClass` its counting form.
* `isMaxSumFree_toNat_of_mem_maxClass` — **restriction**: such an `M`
  stays maximal sum-free inside `{1,…,t}` (every obstruction is `≤ t`).
* `ioc_subset_image_sum_of_mem_maxClass` — the **covering lemma**: every
  `y ∈ (t, n]` is a sum of two elements of `M`.  The obstruction to
  adjoining `y` cannot be `a + y ∈ M` or `y + y ∈ M` (both exceed `t`),
  so it must be `y = a + b` with `a, b ∈ M`.
* Cardinality corollaries: `n - t ≤ |M|²` (`sub_le_card_sq_of_mem_maxClass`)
  and `2|M| ≤ t + 1` (`two_mul_card_le_of_mem_maxClass`), combining into
  `4n ≤ (t + 3)²` (`four_mul_le_sq_add_three_of_mem_maxClass`), i.e.
  `max M ≥ 2√n − 3`.  In particular `maxClass n t` is empty whenever
  `(t + 1)² < 4(n - t)` (`maxClass_eq_empty_of_sq_lt`).
-/

namespace JSP000728

/-- Every subset of the upper half is sum-free: `x, y > n/2` forces
`x + y > n`, so no sum of two members can lie in `interval n ⊇ s`. -/
theorem isSumFree_of_subset_upperHalf {n : ℕ} {s : Finset ℤ}
    (hs : s ⊆ upperHalf n) : IsSumFree s := by
  intro x hx y hy hxy
  have hx2 := (mem_upperHalf.mp (hs hx)).2
  have hy2 := (mem_upperHalf.mp (hs hy)).2
  have hle : x + y ≤ (n : ℤ) :=
    (Finset.mem_Icc.mp (mem_upperHalf.mp (hs hxy)).1).2
  omega

/-- The upper half contributes the full `2 ^ |upperHalf n|` sum-free
subsets. -/
theorem card_powerset_upperHalf (n : ℕ) :
    (upperHalf n).powerset.card = 2 ^ (upperHalf n).card :=
  Finset.card_powerset _

/-- The class of maximal sum-free subsets of `{1,…,n}` whose *maximum* is
exactly `t`: maximal sum-free `M` with `t ∈ M` and `x ≤ t` for all
`x ∈ M`. -/
def maxClass (n : ℕ) (t : ℤ) : Finset (Finset ℤ) :=
  (maxSumFreeSets n).filter fun M => t ∈ M ∧ ∀ x ∈ M, x ≤ t

theorem mem_maxClass {n : ℕ} {M : Finset ℤ} {t : ℤ} :
    M ∈ maxClass n t ↔ M ∈ maxSumFreeSets n ∧ t ∈ M ∧ ∀ x ∈ M, x ≤ t :=
  Finset.mem_filter

/-- **Maximum decomposition.**  Every nonempty maximal sum-free `M` has a
maximum `M.max' ∈ M ⊆ {1,…,n}`, so `maxSumFreeSets n` is the union of the
classes `maxClass n t` over `t ∈ {1,…,n}`. -/
theorem maxSumFreeSets_eq_biUnion_maxClass {n : ℕ} (hn : 1 ≤ n) :
    maxSumFreeSets n = (Finset.Icc 1 (n : ℤ)).biUnion (maxClass n) := by
  ext M
  simp only [Finset.mem_biUnion, mem_maxClass]
  constructor
  · intro hM
    have hne := nonempty_of_mem_maxSumFreeSets hn hM
    have hsub := (mem_maxSumFreeSets.mp hM).1
    exact ⟨M.max' hne, hsub (Finset.max'_mem M hne), hM,
      Finset.max'_mem M hne, fun x hx => Finset.le_max' M x hx⟩
  · rintro ⟨t, -, hM, -, -⟩
    exact hM

/-- The classes `maxClass n t` for distinct `t` are disjoint: a set `M`
cannot have two different maxima. -/
theorem disjoint_maxClass {n : ℕ} :
    (Finset.Icc 1 (n : ℤ) : Set ℤ).PairwiseDisjoint (maxClass n) := by
  intro a _ b _ hab
  show Disjoint (maxClass n a) (maxClass n b)
  rw [Finset.disjoint_left]
  rintro M hMa hMb
  rw [mem_maxClass] at hMa hMb
  exact hab (le_antisymm (hMb.2.2 a hMa.2.1) (hMa.2.2 b hMb.2.1))

/-- `f n` is the sum over `t ∈ {1,…,n}` of the size of the class with
maximum `t`. -/
theorem maxSumFreeCount_eq_sum_maxClass {n : ℕ} (hn : 1 ≤ n) :
    maxSumFreeCount n = ∑ t ∈ Finset.Icc 1 (n : ℤ), (maxClass n t).card := by
  unfold maxSumFreeCount
  rw [maxSumFreeSets_eq_biUnion_maxClass hn,
    Finset.card_biUnion disjoint_maxClass]

/-- Every member of `maxClass n t` is a subset of `Icc 1 t`. -/
theorem maxClass_subset_powerset_Icc (n : ℕ) (t : ℤ) :
    maxClass n t ⊆ (Finset.Icc 1 t).powerset := by
  intro M hM
  obtain ⟨hmax, -, hle⟩ := mem_maxClass.mp hM
  rw [Finset.mem_powerset]
  intro x hx
  rw [Finset.mem_Icc]
  exact ⟨interval_one_le ((mem_maxSumFreeSets.mp hmax).1 hx), hle x hx⟩

/-- The class with maximum `t` injects into the powerset of `Icc 1 t`, so
it has at most `2 ^ t` elements. -/
theorem maxClass_card_le (n : ℕ) (t : ℤ) :
    (maxClass n t).card ≤ 2 ^ (Finset.Icc (1 : ℤ) t).card :=
  (Finset.card_le_card (maxClass_subset_powerset_Icc n t)).trans_eq
    (Finset.card_powerset _)

/-- Numeric form: `|maxClass n t| ≤ 2 ^ t.toNat`. -/
theorem maxClass_card_le_two_pow (n : ℕ) (t : ℤ) :
    (maxClass n t).card ≤ 2 ^ t.toNat := by
  have h := maxClass_card_le n t
  rw [Int.card_Icc, show t + 1 - 1 = t from by omega] at h
  exact h

/-- **Restriction lemma.**  A maximal sum-free `M ⊆ {1,…,n}` with maximum
`t` is still maximal sum-free inside `{1,…,t}`: `M ⊆ {1,…,t}`, and any
`x ∈ {1,…,t} \ M` also lies in `{1,…,n} \ M`, so the same obstruction
destroys sum-freeness of `insert x M`. -/
theorem isMaxSumFree_toNat_of_mem_maxClass {n : ℕ} {M : Finset ℤ} {t : ℤ}
    (hM : M ∈ maxClass n t) : IsMaxSumFree t.toNat M := by
  obtain ⟨hmax, htM, hle⟩ := mem_maxClass.mp hM
  obtain ⟨hsub, hsf, hmaxim⟩ := mem_maxSumFreeSets.mp hmax
  have ht1 : 1 ≤ t := interval_one_le (hsub htM)
  have htn : t ≤ (n : ℤ) := interval_le (hsub htM)
  have htnat : (t.toNat : ℤ) = t := Int.toNat_of_nonneg (by omega)
  refine ⟨?_, hsf, ?_⟩
  · intro x hx
    have hxle := hle x hx
    have hx1 := interval_one_le (hsub hx)
    rw [interval, Finset.mem_Icc]
    exact ⟨hx1, by omega⟩
  · intro x hx hxM
    have hxI := Finset.mem_Icc.mp hx
    refine hmaxim x ?_ hxM
    rw [interval, Finset.mem_Icc]
    exact ⟨hxI.1, by omega⟩

theorem mem_maxSumFreeSets_of_mem_maxClass {n : ℕ} {M : Finset ℤ} {t : ℤ}
    (hM : M ∈ maxClass n t) : M ∈ maxSumFreeSets t.toNat :=
  mem_maxSumFreeSets.mpr (isMaxSumFree_toNat_of_mem_maxClass hM)

/-- **Covering lemma.**  If `M` is maximal sum-free in `{1,…,n}` with
maximum `t`, then every `y ∈ (t, n]` is a sum of two elements of `M`.
The obstruction to adjoining `y` cannot be `a + y ∈ M` or `y + y ∈ M`
(both exceed `t`), so it must be `y = a + b` with `a, b ∈ M`. -/
theorem ioc_subset_image_sum_of_mem_maxClass {n : ℕ} {M : Finset ℤ} {t : ℤ}
    (hM : M ∈ maxClass n t) :
    Finset.Ioc t (n : ℤ) ⊆ (M.product M).image fun p => p.1 + p.2 := by
  intro y hy
  obtain ⟨hmax, htM, hle⟩ := mem_maxClass.mp hM
  have hsub := (mem_maxSumFreeSets.mp hmax).1
  have ht1 : 1 ≤ t := interval_one_le (hsub htM)
  have hyI := Finset.mem_Ioc.mp hy
  have hyM : y ∉ M := fun hmem => by
    have := hle y hmem
    omega
  have hyIn : y ∈ interval n := Finset.mem_Icc.mpr ⟨by omega, hyI.2⟩
  rcases (mem_maxSumFreeSets.mp hmax).exists_obstruction hyIn hyM with
      ⟨a, ha, b, hb, hab⟩ | ⟨a, ha, hax⟩ | ⟨a, ha, hxa⟩ | hxx
  · exact Finset.mem_image.mpr
      ⟨(a, b), Finset.mem_product.mpr ⟨ha, hb⟩, hab⟩
  · have ha1 := interval_one_le (hsub ha)
    have hsum := hle _ hax
    omega
  · have ha1 := interval_one_le (hsub ha)
    have hsum := hle _ hxa
    omega
  · have hsum := hle _ hxx
    omega

/-- The covering lemma bounds the top segment: `(t, n]` has at most `|M|²`
elements, since it is covered by the sumset `M + M`. -/
theorem card_Ioc_le_card_sq_of_mem_maxClass {n : ℕ} {M : Finset ℤ} {t : ℤ}
    (hM : M ∈ maxClass n t) :
    (Finset.Ioc t (n : ℤ)).card ≤ M.card ^ 2 :=
  calc (Finset.Ioc t (n : ℤ)).card
      ≤ ((M.product M).image fun p => p.1 + p.2).card :=
        Finset.card_le_card (ioc_subset_image_sum_of_mem_maxClass hM)
    _ ≤ (M.product M).card := Finset.card_image_le
    _ = M.card * M.card := Finset.card_product _ _
    _ = M.card ^ 2 := (pow_two _).symm

/-- Numeric form of the covering bound: `n - t ≤ |M|²`. -/
theorem sub_le_card_sq_of_mem_maxClass {n : ℕ} {M : Finset ℤ} {t : ℤ}
    (hM : M ∈ maxClass n t) :
    ((n : ℤ) - t).toNat ≤ M.card ^ 2 := by
  rw [← Int.card_Ioc]
  exact card_Ioc_le_card_sq_of_mem_maxClass hM

/-- A maximal sum-free `M ⊆ {1,…,n}` with maximum `t` is a sum-free subset
of `{1,…,t}` (by the restriction lemma), so `2|M| ≤ t + 1`. -/
theorem two_mul_card_le_of_mem_maxClass {n : ℕ} {M : Finset ℤ} {t : ℤ}
    (hM : M ∈ maxClass n t) :
    2 * M.card ≤ t.toNat + 1 :=
  two_mul_card_le_of_isSumFree
    (mem_maxSumFreeSets.mp (mem_maxSumFreeSets_of_mem_maxClass hM)).1
    (mem_maxSumFreeSets.mp (mem_maxSumFreeSets_of_mem_maxClass hM)).2.1

/-- The two key bounds packaged over `ℤ`: `n - t ≤ |M|²` (covering) and
`2|M| ≤ t + 1` (sum-freeness inside `{1,…,t}`). -/
theorem bounds_of_mem_maxClass {n : ℕ} {M : Finset ℤ} {t : ℤ}
    (hM : M ∈ maxClass n t) :
    (n : ℤ) - t ≤ (M.card : ℤ) ^ 2 ∧ 2 * (M.card : ℤ) ≤ t + 1 := by
  obtain ⟨hmax, htM, -⟩ := mem_maxClass.mp hM
  have htI := Finset.mem_Icc.mp ((mem_maxSumFreeSets.mp hmax).1 htM)
  have hcov := card_Ioc_le_card_sq_of_mem_maxClass hM
  have h2k := two_mul_card_le_of_mem_maxClass hM
  have hIoc : ((Finset.Ioc t (n : ℤ)).card : ℤ) = (n : ℤ) - t := by
    rw [Int.card_Ioc, Int.toNat_of_nonneg (by omega)]
  have htnat : (t.toNat : ℤ) = t := Int.toNat_of_nonneg (by omega)
  refine ⟨?_, ?_⟩
  · have h1 : ((Finset.Ioc t (n : ℤ)).card : ℤ) ≤ ((M.card ^ 2 : ℕ) : ℤ) := by
      exact_mod_cast hcov
    rwa [hIoc, Nat.cast_pow] at h1
  · have h1 : ((2 * M.card : ℕ) : ℤ) ≤ ((t.toNat + 1 : ℕ) : ℤ) := by
      exact_mod_cast h2k
    push_cast at h1
    rwa [htnat] at h1

/-- **Maximum lower bound.**  For `M ∈ maxClass n t`, combining
`n - t ≤ |M|²` with `2|M| ≤ t + 1` gives `4n ≤ 4t + 4|M|² ≤ (t + 3)²`,
i.e. `max M ≥ 2√n − 3`. -/
theorem four_mul_le_sq_add_three_of_mem_maxClass {n : ℕ} {M : Finset ℤ} {t : ℤ}
    (hM : M ∈ maxClass n t) :
    4 * (n : ℤ) ≤ (t + 3) ^ 2 := by
  obtain ⟨hcov, h2k⟩ := bounds_of_mem_maxClass hM
  have hsq : (2 * (M.card : ℤ)) ^ 2 ≤ (t + 1) ^ 2 :=
    pow_le_pow_left₀ (by positivity) h2k 2
  nlinarith [hcov, hsq]

/-- **Vanishing criterion.**  If `(t + 1)² < 4(n - t)` then no maximal
sum-free set can have maximum `t`: `n - t ≤ |M|²` and `2|M| ≤ t + 1`
would force `4(n - t) ≤ (t + 1)²`. -/
theorem maxClass_eq_empty_of_sq_lt {n : ℕ} {t : ℤ}
    (h : (t + 1) ^ 2 < 4 * ((n : ℤ) - t)) : maxClass n t = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro M hM
  obtain ⟨hcov, h2k⟩ := bounds_of_mem_maxClass hM
  have hsq : (2 * (M.card : ℤ)) ^ 2 ≤ (t + 1) ^ 2 :=
    pow_le_pow_left₀ (by positivity) h2k 2
  nlinarith [hcov, hsq]

/-- Card form: `(t + 1)² < 4(n - t)` forces `|maxClass n t| = 0`. -/
theorem maxClass_card_eq_zero_of_sq_lt {n : ℕ} {t : ℤ}
    (h : (t + 1) ^ 2 < 4 * ((n : ℤ) - t)) : (maxClass n t).card = 0 :=
  Finset.card_eq_zero.mpr (maxClass_eq_empty_of_sq_lt h)

/-- The maximum lower bound specialised to the actual maximum `M.max'`:
every maximal sum-free `M ⊆ {1,…,n}` satisfies `4n ≤ (max M + 3)²`. -/
theorem four_mul_le_sq_max'_add_three {n : ℕ} (hn : 1 ≤ n) {M : Finset ℤ}
    (hM : M ∈ maxSumFreeSets n) :
    4 * (n : ℤ) ≤ (M.max' (nonempty_of_mem_maxSumFreeSets hn hM) + 3) ^ 2 := by
  have hne := nonempty_of_mem_maxSumFreeSets hn hM
  have hmem : M ∈ maxClass n (M.max' hne) :=
    mem_maxClass.mpr ⟨hM, Finset.max'_mem M hne,
      fun x hx => Finset.le_max' M x hx⟩
  exact four_mul_le_sq_add_three_of_mem_maxClass hmem

end JSP000728
