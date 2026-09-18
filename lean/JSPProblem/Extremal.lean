import JSPProblem.Basic
import JSPProblem.Odds
import JSPProblem.UpperHalf

/-!
# JSP-000728 — extremal uniqueness of the canonical maximal sum-free sets

The two "canonical" inclusion-maximal sum-free subsets of `{1, …, n}` are the
odd numbers `odds n` and the upper half `upperHalf n`.  This file shows each
is the *unique* maximal sum-free set contained in it:

* `isSumFree_insert_odd` — adjoining an odd element to a sum-free set of odds
  keeps it sum-free (odds sum to evens).
* `eq_odds_of_isMaxSumFree_subset` — a maximal sum-free `M ⊆ odds n` equals
  `odds n`.
* `isSumFree_insert_upperHalf` — adjoining an element of the upper-half range
  to a sum-free set inside `upperHalf n` keeps it sum-free (sums exceed `n`).
* `eq_upperHalf_of_isMaxSumFree_subset` — a maximal sum-free
  `M ⊆ upperHalf n` equals `upperHalf n`.
* `odds_ne_upperHalf` — for `n ≥ 2` the two canonical sets are distinct.
-/

namespace JSP000728

/-- Inserting an odd integer `x` into a sum-free set `s ⊆ odds n` preserves
sum-freeness: every element of `insert x s` is odd, so any sum of two of them
is even and cannot lie in `insert x s`. -/
theorem isSumFree_insert_odd {n : ℕ} {s : Finset ℤ} {x : ℤ}
    (_hsf : IsSumFree s) (hsub : s ⊆ odds n) (hx : x % 2 = 1) :
    IsSumFree (insert x s) := by
  intro a ha b hb hab
  have ha_odd : a % 2 = 1 := by
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact hx
    · exact (mem_odds.mp (hsub ha)).2
  have hb_odd : b % 2 = 1 := by
    rcases Finset.mem_insert.mp hb with rfl | hb
    · exact hx
    · exact (mem_odds.mp (hsub hb)).2
  have hab_odd : (a + b) % 2 = 1 := by
    rcases Finset.mem_insert.mp hab with hab' | hab
    · rw [hab']; exact hx
    · exact (mem_odds.mp (hsub hab)).2
  omega

/-- The odds are the *unique* maximal sum-free subset of `{1, …, n}` contained
in `odds n`: any missing odd `x` could be adjoined without destroying
sum-freeness, contradicting maximality. -/
theorem eq_odds_of_isMaxSumFree_subset {n : ℕ} {M : Finset ℤ}
    (hM : IsMaxSumFree n M) (hsub : M ⊆ odds n) : M = odds n := by
  refine subset_antisymm hsub fun x hx => ?_
  by_contra hxM
  have hxo := mem_odds.mp hx
  exact hM.2.2 x hxo.1 hxM (isSumFree_insert_odd hM.2.1 hsub hxo.2)

/-- Inserting an element `x` of `{1, …, n}` lying in the upper-half range
(`n < 2x`) into a sum-free set `s ⊆ upperHalf n` preserves sum-freeness:
every member `y` of `insert x s` satisfies `2y > n`, so `a + b > n` and hence
`a + b ∉ interval n ⊇ insert x s`. -/
theorem isSumFree_insert_upperHalf {n : ℕ} {s : Finset ℤ} {x : ℤ}
    (_hsf : IsSumFree s) (hsub : s ⊆ upperHalf n)
    (hxI : x ∈ interval n) (hx : (n : ℤ) < 2 * x) :
    IsSumFree (insert x s) := by
  intro a ha b hb hab
  have ha_big : (n : ℤ) < 2 * a := by
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact hx
    · exact (mem_upperHalf.mp (hsub ha)).2
  have hb_big : (n : ℤ) < 2 * b := by
    rcases Finset.mem_insert.mp hb with rfl | hb
    · exact hx
    · exact (mem_upperHalf.mp (hsub hb)).2
  have hab_mem : a + b ∈ interval n := by
    rcases Finset.mem_insert.mp hab with hab' | hab
    · rw [hab']; exact hxI
    · exact (mem_upperHalf.mp (hsub hab)).1
  have hab_le : a + b ≤ (n : ℤ) := (Finset.mem_Icc.mp hab_mem).2
  omega

/-- The upper half is the *unique* maximal sum-free subset of `{1, …, n}`
contained in `upperHalf n`. -/
theorem eq_upperHalf_of_isMaxSumFree_subset {n : ℕ} {M : Finset ℤ}
    (hM : IsMaxSumFree n M) (hsub : M ⊆ upperHalf n) : M = upperHalf n := by
  refine subset_antisymm hsub fun x hx => ?_
  by_contra hxM
  have hxu := mem_upperHalf.mp hx
  exact hM.2.2 x hxu.1 hxM
    (isSumFree_insert_upperHalf hM.2.1 hsub hxu.1 hxu.2)

/-- For `n ≥ 2` the two canonical maximal sum-free sets differ: `1` is odd but
does not lie in the upper half. -/
theorem odds_ne_upperHalf {n : ℕ} (hn : 2 ≤ n) : odds n ≠ upperHalf n := by
  intro h
  have h1o : (1 : ℤ) ∈ odds n :=
    mem_odds.mpr ⟨Finset.mem_Icc.mpr ⟨le_refl 1, by omega⟩, by omega⟩
  have h1u : (1 : ℤ) ∈ upperHalf n := by rw [← h]; exact h1o
  have h2 : (n : ℤ) < 2 * 1 := (mem_upperHalf.mp h1u).2
  omega

end JSP000728
