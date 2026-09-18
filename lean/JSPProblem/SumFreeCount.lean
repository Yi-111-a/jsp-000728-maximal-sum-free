import JSPProblem.Basic

/-!
# JSP-000728 — counting all sum-free subsets

`sumFreeCount n` counts *all* sum-free subsets of `interval n = {1,…,n}`
(not just the inclusion-maximal ones).  Since every inclusion-maximal
sum-free subset is sum-free, `maxSumFreeCount n ≤ sumFreeCount n`; all
upper bounds on `sumFreeCount` therefore transfer to `maxSumFreeCount`.
-/

namespace JSP000728

/-- The finset of all sum-free subsets of `interval n`. -/
def sumFreeSets (n : ℕ) : Finset (Finset ℤ) :=
  (interval n).powerset.filter IsSumFree

/-- The number of sum-free subsets of `{1, …, n}`. -/
def sumFreeCount (n : ℕ) : ℕ := (sumFreeSets n).card

theorem mem_sumFreeSets {n : ℕ} {s : Finset ℤ} :
    s ∈ sumFreeSets n ↔ s ⊆ interval n ∧ IsSumFree s := by
  simp only [sumFreeSets, Finset.mem_filter, Finset.mem_powerset]

/-- Every inclusion-maximal sum-free subset is a sum-free subset, so
`f n ≤ #(sum-free subsets of {1,…,n})`. -/
theorem maxSumFreeCount_le_sumFreeCount (n : ℕ) :
    maxSumFreeCount n ≤ sumFreeCount n := by
  apply Finset.card_le_card
  intro s hs
  rw [mem_maxSumFreeSets] at hs
  exact mem_sumFreeSets.mpr ⟨hs.1, hs.2.1⟩

end JSP000728
