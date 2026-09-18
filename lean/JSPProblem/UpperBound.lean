import JSPProblem.Basic
import JSPProblem.UpperHalf
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# JSP-000728 — trivial exponential upper bound

Every inclusion-maximal sum-free subset of `{1,…,n}` is in particular a
*subset* of `{1,…,n}`, so `maxSumFreeCount n ≤ 2 ^ n`.  Taking `log₂`
yields `log₂ (maxSumFreeCount n) ≤ n`, the trivial half of the
`log₂ f(n)/n → 1/4` asymptotic.
-/

namespace JSP000728

/-- The interval `{1,…,n}` as a `Finset ℤ` has `n` elements. -/
theorem card_interval (n : ℕ) : (interval n).card = n := by
  simp [interval, Int.card_Icc]

/-- `f n` counts subsets of `{1,…,n}`, so `f n ≤ 2^n`. -/
theorem maxSumFreeCount_le_two_pow (n : ℕ) : maxSumFreeCount n ≤ 2 ^ n := by
  have hsub : maxSumFreeSets n ⊆ (interval n).powerset :=
    Finset.filter_subset _ _
  calc maxSumFreeCount n
      ≤ ((interval n).powerset).card := Finset.card_le_card hsub
    _ = 2 ^ (interval n).card := Finset.card_powerset _
    _ = 2 ^ n := by rw [card_interval]

/-- `f n ≥ 1`: the upper half of `{1,…,n}` is always maximal sum-free. -/
theorem maxSumFreeCount_pos (n : ℕ) : 0 < maxSumFreeCount n :=
  Finset.card_pos.mpr
    ⟨upperHalf n, mem_maxSumFreeSets.mpr (upperHalf_isMaxSumFree n)⟩

/-- Real-valued version of `maxSumFreeCount_le_two_pow`. -/
theorem maxSumFreeCount_le_two_pow_real (n : ℕ) :
    (maxSumFreeCount n : ℝ) ≤ (2 : ℝ) ^ n := by
  exact_mod_cast maxSumFreeCount_le_two_pow n

/-- Taking `log₂` of `f n ≤ 2 ^ n` gives `log₂ (f n) ≤ n`. -/
theorem logb_two_maxSumFreeCount_le (n : ℕ) :
    Real.logb 2 (maxSumFreeCount n : ℝ) ≤ n := by
  have hb : (1 : ℝ) < 2 := by norm_num
  have hpos : (0 : ℝ) < (maxSumFreeCount n : ℝ) := by
    exact_mod_cast maxSumFreeCount_pos n
  have hpow : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  calc Real.logb 2 (maxSumFreeCount n : ℝ)
      ≤ Real.logb 2 ((2 : ℝ) ^ n) :=
        (Real.logb_le_logb hb hpos hpow).mpr (maxSumFreeCount_le_two_pow_real n)
    _ = (n : ℝ) * Real.logb 2 2 := Real.logb_pow 2 2 n
    _ = n := by simp

end JSP000728
