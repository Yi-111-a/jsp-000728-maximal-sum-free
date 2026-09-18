import JSPProblem.AsymptoticReduction
import JSPProblem.PairBound
import JSPProblem.SumFreeCount
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# JSP-000728 — `1/4` is the sharp threshold for `EventualRatioUpper`

The predicate `EventualRatioUpper c` (eventually `log₂ f(n)/n ≤ c + ε` for
every `ε > 0`, where `f n = maxSumFreeCount n`) is the packaged
container-method hypothesis from `JSPProblem.AsymptoticReduction`.  This file
shows that `1/4` is its *sharp* threshold:

* **Below `1/4` is impossible (proved unconditionally).**  The Cameron–Erdős /
  BLST lower bound `log₂ f(n)/n ≥ 1/4 − ε` (eventually), already proved as
  `logb_ratio_eventually_ge_quarter_sub`, rules out every `c < 1/4`:
  `not_eventualRatioUpper_of_lt_quarter`.

* **`EventualRatioUpper (1/4)` covers everything above.**  By monotonicity,
  `EventualRatioUpper (1/4)` is equivalent to `∀ c ≥ 1/4, EventualRatioUpper c`
  (`eventualRatioUpper_iff_forall_Ici`), hence also to `SharpAsymptotic`
  (`sharpAsymptotic_iff_forall_Ici`).

* **Sanity check at the top.**  The trivial bound gives
  `EventualRatioUpper 1` unconditionally (`eventualRatioUpper_one`), and the
  pairing argument of `JSPProblem.PairBound` applied directly to
  `sumFreeCount` gives `log₂ (sumFreeCount n)/n ≤ log₂ 3 / 2 + ε` eventually
  (`logb_sumFreeCount_ratio_eventually_le`).
-/

namespace JSP000728

/-- The empty set is sum-free (vacuously). -/
theorem isSumFree_empty : IsSumFree (∅ : Finset ℤ) := by
  intro x hx
  exact absurd hx (Finset.notMem_empty x)

/-- `sumFreeCount n ≥ 1`: the empty set is always a sum-free subset. -/
theorem sumFreeCount_pos (n : ℕ) : 0 < sumFreeCount n :=
  Finset.card_pos.mpr
    ⟨∅, mem_sumFreeSets.mpr ⟨Finset.empty_subset _, isSumFree_empty⟩⟩

/-- Taking `log₂` of `sumFreeCount n ≤ 2 * 3^(n/2)`:
`log₂ (sumFreeCount n) ≤ 1 + (n/2) log₂ 3`.  Mirrors
`logb_two_maxSumFreeCount_le_pair`. -/
theorem logb_two_sumFreeCount_le_pair (n : ℕ) :
    Real.logb 2 (sumFreeCount n : ℝ) ≤ 1 + (n : ℝ) / 2 * Real.logb 2 3 := by
  have hb : (1 : ℝ) < 2 := by norm_num
  have hpos : (0 : ℝ) < (sumFreeCount n : ℝ) := by
    exact_mod_cast sumFreeCount_pos n
  have hbound : (0 : ℝ) < ((2 * 3 ^ (n / 2) : ℕ) : ℝ) := by
    have h : 0 < 2 * 3 ^ (n / 2) := by positivity
    exact_mod_cast h
  have hle : (sumFreeCount n : ℝ) ≤ ((2 * 3 ^ (n / 2) : ℕ) : ℝ) := by
    exact_mod_cast sumFreeCount_le_two_mul_three_pow n
  calc Real.logb 2 (sumFreeCount n : ℝ)
      ≤ Real.logb 2 ((2 * 3 ^ (n / 2) : ℕ) : ℝ) :=
        (Real.logb_le_logb hb hpos hbound).mpr hle
    _ = Real.logb 2 2 + Real.logb 2 ((3 : ℝ) ^ (n / 2)) := by
        push_cast
        rw [Real.logb_mul (by norm_num) (pow_ne_zero _ (by norm_num))]
    _ = 1 + (n / 2 : ℕ) * Real.logb 2 3 := by
        rw [Real.logb_pow, Real.logb_self_eq_one hb]
    _ ≤ 1 + (n : ℝ) / 2 * Real.logb 2 3 := by
        have hL : (0 : ℝ) ≤ Real.logb 2 3 :=
          (Real.logb_pos hb (by norm_num)).le
        have hd : ((n / 2 : ℕ) : ℝ) ≤ (n : ℝ) / 2 := Nat.cast_div_le
        gcongr

/-- Dividing by `n`: eventually `log₂ (sumFreeCount n)/n ≤ log₂ 3 / 2 + ε`.
Mirrors `logb_ratio_eventually_le_logb3_half`. -/
theorem logb_sumFreeCount_ratio_eventually_le {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in Filter.atTop,
      Real.logb 2 (sumFreeCount n : ℝ) / (n : ℝ) ≤ Real.logb 2 3 / 2 + ε := by
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
  have hε' : (0 : ℝ) < 1 / ε := by positivity
  have hNpos : (0 : ℝ) < N := hε'.trans hN
  filter_upwards [Filter.eventually_ge_atTop N] with n hn
  have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := hNpos.trans_le hNn
  have hinv : (1 : ℝ) / n ≤ ε := by
    have h1 : (1 : ℝ) / n ≤ 1 / N := one_div_le_one_div_of_le hNpos hNn
    have h2 : (1 : ℝ) / N < ε := by
      rw [← one_div_one_div ε]
      exact one_div_lt_one_div_of_lt hε' hN
    exact h1.trans h2.le
  have hbound := logb_two_sumFreeCount_le_pair n
  calc Real.logb 2 (sumFreeCount n : ℝ) / (n : ℝ)
      ≤ (1 + (n : ℝ) / 2 * Real.logb 2 3) / (n : ℝ) := by
        apply div_le_div_of_nonneg_right hbound
        exact hnpos.le
    _ = 1 / n + Real.logb 2 3 / 2 := by field_simp
    _ ≤ ε + Real.logb 2 3 / 2 := by linarith
    _ = Real.logb 2 3 / 2 + ε := by ring

/-- **Constants below `1/4` are impossible.**  If `EventualRatioUpper c` held
for some `c < 1/4`, then for `ε = (1/4 − c)/3 > 0` the eventual bounds
`log₂ f(n)/n ≤ c + ε` and `1/4 − ε ≤ log₂ f(n)/n` would hold simultaneously at
some `n` (the intersection of two `atTop`-events is nonempty since `atTop` on
`ℕ` is `NeBot`), giving `1/4 − c ≤ 2ε = 2(1/4 − c)/3 < 1/4 − c`. -/
theorem not_eventualRatioUpper_of_lt_quarter {c : ℝ} (h : c < 1 / 4) :
    ¬ EventualRatioUpper c := by
  intro h2
  have hε : (0 : ℝ) < (1 / 4 - c) / 3 := by linarith
  obtain ⟨n, hup, hlo⟩ :=
    ((h2 ((1 / 4 - c) / 3) hε).and
      (logb_ratio_eventually_ge_quarter_sub hε)).exists
  linarith

/-- `EventualRatioUpper (1/4)` holds iff `EventualRatioUpper c` holds for every
`c ≥ 1/4`: the forward direction is monotonicity, the reverse is evaluation at
`c = 1/4`. -/
theorem eventualRatioUpper_iff_forall_Ici :
    EventualRatioUpper (1 / 4) ↔
      ∀ c ∈ Set.Ici (1 / 4), EventualRatioUpper c := by
  constructor
  · intro h c hc
    exact h.mono (Set.mem_Ici.mp hc)
  · intro h
    exact h (1 / 4) (Set.mem_Ici.mpr le_rfl)

/-- The BLST18 headline `SharpAsymptotic` is equivalent to
`EventualRatioUpper c` for **all** `c ≥ 1/4` simultaneously — and, since
`not_eventualRatioUpper_of_lt_quarter` rules out every `c < 1/4`, the
threshold `1/4` is sharp. -/
theorem sharpAsymptotic_iff_forall_Ici :
    SharpAsymptotic ↔ ∀ c ∈ Set.Ici (1 / 4), EventualRatioUpper c :=
  sharpAsymptotic_iff_eventualRatioUpper.trans eventualRatioUpper_iff_forall_Ici

/-- The trivial bound `f n ≤ 2^n` gives `EventualRatioUpper 1`
unconditionally. -/
theorem eventualRatioUpper_one : EventualRatioUpper 1 := by
  intro ε hε
  filter_upwards [logb_ratio_eventually_le_one] with n hn
  linarith

end JSP000728
