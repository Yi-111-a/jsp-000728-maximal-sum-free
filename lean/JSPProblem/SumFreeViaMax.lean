import JSPProblem.SumFreeCount
import JSPProblem.Extend
import JSPProblem.MaxCard
import JSPProblem.AsymptoticReduction
import JSPProblem.OrbitSharp
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic

/-!
# JSP-000728 — bridging `sumFreeCount` and `maxSumFreeCount`

The Wolfovitz-style counting argument relates the number of *all* sum-free
subsets of `{1,…,n}` to the number of *inclusion-maximal* ones.

* `sumFreeSets_subset_biUnion_powerset` — every sum-free `s ⊆ interval n`
  extends to a maximal sum-free `M = maxExt n s` (`maxExt_spec`), and
  `s ∈ M.powerset`; hence `sumFreeSets n` is covered by the powersets of the
  maximal sum-free sets.

* `sumFreeCount_le_maxSumFreeCount_mul_pow` — the fiber bound: each maximal
  sum-free `M` has at most `2^{|M|} ≤ 2^{(n+1)/2}` subsets (the classical bound
  `card_le_of_isMaxSumFree`), so
  `sumFreeCount n ≤ maxSumFreeCount n · 2^{(n+1)/2}`.

* `sumFreeCount_le_rpow`, `logb_sumFreeCount_le` — real and `log₂` forms.

* `eventualRatioUpper_sumFreeCount` — the asymptotic consequence: if
  `maxSumFreeCount` satisfies `EventualRatioUpper c` (i.e. eventually
  `log₂ f(n)/n ≤ c + ε`), then `sumFreeCount` inherits the analogous bound with
  constant `c + 1/2`.  Applied to the proved instance
  `eventualRatioUpper_111_160` this gives
  `log₂ (sumFreeCount n)/n ≤ 191/160 + ε` eventually
  (`logb_sumFreeCount_ratio_eventually_le_191_160`).

The converse direction `maxSumFreeCount n ≤ sumFreeCount n` already exists as
`maxSumFreeCount_le_sumFreeCount` in `JSPProblem.SumFreeCount` (every maximal
sum-free set is sum-free).
-/

namespace JSP000728

/-- **Covering lemma.**  Every sum-free subset of `{1,…,n}` is a subset of its
chosen maximal extension `maxExt n s`, so the sum-free sets are covered by the
powersets of the maximal sum-free sets:
`sumFreeSets n ⊆ ⋃_{M ∈ maxSumFreeSets n} M.powerset`. -/
theorem sumFreeSets_subset_biUnion_powerset (n : ℕ) :
    sumFreeSets n ⊆ (maxSumFreeSets n).biUnion (fun M => M.powerset) := by
  intro s hs
  obtain ⟨hsub, hsf⟩ := mem_sumFreeSets.mp hs
  rw [Finset.mem_biUnion]
  exact ⟨maxExt n s, maxExt_mem hsub hsf,
    Finset.mem_powerset.mpr (maxExt_spec hsub hsf).1⟩

/-- **Wolfovitz-style counting bound (natural form).**  Each maximal sum-free
`M ⊆ {1,…,n}` has `M.card ≤ (n+1)/2` (`card_le_of_isMaxSumFree`), hence covers
at most `2^{(n+1)/2}` sum-free subsets; together with the covering lemma this
gives `sumFreeCount n ≤ maxSumFreeCount n · 2^{(n+1)/2}`. -/
theorem sumFreeCount_le_maxSumFreeCount_mul_pow (n : ℕ) :
    sumFreeCount n ≤ maxSumFreeCount n * 2 ^ ((n + 1) / 2) := by
  calc sumFreeCount n
      = (sumFreeSets n).card := rfl
    _ ≤ ((maxSumFreeSets n).biUnion (fun M => M.powerset)).card :=
        Finset.card_le_card (sumFreeSets_subset_biUnion_powerset n)
    _ ≤ ∑ M ∈ maxSumFreeSets n, M.powerset.card := Finset.card_biUnion_le
    _ ≤ ∑ M ∈ maxSumFreeSets n, 2 ^ ((n + 1) / 2) := by
        refine Finset.sum_le_sum fun M hM => ?_
        rw [Finset.card_powerset]
        exact pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2)
          (card_le_of_isMaxSumFree hM)
    _ = maxSumFreeCount n * 2 ^ ((n + 1) / 2) := by
        simp [Finset.sum_const, maxSumFreeCount]

/-- **Real form.**  The same bound after casting to `ℝ`, relaxing the natural
floor division `(n+1)/2` to real division. -/
theorem sumFreeCount_le_rpow (n : ℕ) :
    (sumFreeCount n : ℝ) ≤
      (maxSumFreeCount n : ℝ) * (2 : ℝ) ^ (((n : ℝ) + 1) / 2) := by
  have hR : (sumFreeCount n : ℝ) ≤
      (maxSumFreeCount n : ℝ) * (2 : ℝ) ^ ((n + 1) / 2 : ℕ) := by
    exact_mod_cast sumFreeCount_le_maxSumFreeCount_mul_pow n
  have hexp : (((n + 1) / 2 : ℕ) : ℝ) ≤ ((n : ℝ) + 1) / 2 := by
    have h' := Nat.cast_div_le (α := ℝ) (m := n + 1) (n := 2)
    push_cast at h'
    linarith
  have hpow : (2 : ℝ) ^ ((n + 1) / 2 : ℕ) ≤
      (2 : ℝ) ^ (((n : ℝ) + 1) / 2) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hexp
  exact hR.trans (mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg _))

/-- **Logarithmic form.**  Taking `log₂` of the bridge bound:
`log₂ (sumFreeCount n) ≤ log₂ (maxSumFreeCount n) + (n + 1)/2`. -/
theorem logb_sumFreeCount_le (n : ℕ) :
    Real.logb 2 (sumFreeCount n : ℝ) ≤
      Real.logb 2 (maxSumFreeCount n : ℝ) + ((n : ℝ) + 1) / 2 := by
  have hpos1 : (0 : ℝ) < (sumFreeCount n : ℝ) :=
    Nat.cast_pos.mpr
      (lt_of_lt_of_le (maxSumFreeCount_pos n)
        (maxSumFreeCount_le_sumFreeCount n))
  have hpos2 : (0 : ℝ) <
      (maxSumFreeCount n : ℝ) * (2 : ℝ) ^ (((n : ℝ) + 1) / 2) :=
    mul_pos (Nat.cast_pos.mpr (maxSumFreeCount_pos n))
      (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _)
  have hlog := (Real.logb_le_logb (by norm_num : (1 : ℝ) < 2) hpos1 hpos2).mpr
    (sumFreeCount_le_rpow n)
  rw [Real.logb_mul (Nat.cast_ne_zero.mpr (maxSumFreeCount_pos n).ne')
        (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _).ne',
      Real.logb_rpow (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)]
    at hlog
  exact hlog

/-- **Transfer of the eventual ratio bound.**  If `maxSumFreeCount` satisfies
`EventualRatioUpper c` — i.e. for every `ε > 0`, eventually
`log₂ (maxSumFreeCount n)/n ≤ c + ε` — then `sumFreeCount` satisfies the
analogous bound with constant `c + 1/2`: the `2^{(n+1)/2}` factor contributes
exactly `1/2` to the exponent, and the `+1` and `ε/2` slack is absorbed by
`1/n → 0`. -/
theorem eventualRatioUpper_sumFreeCount {c : ℝ} (h : EventualRatioUpper c)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in Filter.atTop,
      Real.logb 2 (sumFreeCount n : ℝ) / (n : ℝ) ≤ c + 1 / 2 + ε := by
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
  have hε' : (0 : ℝ) < 1 / ε := by positivity
  have hNpos : (0 : ℝ) < N := hε'.trans hN
  filter_upwards [h (ε / 2) (by linarith), Filter.eventually_ge_atTop N]
    with n hup hn
  have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := hNpos.trans_le hNn
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  -- `1/n ≤ ε` eventually, hence `1/(2n) ≤ ε/2`.
  have hinv : (1 : ℝ) / n ≤ ε := by
    have h1 : (1 : ℝ) / n ≤ 1 / N := one_div_le_one_div_of_le hNpos hNn
    have h2 : (1 : ℝ) / N < ε := by
      rw [← one_div_one_div ε]
      exact one_div_lt_one_div_of_lt hε' hN
    exact h1.trans h2.le
  have hdiv := div_le_div_of_nonneg_right (logb_sumFreeCount_le n) hnpos.le
  rw [add_div] at hdiv
  have hsplit : (((n : ℝ) + 1) / 2) / (n : ℝ) = 1 / 2 + 1 / (2 * (n : ℝ)) := by
    field_simp
  rw [hsplit] at hdiv
  have hhalf : (1 : ℝ) / (2 * (n : ℝ)) ≤ ε / 2 := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (n : ℝ))]
    rw [div_le_iff₀ hnpos] at hinv
    linarith
  linarith

/-- **Unconditional instance.**  The proved bound `eventualRatioUpper_111_160`
(`EventualRatioUpper (max (111/160) (1/2))`) transfers to `sumFreeCount`:
eventually `log₂ (sumFreeCount n)/n ≤ max (111/160) (1/2) + 1/2 + ε`. -/
theorem logb_sumFreeCount_ratio_eventually_le_of_111_160 {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in Filter.atTop,
      Real.logb 2 (sumFreeCount n : ℝ) / (n : ℝ) ≤
        max (111 / 160 : ℝ) (1 / 2) + 1 / 2 + ε :=
  eventualRatioUpper_sumFreeCount eventualRatioUpper_111_160 hε

/-- Numerical form of the instance: `max (111/160) (1/2) + 1/2 = 191/160`. -/
theorem logb_sumFreeCount_ratio_eventually_le_191_160 {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in Filter.atTop,
      Real.logb 2 (sumFreeCount n : ℝ) / (n : ℝ) ≤ 191 / 160 + ε := by
  have hmax : max (111 / 160 : ℝ) (1 / 2) = 111 / 160 := by
    rw [max_eq_left]
    norm_num
  filter_upwards [logb_sumFreeCount_ratio_eventually_le_of_111_160 hε]
    with n hn
  rw [hmax] at hn
  linarith

end JSP000728
