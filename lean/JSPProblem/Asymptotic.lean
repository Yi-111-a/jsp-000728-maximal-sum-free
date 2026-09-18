import JSPProblem.Basic
import JSPProblem.UpperBound
import JSPProblem.BlstCounting
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Defs.Filter

/-!
# JSP-000728 — scaffolding for the sharp asymptotic

Balogh–Liu–Sharifzadeh–Treglown (JEMS 2018) proved that the number `f n`
of inclusion-maximal sum-free subsets of `{1,…,n}` satisfies
`f n = 2 ^ ((1/4 + o(1)) * n)`, i.e. `log₂ f(n) / n → 1/4`.

The upper bound requires the container method and is far beyond what is
formalised here, so we record the statement as a `Prop` (`SharpAsymptotic`)
and prove the honest one-sided consequence of the trivial bound
`f n ≤ 2 ^ n`: eventually `log₂ f(n) / n ≤ 1`.
-/

namespace JSP000728

/-- The BLST18 sharp asymptotic statement: `log₂ f(n) / n → 1/4`.
Formalized as a `Prop` so partial results can be assembled around it. -/
def SharpAsymptotic : Prop :=
  Filter.Tendsto (fun n : ℕ => Real.logb 2 (maxSumFreeCount n : ℝ) / n)
    Filter.atTop (nhds (1 / 4))

/-- The trivial bound gives `log₂ f(n) ≤ n` for all `n`. -/
theorem logb_maxSumFreeCount_le_self (n : ℕ) :
    Real.logb 2 (maxSumFreeCount n : ℝ) ≤ (n : ℝ) :=
  logb_two_maxSumFreeCount_le n

/-- Consequently `log₂ f(n) / n` is eventually at most `1`. -/
theorem logb_ratio_eventually_le_one :
    ∀ᶠ n : ℕ in Filter.atTop, Real.logb 2 (maxSumFreeCount n : ℝ) / n ≤ 1 := by
  rw [Filter.eventually_atTop]
  refine ⟨1, fun n hn => ?_⟩
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [div_le_one hn']
  exact logb_two_maxSumFreeCount_le n

/-- The **lower-bound half of the BLST18 asymptotic is proved**: the
Cameron–Erdős/BLST bound `f n ≥ 2^{⌊n/4⌋}` implies that for every `ε > 0`,
eventually `log₂ f(n) / n ≥ 1/4 − ε`.  Equivalently `liminf ≥ 1/4`; only the
matching `limsup ≤ 1/4` (the container method) is missing. -/
theorem logb_ratio_eventually_ge_quarter_sub {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in Filter.atTop,
      1 / 4 - ε ≤ Real.logb 2 (maxSumFreeCount n : ℝ) / (n : ℝ) := by
  filter_upwards [Filter.eventually_ge_atTop (max 4 (Nat.ceil ε⁻¹ + 1))]
    with n hn
  have hn4 : 4 ≤ n := le_trans (le_max_left _ _) hn
  have hnceil : Nat.ceil ε⁻¹ + 1 ≤ n := le_trans (le_max_right _ _) hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast (by omega : 0 < n)
  have h1 := quarter_sub_one_le_logb_maxSumFreeCount hn4
  have h2 : ((n : ℝ) / 4 - 1) / n ≤ Real.logb 2 (maxSumFreeCount n : ℝ) / n :=
    div_le_div_of_nonneg_right h1 hnpos.le
  have hne' : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  have h3 : ((n : ℝ) / 4 - 1) / n = 1 / 4 - 1 / n := by
    field_simp
  have h4 : (1 : ℝ) / n ≤ ε := by
    have hle : (ε⁻¹ : ℝ) ≤ (n : ℝ) :=
      le_trans (Nat.le_ceil ε⁻¹) (by exact_mod_cast (by omega : Nat.ceil ε⁻¹ ≤ n))
    have hmul : (1 : ℝ) ≤ ε * n := by
      calc (1 : ℝ) = ε * ε⁻¹ := (mul_inv_cancel₀ (ne_of_gt hε)).symm
        _ ≤ ε * n := by gcongr
    rwa [div_le_iff₀ hnpos]
  linarith

/-- With the trivial upper bound, `log₂ f(n) / n` is eventually squeezed into
`[1/4 − ε, 1 + ε]`.  `SharpAsymptotic` would follow from the missing upper
bound `f(n) ≤ 2^{(1/4 + o(1)) n}`. -/
theorem logb_ratio_eventually_mem_Icc {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in Filter.atTop,
      Real.logb 2 (maxSumFreeCount n : ℝ) / (n : ℝ) ∈ Set.Icc (1/4 - ε) (1 + ε) := by
  filter_upwards [logb_ratio_eventually_ge_quarter_sub hε,
    logb_ratio_eventually_le_one] with n hlo hhi
  exact ⟨hlo, by linarith⟩

end JSP000728
