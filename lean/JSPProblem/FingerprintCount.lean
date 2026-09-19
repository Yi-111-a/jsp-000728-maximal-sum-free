import JSPProblem.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Choose.Bounds

/-!
# JSP-000728 — counting small subsets of `interval n`

The container method needs the observation that the number of *small* subsets of
`interval n = Finset.Icc 1 (n : ℤ)` is subexponential: for every `ε > 0` there is
a `δ > 0` such that, eventually in `n`, the number of subsets of size at most
`⌊δ·n⌋` is at most `2 ^ (ε·n)`.

The proof follows the standard entropy estimate

  `#{s ⊆ [N] : |s| ≤ k} ≤ ∑_{i≤k} C(N,i) ≤ (e·N/k)^k`,

obtained from `Nat.choose_le_pow_div` (`C(N,i) ≤ N^i/i!`) together with the
partial exponential series bound `∑_{i≤k} k^i/i! ≤ e^k`.  With `N = n` and
`k = ⌊δ·n⌋` this gives `≤ (2e/δ)^(δ·n) = 2^(δ·log₂(2e/δ)·n) ≤ 2^(ε·n)` once `δ`
is small enough that `δ·log₂(2e/δ) ≤ ε`; such a `δ` exists because
`δ·log₂(C/δ) → 0` as `δ → 0⁺`.

## Main declarations

* `card_powerset_filter_card_le` — `#{s ⊆ S : |s| ≤ k} ≤ ∑_{i≤k} C(|S|, i)`;
* `sum_pow_div_factorial_le_exp` — truncated exponential series bound;
* `sum_choose_le_exp_mul_pow` — `∑_{i≤k} C(N,i) ≤ (e·N/k)^k`;
* `tendsto_mul_logb_div_nhdsGT_zero` — `δ·log₂(C/δ) → 0` as `δ → 0⁺`;
* `exists_pos_mul_logb_le` — choice of a small `δ`;
* `smallPowersetCard_le_two_rpow` — the goal theorem.
-/

namespace JSP000728

open Filter
open scoped Topology Nat

/-! ### Counting: small subsets versus binomial sums -/

/-- The number of subsets of `S` of cardinality at most `k` is at most
`∑_{i≤k} C(|S|, i)`: the filtered powerset is covered by the `powersetCard`
layers `i ≤ k`. -/
theorem card_powerset_filter_card_le (S : Finset ℤ) (k : ℕ) :
    (S.powerset.filter (fun s => s.card ≤ k)).card ≤
      ∑ i ∈ Finset.range (k + 1), Nat.choose S.card i := by
  have hsub : S.powerset.filter (fun s => s.card ≤ k) ⊆
      (Finset.range (k + 1)).biUnion (fun i => S.powersetCard i) := by
    intro s hs
    simp only [Finset.mem_filter, Finset.mem_powerset] at hs
    rw [Finset.mem_biUnion]
    exact ⟨s.card, Finset.mem_range.mpr (Nat.lt_succ_of_le hs.2),
      Finset.mem_powersetCard.mpr ⟨hs.1, rfl⟩⟩
  refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
  exact Finset.sum_le_sum fun i _ => (Finset.card_powersetCard i S).le

/-! ### The entropy bound `∑_{i≤k} C(N,i) ≤ (e·N/k)^k` -/

/-- A truncated exponential series is bounded by the exponential:
`∑_{i≤k} x^i/i! ≤ e^x` for `x ≥ 0`. -/
theorem sum_pow_div_factorial_le_exp {x : ℝ} (hx : 0 ≤ x) (k : ℕ) :
    (∑ i ∈ Finset.range (k + 1), x ^ i / i !) ≤ Real.exp x := by
  have hexp : Real.exp x = ∑' n : ℕ, x ^ n / n ! := by
    rw [Real.exp_eq_exp_ℝ]
    exact congr_fun (NormedSpace.exp_eq_tsum_div (𝔸 := ℝ)) x
  rw [hexp]
  exact (Real.summable_pow_div_factorial x).sum_le_tsum _
    (fun i _ => div_nonneg (pow_nonneg hx i) (Nat.cast_nonneg _))

/-- **Entropy bound**: for `1 ≤ k ≤ N`,
`∑_{i≤k} C(N,i) ≤ (e·N/k)^k`.

Each term satisfies `C(N,i) ≤ N^i/i! = (N/k)^i · k^i/i! ≤ (N/k)^k · k^i/i!`
(using `i ≤ k` and `N/k ≥ 1`); summing and applying the truncated exponential
bound gives the claim. -/
theorem sum_choose_le_exp_mul_pow {N k : ℕ} (hk : 1 ≤ k) (hkN : k ≤ N) :
    (∑ i ∈ Finset.range (k + 1), Nat.choose N i : ℝ) ≤
      ((N : ℝ) * Real.exp 1 / k) ^ k := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hNk : (1 : ℝ) ≤ N / k :=
    (one_le_div hkpos).mpr (by exact_mod_cast hkN)
  calc (∑ i ∈ Finset.range (k + 1), Nat.choose N i : ℝ)
      ≤ ∑ i ∈ Finset.range (k + 1), (N : ℝ) ^ i / i ! := by
        refine Finset.sum_le_sum fun i _ => ?_
        exact Nat.choose_le_pow_div i N
    _ ≤ ∑ i ∈ Finset.range (k + 1), (N / k) ^ k * ((k : ℝ) ^ i / i !) := by
        apply Finset.sum_le_sum
        intro i hi
        have hi_le : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        have hNi : (N : ℝ) ^ i = (N / k) ^ i * (k : ℝ) ^ i := by
          rw [← mul_pow, div_mul_cancel₀ (N : ℝ) hkpos.ne']
        calc (N : ℝ) ^ i / i ! = (N / k) ^ i * (k : ℝ) ^ i / i ! := by rw [hNi]
          _ = (N / k) ^ i * ((k : ℝ) ^ i / i !) := by rw [mul_div_assoc]
          _ ≤ (N / k) ^ k * ((k : ℝ) ^ i / i !) :=
            mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hNk hi_le)
              (div_nonneg (pow_nonneg (Nat.cast_nonneg k) i) (Nat.cast_nonneg _))
    _ = (N / k) ^ k * ∑ i ∈ Finset.range (k + 1), (k : ℝ) ^ i / i ! := by
        rw [Finset.mul_sum]
    _ ≤ (N / k) ^ k * Real.exp k :=
        mul_le_mul_of_nonneg_left
          (sum_pow_div_factorial_le_exp (Nat.cast_nonneg k) k)
          (pow_nonneg (zero_le_one.trans hNk) k)
    _ = ((N : ℝ) * Real.exp 1 / k) ^ k := by
        have hexp : Real.exp (k : ℝ) = Real.exp 1 ^ k := by
          conv_lhs => rw [show (k : ℝ) = (k : ℝ) * 1 by rw [mul_one]]
          exact Real.exp_nat_mul 1 k
        rw [hexp, mul_div_right_comm, mul_pow]

/-! ### Existence of a small `δ` -/

/-- `δ · log₂(C/δ) → 0` as `δ → 0⁺` (for `C ≠ 0`): expanding
`log₂(C/δ) = (log C − log δ)/log 2` gives a difference of terms tending to `0`,
using `x·log x → 0`. -/
theorem tendsto_mul_logb_div_nhdsGT_zero {C : ℝ} (hC : C ≠ 0) :
    Filter.Tendsto (fun δ : ℝ => δ * Real.logb 2 (C / δ))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have h1 : Filter.Tendsto (fun δ : ℝ => δ * Real.log C) (𝓝[>] (0 : ℝ))
      (𝓝 0) := by
    have h := (continuous_id'.tendsto (0 : ℝ)).mul_const (Real.log C)
    simp only [zero_mul] at h
    exact h.mono_left nhdsWithin_le_nhds
  have h2 : Filter.Tendsto (fun δ : ℝ => Real.log δ * δ) (𝓝[>] (0 : ℝ))
      (𝓝 0) := by
    have h := tendsto_log_mul_rpow_nhdsGT_zero zero_lt_one
    simpa only [Real.rpow_one] using h
  have h3 := (h1.sub h2).div_const (Real.log 2)
  simp only [sub_zero, zero_div] at h3
  refine h3.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  have hδ0 : δ ≠ 0 := ne_of_gt hδ
  simp only [Real.logb, Real.log_div hC hδ0]
  ring

/-- For every `C > 0` and `ε > 0` there is a `δ ∈ (0, 1]` with
`δ · log₂(C/δ) ≤ ε`: the function tends to `0` at `0⁺`. -/
theorem exists_pos_mul_logb_le {C ε : ℝ} (hC : 0 < C) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ δ * Real.logb 2 (C / δ) ≤ ε := by
  have h1 : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ), δ * Real.logb 2 (C / δ) < ε :=
    (tendsto_mul_logb_div_nhdsGT_zero hC.ne').eventually (Iio_mem_nhds hε)
  have h2 : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ), δ ∈ Set.Ioo 0 1 :=
    Ioo_mem_nhdsGT zero_lt_one
  obtain ⟨δ, hδε, hδmem⟩ := (h1.and h2).exists
  exact ⟨δ, hδmem.1, hδmem.2.le, hδε.le⟩

/-! ### The main theorem -/

/-- **Small-subset count is subexponential.**  For every `ε > 0` there exists
`δ > 0` such that, eventually in `n`, the number of subsets of `interval n`
of cardinality at most `⌊δ·n⌋` is at most `2 ^ (ε·n)`. -/
theorem smallPowersetCard_le_two_rpow {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n : ℕ in Filter.atTop,
      (((interval n).powerset.filter (fun s => s.card ≤ ⌊δ * n⌋₊)).card : ℝ) ≤
        (2 : ℝ) ^ (ε * n) := by
  obtain ⟨δ, hδpos, hδ1, hδε⟩ :=
    exists_pos_mul_logb_le (C := 2 * Real.exp 1) (by positivity) hε
  refine ⟨δ, hδpos, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop (Nat.ceil (2 / δ))] with n hn
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hδn : (2 : ℝ) ≤ δ * n := by
    have hceil : (Nat.ceil (2 / δ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hle : 2 / δ ≤ (n : ℝ) := (Nat.le_ceil _).trans hceil
    rw [div_le_iff₀ hδpos] at hle
    linarith [hle]
  set k := ⌊δ * n⌋₊ with hk_def
  -- Floor estimates: `δ·n/2 ≤ k ≤ δ·n` and `1 ≤ k ≤ n`.
  have hkR_le : (k : ℝ) ≤ δ * n :=
    Nat.floor_le (mul_nonneg hδpos.le hn0)
  have hkR_gt : δ * n - 1 < (k : ℝ) := by
    have h := Nat.lt_floor_add_one (δ * (n : ℝ))
    linarith
  have hkR_ge : δ * n / 2 ≤ (k : ℝ) := by linarith
  have hk1 : 1 ≤ k := by
    have h1k : (1 : ℝ) < (k : ℝ) := by linarith
    exact_mod_cast h1k.le
  have hkN : k ≤ n := by
    have h : (k : ℝ) ≤ (n : ℝ) := by
      refine hkR_le.trans ?_
      nlinarith [hδ1, hn0]
    exact_mod_cast h
  -- The ambient cardinality.
  have hcard : (interval n).card = n := by
    unfold interval
    rw [Int.card_Icc]
    simp
  -- Counting + entropy bound.
  have hcount : (((interval n).powerset.filter
        (fun s => s.card ≤ k)).card : ℝ) ≤
      ∑ i ∈ Finset.range (k + 1), (Nat.choose n i : ℝ) := by
    have h := card_powerset_filter_card_le (interval n) k
    rw [hcard] at h
    exact_mod_cast h
  have hsum := sum_choose_le_exp_mul_pow hk1 hkN
  -- Positivity facts and the base comparison `n·e/k ≤ 2e/δ`.
  have hnR : (0 : ℝ) < (n : ℝ) := by
    by_contra hcon
    simp only [not_lt] at hcon
    have hle0 := mul_nonpos_of_nonneg_of_nonpos hδpos.le hcon
    linarith
  have hkR_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
  have h2k : δ * n ≤ 2 * k := by linarith
  have hbase : (n : ℝ) * Real.exp 1 / k ≤ 2 * Real.exp 1 / δ := by
    have hmul := mul_le_mul_of_nonneg_left h2k (Real.exp_pos 1).le
    rw [div_le_div_iff₀ hkR_pos hδpos]
    nlinarith [hmul]
  have hbase1 : (1 : ℝ) ≤ (n : ℝ) * Real.exp 1 / k := by
    have hnk : (1 : ℝ) ≤ (n : ℝ) / k :=
      (one_le_div hkR_pos).mpr (by exact_mod_cast hkN)
    have he : (1 : ℝ) ≤ Real.exp 1 := by
      have h := Real.add_one_le_exp (1 : ℝ)
      norm_num at h
      linarith
    calc (n : ℝ) * Real.exp 1 / k = (n / k) * Real.exp 1 := by
          rw [mul_div_right_comm]
      _ ≥ 1 * 1 := mul_le_mul hnk he zero_le_one (zero_le_one.trans hnk)
      _ = 1 := one_mul 1
  -- Chain of inequalities.
  refine hcount.trans (hsum.trans ?_)
  have hC1 : (1 : ℝ) ≤ 2 * Real.exp 1 / δ := hbase1.trans hbase
  calc ((n : ℝ) * Real.exp 1 / k) ^ k
      ≤ (2 * Real.exp 1 / δ) ^ k :=
        pow_le_pow_left₀ (zero_le_one.trans hbase1) hbase _
    _ = (2 * Real.exp 1 / δ) ^ ((k : ℝ)) := by
        rw [Real.rpow_natCast]
    _ ≤ (2 * Real.exp 1 / δ) ^ (δ * n) :=
        Real.rpow_le_rpow_of_exponent_le hC1 hkR_le
    _ = (2 : ℝ) ^ (δ * n * Real.logb 2 (2 * Real.exp 1 / δ)) := by
        have hC0 : (0 : ℝ) < 2 * Real.exp 1 / δ := by positivity
        conv_lhs =>
          rw [← Real.rpow_logb (by norm_num : (0:ℝ) < 2) (by norm_num) hC0]
        rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
        congr 1
        ring
    _ ≤ (2 : ℝ) ^ (ε * n) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
        have h := mul_le_mul_of_nonneg_right hδε hn0
        linarith [h]

end JSP000728
