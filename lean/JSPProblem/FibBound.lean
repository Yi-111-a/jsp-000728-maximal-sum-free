import JSPProblem.NoConsec
import JSPProblem.MinDecomp
import JSPProblem.AsymptoticReduction
import JSPProblem.UpperHalf
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# JSP-000728 — the Fibonacci-path bound

The elementary upper bound `limsup log₂ f(n) / n ≤ log₂ φ ≈ 0.6942`, where
`f n = maxSumFreeCount n` and `φ = Real.goldenRatio`.

* `fib_le_goldenRatio_pow` : `F_{k+1} ≤ φ^k`, by two-step induction using
  `φ² = φ + 1`.
* `minClass_card_le_sf_Icc` : deleting the minimum injects `minClass n m`
  into the shift-free subsets of `Icc (m+1) n`.
* `minClass_card_le` : `#minClass n m ≤ φ^n`, combining the class
  factorisation and the progression count `F_{L+2} ≤ φ^{L+1}`.
* `maxSumFreeCount_le_goldenRatio` : `f n ≤ n·φ^n`.
* `logb_maxSumFreeCount_le` : `log₂ f(n) ≤ log₂ n + n·log₂ φ`.
* `eventualRatioUpper_goldenRatio` : the headline, since `log₂ n / n → 0`.
-/

namespace JSP000728

/-- `F_{k+1} ≤ φ^k` for the golden ratio `φ`. -/
theorem fib_le_goldenRatio_pow (k : ℕ) :
    (Nat.fib (k + 1) : ℝ) ≤ Real.goldenRatio ^ k := by
  induction k using Nat.twoStepInduction with
  | zero => simp [Nat.fib_one]
  | one =>
      have h : (Nat.fib 2 : ℝ) = 1 := by exact_mod_cast Nat.fib_two
      rw [h, pow_one]
      exact Real.one_lt_goldenRatio.le
  | more k ih ih1 =>
      show (Nat.fib (k + 1 + 2) : ℝ) ≤ Real.goldenRatio ^ (k + 2)
      rw [Nat.fib_add_two]
      push_cast
      calc (Nat.fib (k + 1) : ℝ) + (Nat.fib (k + 2) : ℝ)
          ≤ Real.goldenRatio ^ k + Real.goldenRatio ^ (k + 1) :=
            add_le_add ih ih1
        _ = Real.goldenRatio ^ k * (1 + Real.goldenRatio) := by
            rw [pow_succ]; ring
        _ = Real.goldenRatio ^ k * Real.goldenRatio ^ 2 := by
            congr 1
            rw [add_comm, Real.goldenRatio_sq]
        _ = Real.goldenRatio ^ (k + 2) := by
            rw [← pow_add]

/-- Removing the minimum maps `minClass n m` injectively into the shift-free
subsets of `Icc (m+1) n`. -/
theorem minClass_card_le_sf_Icc {n : ℕ} {m : ℤ} :
    (minClass n m).card ≤
      ((Finset.Icc (m + 1) (n : ℤ)).powerset.filter (shiftFree m)).card := by
  refine Finset.card_le_card_of_injOn (fun M => M.erase m) ?_ ?_
  · intro M hM
    rw [Finset.mem_coe, mem_minClass] at hM
    obtain ⟨hmax, hmM, hmin⟩ := hM
    have hMmax : IsMaxSumFree n M := mem_maxSumFreeSets.mp hmax
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset]
    refine ⟨?_, ?_⟩
    · intro x hx
      rw [Finset.mem_erase] at hx
      have hxint := Finset.mem_Icc.mp (hMmax.1 hx.2)
      rw [Finset.mem_Icc]
      exact ⟨by have := hmin x hx.2; omega, hxint.2⟩
    · intro x hx hxm
      rw [Finset.mem_erase] at hx hxm
      exact not_mem_add_min_of_isMaxSumFree hMmax hmM hx.2 hxm.2
  · intro M₁ hM₁ M₂ hM₂ h
    rw [Finset.mem_coe, mem_minClass] at hM₁ hM₂
    have h' : M₁.erase m = M₂.erase m := h
    rw [← Finset.insert_erase hM₁.2.1, ← Finset.insert_erase hM₂.2.1, h']

/-- The `φ^n` bound for each minimum class (real version). -/
theorem minClass_card_le_goldenRatio {n : ℕ} {m : ℤ} (hm : m ∈ Finset.Icc 1 (n : ℤ)) :
    ((minClass n m).card : ℝ) ≤ Real.goldenRatio ^ n := by
  rw [Finset.mem_Icc] at hm
  have hA := minClass_card_le_sf_Icc (n := n) (m := m)
  have hB : ((Finset.Icc (m + 1) (n : ℤ)).powerset.filter (shiftFree m)).card ≤
      ∏ r ∈ Finset.Icc 1 m, ((cls n m r).powerset.filter (shiftFree m)).card :=
    card_powerset_filter_shiftFree_le_prod (Finset.Icc 1 m) (cls n m)
      (Finset.Icc (m + 1) (n : ℤ)) (Icc_subset_biUnion_cls hm.1)
  have hC : (minClass n m).card ≤
      ∏ r ∈ Finset.Icc 1 m, Nat.fib ((((n : ℤ) - r) / m).toNat + 2) :=
    hA.trans (hB.trans (Finset.prod_le_prod fun r _ =>
      le_of_eq (card_powerset_filter_shiftFree_cls hm.1)))
  calc ((minClass n m).card : ℝ)
      ≤ ∏ r ∈ Finset.Icc 1 m,
          (Nat.fib ((((n : ℤ) - r) / m).toNat + 2) : ℝ) := by
        exact_mod_cast hC
    _ ≤ ∏ r ∈ Finset.Icc 1 m,
          Real.goldenRatio ^ ((((n : ℤ) - r) / m).toNat + 1) := by
        apply Finset.prod_le_prod₀
        · intro r _
          exact Nat.cast_nonneg _
        · intro r _
          exact fib_le_goldenRatio_pow _
    _ = Real.goldenRatio ^ n := by
        rw [Finset.prod_pow_eq_pow_sum]
        congr 1
        rw [Finset.sum_add_distrib, Finset.sum_const, sum_cls_card hm.1,
          Int.card_Icc]
        simp only [smul_eq_mul, mul_one]
        omega

/-- The global bound `f n ≤ n·φ^n`. -/
theorem maxSumFreeCount_le_goldenRatio {n : ℕ} (hn : 1 ≤ n) :
    (maxSumFreeCount n : ℝ) ≤ n * Real.goldenRatio ^ n := by
  have hsum : (maxSumFreeCount n : ℝ) =
      ∑ m ∈ Finset.Icc 1 (n : ℤ), ((minClass n m).card : ℝ) := by
    rw [maxSumFreeCount_eq_sum_minClass hn]
    exact Nat.cast_sum _ _
  rw [hsum]
  calc ∑ m ∈ Finset.Icc 1 (n : ℤ), ((minClass n m).card : ℝ)
      ≤ ∑ m ∈ Finset.Icc 1 (n : ℤ), Real.goldenRatio ^ n :=
        Finset.sum_le_sum fun m hm => minClass_card_le_goldenRatio hm
    _ = (Finset.Icc 1 (n : ℤ)).card * Real.goldenRatio ^ n := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = n * Real.goldenRatio ^ n := by
        rw [Int.card_Icc]
        congr 1
        simp

/-- The logarithmic bound `log₂ f(n) ≤ log₂ n + n·log₂ φ`. -/
theorem logb_maxSumFreeCount_le {n : ℕ} (hn : 1 ≤ n) :
    Real.logb 2 (maxSumFreeCount n : ℝ) ≤
      Real.logb 2 n + n * Real.logb 2 Real.goldenRatio := by
  have hpos : (0 : ℝ) < maxSumFreeCount n :=
    Nat.cast_pos.mpr (maxSumFreeCount_pos n)
  have hle := maxSumFreeCount_le_goldenRatio hn
  have h2 := Real.logb_le_logb_of_le (b := 2) (by norm_num) hpos hle
  rw [Real.logb_mul (Nat.cast_ne_zero.mpr (by omega))
    (ne_of_gt (pow_pos Real.goldenRatio_pos n)), Real.logb_pow] at h2
  exact h2

/-- `log₂ n / n → 0` as `n → ∞` through the naturals. -/
theorem tendsto_logb_div :
    Filter.Tendsto (fun n : ℕ => Real.logb 2 (n : ℝ) / (n : ℝ))
      Filter.atTop (nhds 0) := by
  have h : Filter.Tendsto (fun x : ℝ => Real.logb 2 x / x)
      Filter.atTop (nhds 0) := by
    have h := (Real.isLittleO_logb_id_atTop (b := 2)).tendsto_div_nhds_zero
    simpa only [id] using h
  exact h.comp tendsto_natCast_atTop_atTop

/-- **Headline.**  `limsup log₂ f(n) / n ≤ log₂ φ`. -/
theorem eventualRatioUpper_goldenRatio :
    EventualRatioUpper (Real.logb 2 Real.goldenRatio) := by
  intro ε hε
  have h0 : ∀ᶠ n : ℕ in Filter.atTop, Real.logb 2 (n : ℝ) / (n : ℝ) < ε :=
    tendsto_logb_div.eventually (Iio_mem_nhds hε)
  filter_upwards [h0, Filter.eventually_ge_atTop 1] with n hn' hn
  have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have hdiv := div_le_div_of_nonneg_right (logb_maxSumFreeCount_le hn) hnR.le
  rw [add_div, mul_div_cancel_left₀ _ hn0] at hdiv
  linarith

end JSP000728
