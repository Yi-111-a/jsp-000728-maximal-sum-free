import JSPProblem.MinDecomp
import JSPProblem.DeterminedMinClass
import JSPProblem.FibBound
import JSPProblem.Asymptotic
import JSPProblem.TwoMin
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Data.Int.Interval

/-!
# JSP-000728 — reduction of `EventualRatioUpper` to the small-minimum frontier

By `maxSumFreeCount_eq_sum_minClass`, the number `f n = maxSumFreeCount n` of
inclusion-maximal sum-free subsets of `{1,…,n}` splits into the classes
`minClass n m` grouped by their minimum `m`.  This file shows that the
**only** exponentially-relevant part of that decomposition is the
*small-minimum frontier* `4 * m < n`:

* `minClass_card_le_two_pow_half` — for `4 * m ≥ n` the Cameron–Erdős/
  Wolfovitz determination bound `minClass_card_le_two_pow_determined`
  collapses to `(minClass n m).card ≤ 2 ^ (n/2 + 1)`, since the trace
  `M ∩ {m,…,n−m}` then has at most `n/2 + 1` elements.

* `maxSumFreeCount_le_smallMin_add` — the assembly bound

    `f n ≤ smallMinSum n + n · 2 ^ (n/2 + 1)`

  where `smallMinSum n = ∑_{m ∈ [1,n], 4m < n} (minClass n m).card`: the
  `m ≥ n/4` region contributes at most `poly(n) · 2^(n/2)`.

* `SmallMinBound c` — the packaged frontier hypothesis: for every `ε > 0`
  there is a constant `C` with `smallMinSum n ≤ C · 2^((c + ε) n)`
  eventually.  `eventualRatioUpper_of_smallMinBound` proves

    `SmallMinBound c → EventualRatioUpper (max c (1/2))`:

  the `n · 2^(n/2+1)` remainder is absorbed by the `1/2` term, so any
  eventual bound on the small-minimum classes with exponent `c` upgrades
  to `limsup log₂ f(n)/n ≤ max c (1/2)`.

* `smallMinBound_of_uniform` — the hypothesis is discharged by any
  *uniform* per-class bound `(minClass n m).card ≤ 2^((c + ε) n)` on the
  frontier classes, since at most `n` classes enter the sum and
  `n ≤ 2^(ε n)` eventually.  This is the form a future refined
  `secondMinClass` / ladder analysis can plug into.

Note the `1/2` ceiling is genuine at this level: the determination bound
is essentially sharp for `m ≈ n/4` (the sum `∑_{m ≥ n/4} 2^{n−2m+1}` is
dominated by the `m = ⌈n/4⌉` term `≈ 2^{n/2}`), so this assembly layer
alone cannot beat `log₂ f(n)/n ≤ 1/2` — improving the constant further
requires a bound on `smallMinSum` itself with `c < 1/2`, i.e. real input
about the small-minimum classes.
-/

namespace JSP000728

/-- **The small-minimum frontier.**  The sum of `(minClass n m).card` over
the classes whose minimum satisfies `4 * m < n`.  Every exponential bound
on `maxSumFreeCount` reduces to bounding this sum, since the complementary
region `4 * m ≥ n` contributes only `poly(n) · 2^(n/2)`
(`maxSumFreeCount_le_smallMin_add`). -/
def smallMinSum (n : ℕ) : ℕ :=
  ∑ m ∈ (Finset.Icc 1 (n : ℤ)).filter (fun m => 4 * m < (n : ℤ)),
    (minClass n m).card

/-- **Half-range determination bound.**  If `4 * m ≥ n`, the determination
bound `minClass_card_le_two_pow_determined` gives
`(minClass n m).card ≤ 2 ^ (n / 2 + 1)`: from `4m ≥ n` one gets
`2m ≥ ⌈n/2⌉`, hence `n − 2m + 1 ≤ n/2 + 1` (with `n/2` the natural
floor-division). -/
theorem minClass_card_le_two_pow_half {n : ℕ} {m : ℤ}
    (hm : (n : ℤ) ≤ 4 * m) :
    (minClass n m).card ≤ 2 ^ (n / 2 + 1) := by
  refine minClass_card_le_two_pow_determined.trans
    (pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) ?_)
  have hle : (n : ℤ) - 2 * m + 1 ≤ ((n / 2 : ℕ) : ℤ) + 1 := by
    have h2 : n % 2 < 2 := by omega
    have h := Nat.div_add_mod n 2
    omega
  exact Int.toNat_le.mpr (by exact_mod_cast hle)

/-- The large-minimum region `4 * m ≥ n` of the decomposition contributes
at most `n · 2 ^ (n/2 + 1)` — at most `n` classes, each bounded by
`minClass_card_le_two_pow_half`. -/
theorem sum_minClass_large_le {n : ℕ} :
    ∑ m ∈ (Finset.Icc 1 (n : ℤ)).filter (fun m => ¬ 4 * m < (n : ℤ)),
        (minClass n m).card ≤ n * 2 ^ (n / 2 + 1) := by
  calc ∑ m ∈ (Finset.Icc 1 (n : ℤ)).filter (fun m => ¬ 4 * m < (n : ℤ)),
        (minClass n m).card
      ≤ ∑ m ∈ (Finset.Icc 1 (n : ℤ)).filter (fun m => ¬ 4 * m < (n : ℤ)),
          2 ^ (n / 2 + 1) :=
        Finset.sum_le_sum fun m hm =>
          minClass_card_le_two_pow_half
            (le_of_not_gt (Finset.mem_filter.mp hm).2)
    _ = ((Finset.Icc 1 (n : ℤ)).filter
          (fun m => ¬ 4 * m < (n : ℤ))).card * 2 ^ (n / 2 + 1) := by
        simp
    _ ≤ n * 2 ^ (n / 2 + 1) := by
        apply Nat.mul_le_mul_right
        refine (Finset.card_filter_le _ _).trans ?_
        rw [Int.card_Icc]
        simp

/-- **Assembly bound (natural form).**  Splitting the minimum decomposition
at `4 * m = n`,

    `f n ≤ smallMinSum n + n · 2 ^ (n/2 + 1)`:

the large-minimum region is `poly(n) · 2^(n/2)`, so the exponential rate of
`f n` is governed entirely by the small-minimum frontier. -/
theorem maxSumFreeCount_le_smallMin_add {n : ℕ} (hn : 1 ≤ n) :
    maxSumFreeCount n ≤ smallMinSum n + n * 2 ^ (n / 2 + 1) := by
  rw [maxSumFreeCount_eq_sum_minClass hn]
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 (n : ℤ))
      (fun m => 4 * m < (n : ℤ)) (fun m => (minClass n m).card)]
  exact add_le_add le_rfl sum_minClass_large_le

/-- **Assembly bound (real form).** -/
theorem maxSumFreeCount_le_smallMin_add_real {n : ℕ} (hn : 1 ≤ n) :
    (maxSumFreeCount n : ℝ) ≤
      (smallMinSum n : ℝ) + (n : ℝ) * (2 : ℝ) ^ (n / 2 + 1) := by
  exact_mod_cast maxSumFreeCount_le_smallMin_add hn

/-- **The small-minimum hypothesis.**  `SmallMinBound c` says the frontier
sum is eventually bounded by `C · 2 ^ ((c + ε) * n)` for every `ε > 0`,
with `C` a constant (depending on `ε` but not on `n`).  Equivalently,
`limsup log₂ (smallMinSum n) / n ≤ c`.  This is the form a future uniform
per-class bound on `minClass n m` for `4m < n` can discharge
(`smallMinBound_of_uniform`). -/
def SmallMinBound (c : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ᶠ n : ℕ in Filter.atTop,
    (smallMinSum n : ℝ) ≤ C * (2 : ℝ) ^ ((c + ε) * (n : ℝ))

/-- Any constant `D` is eventually dominated by `2 ^ (δ * n)` for `δ > 0`. -/
theorem eventually_le_two_pow_mul {δ : ℝ} (hδ : 0 < δ) (D : ℝ) :
    ∀ᶠ n : ℕ in Filter.atTop, D ≤ (2 : ℝ) ^ (δ * (n : ℝ)) := by
  have hD : (0 : ℝ) < max D 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  filter_upwards
    [Filter.eventually_ge_atTop (Nat.ceil (Real.logb 2 (max D 1) / δ))]
    with n hn
  have h1 : Real.logb 2 (max D 1) ≤ δ * (n : ℝ) := by
    have hceil : (Nat.ceil (Real.logb 2 (max D 1) / δ) : ℝ) ≤ (n : ℝ) :=
      by exact_mod_cast hn
    have hle : Real.logb 2 (max D 1) / δ ≤ (n : ℝ) :=
      (Nat.le_ceil _).trans hceil
    have hle' := (div_le_iff₀ hδ).mp hle
    rwa [mul_comm] at hle'
  calc D ≤ max D 1 := le_max_left _ _
    _ = (2 : ℝ) ^ (Real.logb 2 (max D 1)) :=
        (Real.rpow_logb (by norm_num : (0 : ℝ) < 2) (by norm_num) hD).symm
    _ ≤ (2 : ℝ) ^ (δ * (n : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) h1

/-- The variable `n` itself is eventually dominated by `2 ^ (δ * n)`:
`log₂ n / n → 0` gives `log₂ n ≤ δ n` eventually. -/
theorem eventually_natCast_le_two_pow_mul {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in Filter.atTop, (n : ℝ) ≤ (2 : ℝ) ^ (δ * (n : ℝ)) := by
  have h1 : ∀ᶠ n : ℕ in Filter.atTop,
      Real.logb 2 (n : ℝ) / (n : ℝ) < δ :=
    tendsto_logb_div.eventually (Iio_mem_nhds hδ)
  filter_upwards [h1, Filter.eventually_ge_atTop 1] with n a hn
  have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have al : Real.logb 2 (n : ℝ) < δ * (n : ℝ) := (div_lt_iff₀ hnR).mp a
  calc (n : ℝ) = (2 : ℝ) ^ (Real.logb 2 (n : ℝ)) :=
      (Real.rpow_logb (by norm_num : (0 : ℝ) < 2) (by norm_num) hnR).symm
    _ ≤ (2 : ℝ) ^ (δ * (n : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) al.le

/-- The large-minimum aggregate `n · 2 ^ (n/2 + 1)` is eventually absorbed
by `2 ^ ((1/2 + δ) n)`: its logarithm is
`log₂ n + ⌊n/2⌋ + 1 ≤ n/2 + δ n` eventually, since `log₂ n + 1 < δ n`
eventually. -/
theorem eventually_mul_two_pow_half_le {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in Filter.atTop,
      (n : ℝ) * (2 : ℝ) ^ (n / 2 + 1) ≤ (2 : ℝ) ^ ((1 / 2 + δ) * (n : ℝ)) := by
  have h1 : ∀ᶠ n : ℕ in Filter.atTop,
      Real.logb 2 (n : ℝ) / (n : ℝ) < δ / 2 :=
    tendsto_logb_div.eventually (Iio_mem_nhds (by linarith))
  have h2 : ∀ᶠ n : ℕ in Filter.atTop, (1 : ℝ) / (n : ℝ) < δ / 2 := by
    obtain ⟨N, hN⟩ := exists_nat_gt (4 / δ)
    have hNpos : (0 : ℝ) < (N : ℝ) := by
      have hδ' : (0 : ℝ) < 4 / δ := by positivity
      exact hδ'.trans hN
    filter_upwards [Filter.eventually_ge_atTop N] with n hn
    have hnR : (0 : ℝ) < (n : ℝ) := hNpos.trans_le (by exact_mod_cast hn)
    have hNle : (4 : ℝ) / δ ≤ (n : ℝ) := le_trans hN.le (by exact_mod_cast hn)
    have h4 : (4 : ℝ) ≤ (n : ℝ) * δ := (div_le_iff₀ hδ).mp hNle
    rw [div_lt_iff₀ hnR]
    linarith
  filter_upwards [h1, h2, Filter.eventually_ge_atTop 1] with n a b hn
  have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hL : (0 : ℝ) < (n : ℝ) * (2 : ℝ) ^ (n / 2 + 1) := by positivity
  refine (Real.logb_le_logb (by norm_num : (1 : ℝ) < 2) hL
    (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _)).mp ?_
  rw [Real.logb_mul (ne_of_gt hnR) (pow_ne_zero _ (by norm_num : (2:ℝ) ≠ 0)),
    Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one,
    Real.logb_rpow (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)]
  -- Goal: `log₂ n + ↑(n/2 + 1) ≤ (1/2 + δ) * n`.
  have hcast : ((n / 2 + 1 : ℕ) : ℝ) ≤ (n : ℝ) / 2 + 1 := by
    have h := Nat.cast_div_le (α := ℝ) (m := n) (n := 2)
    push_cast
    linarith [h]
  have al : Real.logb 2 (n : ℝ) < δ / 2 * (n : ℝ) := (div_lt_iff₀ hnR).mp a
  have bl : (1 : ℝ) < δ / 2 * (n : ℝ) := (div_lt_iff₀ hnR).mp b
  have hlog : Real.logb 2 (n : ℝ) + 1 < δ * (n : ℝ) := by linarith
  have hhalf : ((n / 2 + 1 : ℕ) : ℝ) ≤ (n : ℝ) / 2 + 1 := hcast
  linarith

/-- **Conditional reduction.**  If the small-minimum frontier is eventually
bounded by `C · 2 ^ ((c + ε) n)` for every `ε > 0` (`SmallMinBound c`),
then `EventualRatioUpper (max c (1/2))`: the `4m ≥ n` region contributes
at most `n · 2 ^ (n/2+1) ≤ 2 ^ ((1/2 + ε/2) n)` eventually, the constant
`C` is absorbed by `2 ^ ((ε/4) n)`, and `f n ≤ 2 · 2 ^ ((max c (1/2) + ε/2) n)`
gives `log₂ f(n)/n ≤ max c (1/2) + ε/2 + 1/n ≤ max c (1/2) + ε`. -/
theorem eventualRatioUpper_of_smallMinBound {c : ℝ} (h : SmallMinBound c) :
    EventualRatioUpper (max c (1 / 2)) := by
  intro ε hε
  have hε2 : (0 : ℝ) < ε / 2 := by linarith
  have hε4 : (0 : ℝ) < ε / 4 := by linarith
  obtain ⟨C, hC⟩ := h (ε / 4) hε4
  have hCabs := eventually_le_two_pow_mul hε4 (max C 1)
  have hlarge := eventually_mul_two_pow_half_le hε2
  obtain ⟨N, hN⟩ := exists_nat_gt (2 / ε)
  filter_upwards [hC, hCabs, hlarge, Filter.eventually_ge_atTop N,
    Filter.eventually_ge_atTop 1] with n hs hCa hl hnN hn1
  have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn1
  -- Absorb the constant `C`: `smallMinSum n ≤ 2 ^ ((c + ε/2) n)`.
  have hs2 : (smallMinSum n : ℝ) ≤ (2 : ℝ) ^ ((c + ε / 2) * (n : ℝ)) := by
    calc (smallMinSum n : ℝ)
        ≤ C * (2 : ℝ) ^ ((c + ε / 4) * (n : ℝ)) := hs
      _ ≤ max C 1 * (2 : ℝ) ^ ((c + ε / 4) * (n : ℝ)) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _)
            (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
      _ ≤ (2 : ℝ) ^ ((ε / 4) * (n : ℝ)) * (2 : ℝ) ^ ((c + ε / 4) * (n : ℝ)) :=
          mul_le_mul_of_nonneg_right hCa
            (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
      _ = (2 : ℝ) ^ ((c + ε / 2) * (n : ℝ)) := by
          rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
          congr 1
          ring
  -- Split the count and compare each piece to `2 ^ ((max c (1/2) + ε/2) n)`.
  have hbound := maxSumFreeCount_le_smallMin_add_real hn1
  have he1 : (2 : ℝ) ^ ((c + ε / 2) * (n : ℝ)) ≤
      (2 : ℝ) ^ ((max c (1 / 2) + ε / 2) * (n : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (mul_le_mul_of_nonneg_right (add_le_add (le_max_left _ _) (le_refl _))
        (Nat.cast_nonneg _))
  have he2 : (2 : ℝ) ^ ((1 / 2 + ε / 2) * (n : ℝ)) ≤
      (2 : ℝ) ^ ((max c (1 / 2) + ε / 2) * (n : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (mul_le_mul_of_nonneg_right (add_le_add (le_max_right _ _) (le_refl _))
        (Nat.cast_nonneg _))
  have htot : (maxSumFreeCount n : ℝ) ≤
      2 * (2 : ℝ) ^ ((max c (1 / 2) + ε / 2) * (n : ℝ)) := by
    linarith [hbound, hs2, hl, he1, he2]
  -- Take `log₂` and divide by `n`.
  have hpos : (0 : ℝ) < (maxSumFreeCount n : ℝ) :=
    Nat.cast_pos.mpr (maxSumFreeCount_pos n)
  have hpos2 : (0 : ℝ) < 2 * (2 : ℝ) ^ ((max c (1 / 2) + ε / 2) * (n : ℝ)) := by
    positivity
  have hlog := (Real.logb_le_logb (by norm_num : (1 : ℝ) < 2) hpos hpos2).mpr htot
  rw [Real.logb_mul (by norm_num : (2 : ℝ) ≠ 0)
        (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _).ne',
      Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2),
      Real.logb_rpow (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)]
    at hlog
  have hinv : (1 : ℝ) / (n : ℝ) ≤ ε / 2 := by
    have hNle : (2 : ℝ) / ε ≤ (n : ℝ) :=
      le_trans (le_of_lt hN) (by exact_mod_cast hnN)
    have h3 : (2 : ℝ) ≤ (n : ℝ) * ε := (div_le_iff₀ hε).mp hNle
    rw [div_le_iff₀ hnR]
    linarith
  calc Real.logb 2 (maxSumFreeCount n : ℝ) / (n : ℝ)
      ≤ (1 + (max c (1 / 2) + ε / 2) * (n : ℝ)) / (n : ℝ) :=
        div_le_div_of_nonneg_right hlog hnR.le
    _ = (1 : ℝ) / (n : ℝ) + (max c (1 / 2) + ε / 2) := by
        rw [add_div, mul_div_cancel_right₀ _ hnR.ne']
    _ ≤ ε / 2 + (max c (1 / 2) + ε / 2) := by linarith [hinv]
    _ = max c (1 / 2) + ε := by ring

/-- **Discharging the hypothesis by a uniform bound.**  If every frontier
class satisfies `(minClass n m).card ≤ 2 ^ ((c + ε) n)` eventually (for
each `ε > 0`), then `SmallMinBound c` holds: at most `n` classes enter the
sum and `n ≤ 2 ^ ((ε/2) n)` eventually.  A future per-class bound — e.g.
a refined `secondMinClass`/ladder analysis uniform in `4m < n` — can plug
in here. -/
theorem smallMinBound_of_uniform {c : ℝ}
    (h : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in Filter.atTop,
      ∀ m ∈ (Finset.Icc 1 (n : ℤ)).filter (fun m => 4 * m < (n : ℤ)),
        ((minClass n m).card : ℝ) ≤ (2 : ℝ) ^ ((c + ε) * (n : ℝ))) :
    SmallMinBound c := by
  intro ε hε
  have hε2 : (0 : ℝ) < ε / 2 := by linarith
  refine ⟨1, ?_⟩
  have hu := h (ε / 2) hε2
  have hn2 := eventually_natCast_le_two_pow_mul hε2
  filter_upwards [hu, hn2, Filter.eventually_ge_atTop 1] with n hu hn2 hn1
  have hsum : (smallMinSum n : ℝ) ≤
      (n : ℝ) * (2 : ℝ) ^ ((c + ε / 2) * (n : ℝ)) := by
    have hcard : ((Finset.Icc 1 (n : ℤ)).filter
        (fun m => 4 * m < (n : ℤ))).card ≤ n := by
      refine (Finset.card_filter_le _ _).trans ?_
      rw [Int.card_Icc]
      simp
    have hsum' : (smallMinSum n : ℝ) =
        ∑ m ∈ (Finset.Icc 1 (n : ℤ)).filter (fun m => 4 * m < (n : ℤ)),
          ((minClass n m).card : ℝ) := by
      rw [smallMinSum]
      exact Nat.cast_sum _ _
    calc (smallMinSum n : ℝ)
        = ∑ m ∈ (Finset.Icc 1 (n : ℤ)).filter (fun m => 4 * m < (n : ℤ)),
            ((minClass n m).card : ℝ) := hsum'
      _ ≤ ∑ m ∈ (Finset.Icc 1 (n : ℤ)).filter (fun m => 4 * m < (n : ℤ)),
            (2 : ℝ) ^ ((c + ε / 2) * (n : ℝ)) :=
          Finset.sum_le_sum fun m hm => hu m hm
      _ = ((Finset.Icc 1 (n : ℤ)).filter (fun m => 4 * m < (n : ℤ))).card *
            (2 : ℝ) ^ ((c + ε / 2) * (n : ℝ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (n : ℝ) * (2 : ℝ) ^ ((c + ε / 2) * (n : ℝ)) := by
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by norm_num) _)
          exact_mod_cast hcard
  calc (smallMinSum n : ℝ)
      ≤ (n : ℝ) * (2 : ℝ) ^ ((c + ε / 2) * (n : ℝ)) := hsum
    _ ≤ (2 : ℝ) ^ ((ε / 2) * (n : ℝ)) * (2 : ℝ) ^ ((c + ε / 2) * (n : ℝ)) :=
        mul_le_mul_of_nonneg_right hn2 (Real.rpow_nonneg (by norm_num) _)
    _ = (2 : ℝ) ^ ((c + ε) * (n : ℝ)) := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        congr 1
        ring
    _ = 1 * (2 : ℝ) ^ ((c + ε) * (n : ℝ)) := (one_mul _).symm

end JSP000728
