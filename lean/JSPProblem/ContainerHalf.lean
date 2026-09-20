import JSPProblem.BMSContainer
import JSPProblem.Removal
import JSPProblem.SparseCard

/-!
# JSP-000728 — container existence alone gives the `1/2` bound

`SparseCard.card_le_half_add_of_schurTripleCount_le` proves the size
component of the stability lemma elementarily: a container with at most
`δ·n²` Schur triples has at most `(1/2 + ε)·n` elements.  This removes the
Schur removal lemma from the constant-`1/2` route: `ContainerExistence`
alone yields `f(n) ≤ 2^{(1/2 + o(1)) n}`, i.e. `EventualRatioUpper (1/2)`.

(The removal lemma — or the finer `C = A ∪ B` decomposition — is still
needed for the sharp constant `1/4`, since the `1/4` comes from the
per-container maximal-set count, not from `|C|` alone.)
-/

namespace JSP000728

/-- **Constant-`1/2` bound from container existence alone.**  Applying
`ContainerExistence (ε/4) δ` with `δ` from
`card_le_half_add_of_schurTripleCount_le (ε/4)` yields, eventually, a family
`F` with `F.card ≤ 2^{(ε/4) n}` whose members satisfy
`C.card ≤ (1/2 + ε/4)·n`; this is a good container family with
`K = ⌈(1/2 + ε/4) n⌉₊`, giving `f(n) ≤ 2^{(1/2 + ε/2) n + 1}`. -/
theorem eventualRatioUpper_half_of_containerExistence
    (hCE : ContainerExistence) : EventualRatioUpper (1 / 2) := by
  intro ε hε
  have hε4 : 0 < ε / 4 := by linarith
  obtain ⟨δ, hδ, hcard⟩ := card_le_half_add_of_schurTripleCount_le hε4
  have hcont := hCE (ε / 4) hε4 δ hδ
  filter_upwards [hcard, hcont, Filter.eventually_ge_atTop ⌈3 / ε⌉₊]
    with n hcardn hcontn hnN
  obtain ⟨F, hFfam, hFcard, hFtr⟩ := hcontn
  have hnR : (0 : ℝ) < (n : ℝ) := by
    have hNpos : 0 < ⌈3 / ε⌉₊ := Nat.ceil_pos.mpr (by positivity)
    exact_mod_cast hNpos.trans_le hnN
  -- The size cap on containers: `K = ⌈(1/2 + ε/4)·n⌉₊`.
  set x : ℝ := (1 / 2 + ε / 4) * (n : ℝ) with hx
  set K : ℕ := ⌈x⌉₊ with hK
  have hxnonneg : 0 ≤ x := by
    rw [hx]
    exact mul_nonneg (by linarith) (Nat.cast_nonneg n)
  have hgood : IsGoodContainerFamily n F K := by
    refine ⟨hFfam, fun C hC => ?_⟩
    have hCx : (C.card : ℝ) ≤ x :=
      hcardn C (hFfam.1 C hC) (hFtr C hC)
    exact Nat.cast_le.mp (hCx.trans (Nat.le_ceil x))
  have hcountℕ : maxSumFreeCount n ≤ F.card * 2 ^ K :=
    maxSumFreeCount_le_of_good hgood
  have h2pos : (0 : ℝ) < 2 := by norm_num
  -- Real-valued count: `f(n) ≤ 2^{(ε/4) n} · 2^{x + 1}`.
  have hcount : (maxSumFreeCount n : ℝ) ≤ (F.card : ℝ) * (2 : ℝ) ^ (K : ℝ) := by
    calc (maxSumFreeCount n : ℝ)
        ≤ (F.card : ℝ) * (2 : ℝ) ^ (K : ℕ) := by exact_mod_cast hcountℕ
      _ = (F.card : ℝ) * (2 : ℝ) ^ (K : ℝ) := by rw [Real.rpow_natCast]
  have hKle : (K : ℝ) ≤ x + 1 := (Nat.ceil_lt_add_one hxnonneg).le
  have hpow : (2 : ℝ) ^ (K : ℝ) ≤ (2 : ℝ) ^ (x + 1) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hKle
  have hmul : (F.card : ℝ) * (2 : ℝ) ^ (K : ℝ) ≤
      (2 : ℝ) ^ ((ε / 4) * (n : ℝ)) * (2 : ℝ) ^ (x + 1) :=
    mul_le_mul hFcard hpow (Real.rpow_nonneg h2pos.le _)
      (Real.rpow_nonneg h2pos.le _)
  have hexp : (ε / 4) * (n : ℝ) + (x + 1) =
      (1 / 2 + ε / 2) * (n : ℝ) + 1 := by
    rw [hx]; ring
  have hbound : (maxSumFreeCount n : ℝ) ≤
      (2 : ℝ) ^ ((1 / 2 + ε / 2) * (n : ℝ) + 1) := by
    calc (maxSumFreeCount n : ℝ)
        ≤ (2 : ℝ) ^ ((ε / 4) * (n : ℝ)) * (2 : ℝ) ^ (x + 1) :=
          hcount.trans hmul
      _ = (2 : ℝ) ^ ((ε / 4) * (n : ℝ) + (x + 1)) := by
          rw [← Real.rpow_add h2pos]
      _ = (2 : ℝ) ^ ((1 / 2 + ε / 2) * (n : ℝ) + 1) := by rw [hexp]
  -- Take `log₂` and divide by `n ≥ 3/ε`.
  have hpos : (0 : ℝ) < (maxSumFreeCount n : ℝ) := by
    exact_mod_cast maxSumFreeCount_pos n
  have hlog : Real.logb 2 (maxSumFreeCount n : ℝ) ≤
      (1 / 2 + ε / 2) * (n : ℝ) + 1 := by
    calc Real.logb 2 (maxSumFreeCount n : ℝ)
        ≤ Real.logb 2 ((2 : ℝ) ^ ((1 / 2 + ε / 2) * (n : ℝ) + 1)) :=
          (Real.logb_le_logb (by norm_num) hpos
            (Real.rpow_pos_of_pos h2pos _)).mpr hbound
      _ = (1 / 2 + ε / 2) * (n : ℝ) + 1 :=
          Real.logb_rpow h2pos (by norm_num : (2 : ℝ) ≠ 1)
  have htail : (1 : ℝ) / (n : ℝ) ≤ ε / 2 := by
    have hn3 : (3 : ℝ) / ε ≤ (n : ℝ) :=
      (Nat.le_ceil _).trans (Nat.cast_le.mpr hnN)
    have h3 : (3 : ℝ) ≤ (n : ℝ) * ε := (div_le_iff₀ hε).mp hn3
    rw [div_le_iff₀ hnR]
    linarith
  calc Real.logb 2 (maxSumFreeCount n : ℝ) / (n : ℝ)
      ≤ ((1 / 2 + ε / 2) * (n : ℝ) + 1) / (n : ℝ) :=
        div_le_div_of_nonneg_right hlog hnR.le
    _ = (1 / 2 + ε / 2) + 1 / (n : ℝ) := by
        rw [add_div, mul_div_cancel_right₀ _ hnR.ne']
    _ ≤ 1 / 2 + ε := by linarith [htail]

/-- **Unconditional `1/2` bound.**  With `containerExistence` proved,
`ContainerExistence` holds outright, so `f(n) ≤ 2^{(1/2 + o(1)) n}` is an
unconditional theorem. -/
theorem eventualRatioUpper_half : EventualRatioUpper (1 / 2) :=
  eventualRatioUpper_half_of_containerExistence containerExistence

end JSP000728
