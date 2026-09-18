import JSPProblem.Ladder
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith

/-!
# JSP-000728 — sharp Pell-root bound on `ladSets`

The ladder independent-set count `a(L) = (ladSets L).card` satisfies
`a(L+2) = 2·a(L+1) + a(L)`, whose characteristic root is the Pell
number `ρ = 1 + √2`, satisfying `ρ² = 2ρ + 1` exactly.  Unlike the
integer-normalised bound `a(L) ≤ 3·(5/2)^{L-1}` of
`ladSets_card_mul_two_pow_le` (which uses the suboptimal ratio `5/2`),
two-step induction against `5/4 · ρ^L` closes with **no slack**:

  `a(k+2) = 2a(k+1) + a(k) ≤ 5/4 · (2ρ^{k+1} + ρ^k)
          = 5/4 · ρ^k · (2ρ + 1) = 5/4 · ρ^{k+2}`.

The constant `5/4` absorbs the base cases: `a(0) = 1 ≤ 5/4` and
`a(1) = 3 ≤ 5/4·(1 + √2)` (since `√2 ≥ 1.4`).

* `pell_root_sq` : `(1 + √2)² = 2(1 + √2) + 1`.
* `sqrt_two_ge_one_point_four` : `1.4 ≤ √2`.
* `ladSets_card_le_pell_pow` : `a(L) ≤ 5/4 · (1 + √2)^L`.
* `ladSets_card_le_pell_pow_succ` : the looser `a(L) ≤ (1 + √2)^{L+1}`.
-/

namespace JSP000728

/-- The characteristic root `ρ = 1 + √2` of the ladder recurrence
satisfies `ρ² = 2ρ + 1` exactly. -/
theorem pell_root_sq :
    (1 + Real.sqrt 2) ^ 2 = 2 * (1 + Real.sqrt 2) + 1 := by
  have h2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  calc (1 + Real.sqrt 2) ^ 2
      = 1 + 2 * Real.sqrt 2 + (Real.sqrt 2) ^ 2 := by ring
    _ = 2 * (1 + Real.sqrt 2) + 1 := by rw [h2]; ring

/-- `√2 ≥ 1.4`, used for the `L = 1` base case. -/
theorem sqrt_two_ge_one_point_four : (1.4 : ℝ) ≤ Real.sqrt 2 := by
  rw [Real.le_sqrt' (by norm_num : (0 : ℝ) < 1.4)]
  norm_num

/-- **Sharp Pell-root bound.**  `a(L) ≤ 5/4 · (1 + √2)^L`, proved by
two-step induction; the step uses `ρ² = 2ρ + 1` with no slack. -/
theorem ladSets_card_le_pell_pow (L : ℕ) :
    ((ladSets L).card : ℝ) ≤ 5 / 4 * (1 + Real.sqrt 2) ^ L := by
  induction L using Nat.twoStepInduction with
  | zero =>
      have h0 : ((ladSets 0).card : ℝ) = 1 := by
        exact_mod_cast ladSets_card_zero
      rw [h0, pow_zero]
      norm_num
  | one =>
      have h1 : ((ladSets 1).card : ℝ) = 3 := by
        exact_mod_cast ladSets_card_one
      rw [h1, pow_one]
      linarith [sqrt_two_ge_one_point_four]
  | more k ih ih1 =>
      have hrec : ((ladSets (k + 2)).card : ℝ) =
          2 * ((ladSets (k + 1)).card : ℝ) + (ladSets k).card := by
        exact_mod_cast ladSets_card_add_two k
      calc ((ladSets (k + 2)).card : ℝ)
          = 2 * (ladSets (k + 1)).card + (ladSets k).card := hrec
        _ ≤ 2 * (5 / 4 * (1 + Real.sqrt 2) ^ (k + 1)) +
              5 / 4 * (1 + Real.sqrt 2) ^ k :=
            add_le_add
              (mul_le_mul_of_nonneg_left ih1 (by norm_num)) ih
        _ = 5 / 4 * (1 + Real.sqrt 2) ^ (k + 2) := by
            have e1 : (1 + Real.sqrt 2) ^ (k + 1) =
                (1 + Real.sqrt 2) * (1 + Real.sqrt 2) ^ k :=
              pow_succ' _ _
            have e2 : (1 + Real.sqrt 2) ^ (k + 2) =
                (1 + Real.sqrt 2) ^ k * (1 + Real.sqrt 2) ^ 2 :=
              pow_add _ _ _
            rw [e1, e2, pell_root_sq]
            ring

/-- Looser corollary: `a(L) ≤ (1 + √2)^{L+1}`. -/
theorem ladSets_card_le_pell_pow_succ (L : ℕ) :
    ((ladSets L).card : ℝ) ≤ (1 + Real.sqrt 2) ^ (L + 1) := by
  have hρ : (0 : ℝ) ≤ 1 + Real.sqrt 2 :=
    add_nonneg zero_le_one (Real.sqrt_nonneg 2)
  have h54 : (5 : ℝ) / 4 ≤ 1 + Real.sqrt 2 := by
    linarith [sqrt_two_ge_one_point_four]
  calc ((ladSets L).card : ℝ)
      ≤ 5 / 4 * (1 + Real.sqrt 2) ^ L := ladSets_card_le_pell_pow L
    _ ≤ (1 + Real.sqrt 2) ^ (L + 1) := by
        rw [pow_succ']
        exact mul_le_mul_of_nonneg_right h54 (pow_nonneg hρ L)

end JSP000728
