import JSPProblem.LevSmel

/-!
# `LSBound` and `LSResidual` are **false as stated** — a counterexample

Take `X = {0, 3, 6}` (`lX = 6`) and `Y = {0, 1, 3, 4}` (`lY = 4`).  Every
`LSBound` hypothesis holds:

* `0, 6 ∈ X ⊆ [0, 6]`, `0, 4 ∈ Y ⊆ [0, 4]`, `lY ≤ lX`;
* the differences of `X ∪ Y = {0, 1, 3, 4, 6}` are coprime (it contains `1`),
  and likewise those of `X' ∪ Y = {0, 1, 3, 4}` where `X' = X ∖ {6} = {0, 3}`;
* `l' = max X' = 3 < lY = 4`, and the second `LSResidual` disjunct triggers:
  `min (lY + |X'|, |Y| + 2|X'| − 2) + r = min 6 6 + 2 = 8 < 9`
  `= min (lX + |Y|, |X| + 2|Y| − 2 − δ)`, where `r = lsNewX X 6 Y = 2`
  (`6 + 0 = 6 = 3 + 3` and `6 + 1 = 7 = 3 + 4` lie in `X' + Y`, while
  `9, 10` do not).

Yet `X + Y = {0, 1, 3, 4, 6, 7, 9, 10}` has cardinality `8 < 9`, so the
conclusion fails.  Hence `LSBound` (`not_lsBound`) and therefore `LSResidual`
(`not_lsResidual`, via `ls_of_lsResidual`) are both false.

## Diagnosis

The stated second branch `|X| + 2|Y| − 2 − δ` is only valid under an extra
hypothesis.  The actual Lev–Smeliansky theorem (Acta Arith. 70, 1995; see
also Stanchescu, Acta Arith. 75, Thm. 3, where the `|A| + 2|B| − 2 − δ`
branch is stated under `d(A) = 1`, the gcd of the differences of `A` *alone*)
has the bound

  `|X + Y| ≥ min (lX + |Y|, |X| + |Y| + min (|X|, |Y|) − 2 − δ)`,

equivalently `min (lX + |Y|, |X| + 2|Y| − 2 − δ)` **when `|Y| ≤ |X|`**.
The counterexample has `|Y| = 4 > 3 = |X|` and `gcd (diffs X) = 3` — only the
union `X ∪ Y` is coprime, which is too weak.  Two non-equivalent fixes:

* strengthen the coprimality hypothesis to `gcd (diffs X) = 1`
  (`∀ d ≥ 2, ∃ u v ∈ X, ¬ d ∣ u − v`), or
* weaken the second branch to `|X| + |Y| + min(|X|,|Y|) − 2 − δ`
  (`LSBoundFixed` below; verified on all `~7·10⁵` pairs with `lX ≤ 10`).

The intended application `freiman3k4Residual_of_ls` (`X = A`, `Y = l − A`)
has `|X| = |Y|` and `gcd (diffs X) = gcd (diffs A) = 1`, so it is unaffected
by either fix.
-/

namespace JSP000728

open Finset
open scoped Pointwise

/-- `u = 1, v = 0` witnesses the coprimality hypothesis whenever `1` lies in
the relevant union: no `d ≥ 2` divides `1 - 0`. -/
theorem exists_not_dvd_one_sub_zero {d : ℤ} (hd : 2 ≤ d) :
    ¬ d ∣ (1 : ℤ) - 0 := by
  intro hdvd
  have hle := Int.natAbs_le_of_dvd_ne_zero hdvd
    (by norm_num : (1 : ℤ) - 0 ≠ 0)
  have hd' : d.natAbs = d := Int.natAbs_of_nonneg (by omega)
  have : d.natAbs ≤ 1 := by simpa using hle
  omega

/-- **`LSBound` is false.**  `X = {0, 3, 6}`, `Y = {0, 1, 3, 4}` satisfies
all hypotheses but `|X + Y| = 8 < 9 = min (6 + 4, 3 + 2·4 − 2)`. -/
theorem not_lsBound : ¬ LSBound := by
  intro h
  have hcop : ∀ d : ℤ, 2 ≤ d →
      ∃ u ∈ ({0, 3, 6} : Finset ℤ) ∪ {0, 1, 3, 4},
        ∃ v ∈ ({0, 3, 6} : Finset ℤ) ∪ {0, 1, 3, 4}, ¬ d ∣ u - v := by
    intro d hd
    exact ⟨1, by decide, 0, by decide, exists_not_dvd_one_sub_zero hd⟩
  have hb := h {0, 3, 6} {0, 1, 3, 4} 6 4
    (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
    (by norm_num) hcop
  have hcX : (({0, 3, 6} : Finset ℤ).card : ℤ) = 3 := by decide
  have hcY : (({0, 1, 3, 4} : Finset ℤ).card : ℤ) = 4 := by decide
  have hcS : ((({0, 3, 6} : Finset ℤ).image₂ (· + ·) {0, 1, 3, 4}).card : ℤ) = 8 := by
    decide
  rw [hcX, hcY, hcS] at hb
  norm_num at hb

/-- **`LSResidual` is false.**  Since `ls_of_lsResidual : LSResidual → LSBound`
is already proved, the counterexample to `LSBound` yields `¬ LSResidual`
directly. -/
theorem not_lsResidual : ¬ LSResidual :=
  fun h => not_lsBound (ls_of_lsResidual h)

/-! ### The residual hypothesis is genuinely instantiated

The failure is not vacuous: the counterexample satisfies *every* `LSResidual`
hypothesis, including the second disjunct (`l' < lY` and the strict
inequality `min (lY + |X'|, |Y| + 2|X'| − 2) + r < target`).  We verify the
two computational ingredients (`r = lsNewX X 6 Y = 2`, `|X'| = 2`) and then
derive `¬ LSResidual` a second time, directly. -/

/-- The counterexample is "new-sum" count: `lsNewX {0,3,6} 6 {0,1,3,4} = 2`
(`6 + 3 = 9` and `6 + 4 = 10` escape `X' + Y = {0,1,3,4,6,7}`). -/
theorem lsNewX_cex : lsNewX {0, 3, 6} 6 {0, 1, 3, 4} = 2 := by decide

/-- Direct disproof of `LSResidual`: all hypotheses, including the second
tightness disjunct, hold for `X = {0,3,6}`, `Y = {0,1,3,4}`, `l' = 3`,
while the conclusion `9 ≤ |X + Y| = 8` fails. -/
theorem not_lsResidual' : ¬ LSResidual := by
  intro h
  have hcop : ∀ d : ℤ, 2 ≤ d →
      ∃ u ∈ ({0, 3, 6} : Finset ℤ) ∪ {0, 1, 3, 4},
        ∃ v ∈ ({0, 3, 6} : Finset ℤ) ∪ {0, 1, 3, 4}, ¬ d ∣ u - v := by
    intro d hd
    exact ⟨1, by decide, 0, by decide, exists_not_dvd_one_sub_zero hd⟩
  have hcop' : ∀ d : ℤ, 2 ≤ d →
      ∃ u ∈ ({0, 3, 6} : Finset ℤ).erase 6 ∪ {0, 1, 3, 4},
        ∃ v ∈ ({0, 3, 6} : Finset ℤ).erase 6 ∪ {0, 1, 3, 4}, ¬ d ∣ u - v := by
    intro d hd
    exact ⟨1, by decide, 0, by decide, exists_not_dvd_one_sub_zero hd⟩
  have htrig :
      min (4 + (({0, 3, 6} : Finset ℤ).erase 6).card)
          (({0, 1, 3, 4} : Finset ℤ).card +
            2 * (({0, 3, 6} : Finset ℤ).erase 6).card - 2) +
        (lsNewX {0, 3, 6} 6 {0, 1, 3, 4} : ℤ) <
        min (6 + (({0, 1, 3, 4} : Finset ℤ).card : ℤ))
          ((({0, 3, 6} : Finset ℤ).card : ℤ) +
            2 * (({0, 1, 3, 4} : Finset ℤ).card : ℤ) - 2 -
            (if (6 : ℤ) = 4 then (1 : ℤ) else 0)) := by
    rw [lsNewX_cex]
    norm_num
    decide
  have hb := h {0, 3, 6} {0, 1, 3, 4} 6 4 3
    (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
    (by norm_num) hcop
    (by decide) (by decide) hcop'
    (Or.inr ⟨by norm_num, htrig⟩)
  have hcX : (({0, 3, 6} : Finset ℤ).card : ℤ) = 3 := by decide
  have hcY : (({0, 1, 3, 4} : Finset ℤ).card : ℤ) = 4 := by decide
  have hcS : ((({0, 3, 6} : Finset ℤ).image₂ (· + ·) {0, 1, 3, 4}).card : ℤ) = 8 := by
    decide
  rw [hcX, hcY, hcS] at hb
  norm_num at hb

/-! ### The corrected bound -/

/-- The corrected Lev–Smeliansky bound: with `gcd (diffs (X ∪ Y)) = 1` alone,
the second branch must use `min (|X|, |Y|)`, i.e.
`|X + Y| ≥ min (lX + |Y|, |X| + |Y| + min (|X|, |Y|) − 2 − δ)`.
For `|Y| ≤ |X|` this coincides with the file's `|X| + 2|Y| − 2 − δ`. -/
def LSBoundFixed : Prop :=
  ∀ (X Y : Finset ℤ) (lX lY : ℤ),
    0 ∈ X → lX ∈ X → (∀ x ∈ X, 0 ≤ x ∧ x ≤ lX) →
    0 ∈ Y → lY ∈ Y → (∀ y ∈ Y, 0 ≤ y ∧ y ≤ lY) →
    lY ≤ lX →
    (∀ d : ℤ, 2 ≤ d → ∃ u ∈ X ∪ Y, ∃ v ∈ X ∪ Y, ¬ d ∣ u - v) →
    min (lX + (Y.card : ℤ))
        ((X.card : ℤ) + (Y.card : ℤ) +
          min (X.card : ℤ) (Y.card : ℤ) - 2 -
          (if lX = lY then (1 : ℤ) else 0))
      ≤ ((X.image₂ (· + ·) Y).card : ℤ)

/-- The counterexample confirms the corrected bound is sharp there:
`|X + Y| = 8 = min (10, 3 + 4 + 3 − 2)`. -/
theorem cex_fixed_bound_sharp :
    (({0, 3, 6} : Finset ℤ).image₂ (· + ·) {0, 1, 3, 4}).card = 8 ∧
    min (6 + (4 : ℤ)) (3 + 4 + min (3 : ℤ) 4 - 2 - 0) = 8 :=
  ⟨by decide, by norm_num⟩

/-- Sanity check that the intended application is unaffected: when
`|Y| = |X|` the corrected second branch agrees with the file's
`|X| + 2|Y| − 2 − δ`. -/
theorem fixed_eq_of_card_le {X Y : Finset ℤ} (h : Y.card ≤ X.card) (δ : ℤ) :
    (X.card : ℤ) + (Y.card : ℤ) + min (X.card : ℤ) (Y.card : ℤ) - 2 - δ =
      (X.card : ℤ) + 2 * (Y.card : ℤ) - 2 - δ := by
  rw [min_eq_right (by exact_mod_cast h)]
  ring

end JSP000728
