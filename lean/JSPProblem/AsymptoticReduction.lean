import JSPProblem.Asymptotic

/-!
# JSP-000728 — reduction of the sharp asymptotic to a single upper-bound hypothesis

The BLST18 headline statement is `SharpAsymptotic` : `log₂ f(n) / n → 1/4`,
where `f n = maxSumFreeCount n` counts inclusion-maximal sum-free subsets of
`{1,…,n}`.

The lower-bound half (`liminf ≥ 1/4`) is already proved in
`JSPProblem.Asymptotic` as `logb_ratio_eventually_ge_quarter_sub`.  The only
missing ingredient for the full headline is the matching upper bound:

  for every `ε > 0`, eventually `log₂ f(n) / n ≤ 1/4 + ε`,

i.e. the container-method bound `f(n) ≤ 2^{(1/4 + o(1)) n}` of
Balogh–Liu–Sharifzadeh–Treglown.  We package exactly this as the predicate
`EventualRatioUpper (1/4)` and prove it is **equivalent** to `SharpAsymptotic`,
so that the eventual unconditional proof of the headline reduces to a single,
clearly-stated hypothesis.
-/

namespace JSP000728

/-- `EventualRatioUpper c` says the ratio `log₂ f(n) / n` is eventually at most
`c + ε` for every `ε > 0`; equivalently `limsup (log₂ f(n) / n) ≤ c`.
For `c = 1/4` this is exactly the container-method upper bound
`f(n) ≤ 2^{(1/4 + o(1)) n}` needed for the BLST18 headline. -/
def EventualRatioUpper (c : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in Filter.atTop,
    Real.logb 2 (maxSumFreeCount n : ℝ) / (n : ℝ) ≤ c + ε

/-- **The remaining gap implies the headline.**  Together with the proved
lower bound `log₂ f(n) / n ≥ 1/4 − ε` (eventually), the hypothesis
`EventualRatioUpper (1/4)` squeezes `log₂ f(n) / n` to `1/4`. -/
theorem sharpAsymptotic_of_eventualRatioUpper (h : EventualRatioUpper (1 / 4)) :
    SharpAsymptotic := by
  unfold SharpAsymptotic
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  filter_upwards [h (ε / 2) hε2, logb_ratio_eventually_ge_quarter_sub hε2]
    with n hup hlo
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

/-- **The headline implies the hypothesis.**  Convergence of
`log₂ f(n) / n` to `1/4` gives, for each `ε > 0`, the eventual bound
`log₂ f(n) / n ≤ 1/4 + ε`. -/
theorem eventualRatioUpper_of_sharpAsymptotic (h : SharpAsymptotic) :
    EventualRatioUpper (1 / 4) := by
  intro ε hε
  filter_upwards [(Metric.tendsto_nhds.mp h) ε hε] with n hn
  rw [Real.dist_eq] at hn
  have hlt : Real.logb 2 (maxSumFreeCount n : ℝ) / (n : ℝ) - 1 / 4 < ε :=
    (abs_lt.mp hn).2
  linarith

/-- The sharp asymptotic `log₂ f(n) / n → 1/4` is **equivalent** to the single
missing hypothesis `EventualRatioUpper (1/4)` (the container-method upper
bound `f(n) ≤ 2^{(1/4 + o(1)) n}`); the matching lower bound is already
proved unconditionally. -/
theorem sharpAsymptotic_iff_eventualRatioUpper :
    SharpAsymptotic ↔ EventualRatioUpper (1 / 4) :=
  ⟨eventualRatioUpper_of_sharpAsymptotic, sharpAsymptotic_of_eventualRatioUpper⟩

/-- Glue naming for the headline: identical to
`sharpAsymptotic_iff_eventualRatioUpper`.

NOTE for the final unconditional proof (to be named
`maxSumFreeCount_sharp_asymptotic`): the only missing hypothesis for the
BLST18 headline is `EventualRatioUpper (1/4)`, which is exactly the
container-method upper bound `f(n) ≤ 2^{(1/4 + o(1)) n}`. -/
theorem tendsto_logb_ratio_iff :
    SharpAsymptotic ↔ EventualRatioUpper (1 / 4) :=
  sharpAsymptotic_iff_eventualRatioUpper

/-- `EventualRatioUpper` is monotone in the constant: any eventual upper bound
with constant `c` is also one with any larger constant `c'`. -/
theorem EventualRatioUpper.mono {c c' : ℝ} (h : EventualRatioUpper c)
    (hcc : c ≤ c') : EventualRatioUpper c' := by
  intro ε hε
  filter_upwards [h ε hε] with n hn
  linarith

end JSP000728
