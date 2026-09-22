import JSPProblem.Prize
import JSPProblem.ZModRemoval
import JSPProblem.DFSTBridge
import JSPProblem.BMSContainer
import JSPProblem.ZKAssemble

/-!
# JSP-000728 — the headline layer

With this file the BLST18 sharp asymptotic is reduced to **a single
remaining hypothesis**: Freiman's `3k − 4` theorem (`Freiman3k4`,
`JSPProblem/DFSTBridge.lean`).

Unconditionally proved (standard axioms only):

* `containerExistence` — the Green/BMS container lemma
  (`BMSContainer.lean`);
* `schurRemoval` — Green's arithmetic removal lemma for `x + y = z`,
  proved here via the cyclic-group reduction `schurRemoval_of_zmod`
  (`RemovalFull.lean`) applied to `schurRemovalZMod`
  (`ZModRemoval.lean`: the tripartite-graph reduction to Mathlib's
  `SimpleGraph.triangle_removal`);
* `oddContainerBound` — the odd-type per-container bound
  (`OddBound.lean`);
* `sharpAsymptotic_of_freiman3k4 : Freiman3k4 → SharpAsymptotic` — the
  conditional headline modulo only Freiman `3k − 4`.
-/

namespace JSP000728

/-- **The Schur removal lemma, proved.**  Green's arithmetic removal lemma
for `x + y = z`, obtained via the cyclic-group reduction
`schurRemoval_of_zmod` applied to `schurRemovalZMod` (the tripartite
triangle-removal argument of `ZModRemoval.lean`, powered by Mathlib's
`SimpleGraph.triangle_removal`). -/
theorem schurRemoval : SchurRemoval := schurRemoval_of_zmod schurRemovalZMod

/-- **BLST18 modulo only Freiman's `3k − 4` theorem.**  Container existence
(`containerExistence`), the Schur removal lemma (`schurRemoval`) and the odd
container bound (`oddContainerBound`) are all proved unconditionally; the
sole remaining hypothesis is `Freiman3k4`, which yields `DFST` via
`dfst_of_freiman3k4`. -/
theorem sharpAsymptotic_of_freiman3k4 (hF : Freiman3k4) : SharpAsymptotic :=
  sharpAsymptotic_of_removal_dfst schurRemoval (dfst_of_freiman3k4 hF)

/-- The `EventualRatioUpper (1/4)` form of the same conditional headline. -/
theorem eventualRatioUpper_quarter_of_freiman3k4 (hF : Freiman3k4) :
    EventualRatioUpper (1 / 4) :=
  sharpAsymptotic_iff_eventualRatioUpper.mp (sharpAsymptotic_of_freiman3k4 hF)

/-- **The BLST18 sharp asymptotic, unconditional.**  The number `f(n)` of
inclusion-maximal sum-free subsets of `{1,…,n}` satisfies
`log₂ f(n) / n → 1/4`, i.e. `f(n) = 2^{(1/4 + o(1))·n}`.

The remaining hypothesis `Freiman3k4` is discharged by the tight periodic
fibre count `zkTightCount` (`ZKAssemble.lean`) through the chain
`ZKTightCount → ZKPartialResidual → PeriodicMarginal → ZModKneserBound →
Freiman3k4Residual → Freiman3k4`. -/
theorem maxSumFreeCount_sharp_asymptotic : SharpAsymptotic :=
  sharpAsymptotic_of_freiman3k4
    (freiman3k4 (freiman3k4Residual
      (zmodKneserBound' (zmodKneserBound_of_zkPartial
        (zkPartialResidual zkTightCount)))))

/-- The same headline in catalog language (`jsp_000728_blst18` alias). -/
theorem jsp_000728_blst18 : SharpAsymptotic :=
  maxSumFreeCount_sharp_asymptotic

end JSP000728
