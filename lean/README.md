# JSP-000728 — maximal sum-free subsets of `{1,…,n}` (Lean 4 + Mathlib)

How many inclusion-maximal sum-free subsets does a finite integer interval have?
Catalog answer (Balogh–Liu–Sharifzadeh–Treglown, JEMS 2018; Proc. AMS 2015):

    f(n) = 2^((1/4 + o(1)) · n)

## Status

**Complete proof assembled — `maxSumFreeCount_sharp_asymptotic : SharpAsymptotic`**
(`JSPProblem/Headline.lean`), i.e. `log₂ f(n) / n → 1/4`, formalizing
`f(n) = 2^{(1/4+o(1))n}`. Zero `sorry`/`admit`, no custom axioms. The upper
bound is discharged through the full BLST18 pipeline: BMS/Saxton–Thomason
container existence (`BMSContainer.lean`), the Schur arithmetic removal lemma
via tripartite `ZMod` reduction to Mathlib's `triangle_removal`
(`ZModRemoval.lean`, `RemovalFull.lean`), the odd-container Sapozhenko bound
(`OddBound.lean`), the DFST trichotomy (`Trichotomy.lean`, `DFSTBridge.lean`),
and Freiman's `3k−4` theorem (`Freiman3k4.lean`) whose periodic residual case
is closed by the tight-Kneser fibre count `zkTightCount`
(`ZKAssemble.lean`/`ZKTight.lean`/`ZKMissing.lean`/`ZKTightAttack.lean` via
`ZKPartial.lean`/`ZKBound2.lean`).

Also proved: definitions, exact counts `f(0)…f(15)` by kernel `decide`
(`ExactCounts.lean`, `BitmaskCount.lean`), the sharp-rate lower bound
`f(n) ≥ 2^{⌊n/4⌋}`, elementary upper bounds, monotonicity,
obstruction/covering lemmas, Moon–Moser/Hujter–Tuza link-graph MIS bounds,
the fingerprint entropy count `#{s ⊆ [n] : |s| ≤ δn} ≤ 2^{εn}`, Schur-triple
supersaturation, and the linear removal fragment.

## Build

Requires [elan](https://github.com/leanprover/elan) (Lean toolchain manager).
The toolchain is pinned by `lean-toolchain`:

```
leanprover/lean4:v4.35.0-rc2
```

```sh
cd lean
lake build          # downloads the pinned toolchain via elan on first run
```

Mathlib is fetched from `leanprover-community/mathlib4` `master` (see
`lakefile.lean` / `lake-manifest.json`).

## Layout

- `JSPProblem/Basic.lean` — `interval`, `IsSumFree`, `IsMaxSumFree`, `maxSumFreeCount`
- `JSPProblem/ExactCounts.lean` — `f(0)…f(12)` by kernel `decide`
- `JSPProblem/BlstFamily.lean`, `BlstCounting.lean` — lower bound `f(n) ≥ 2^{n/4}`
- `JSPProblem/PairBound.lean` — elementary upper bound `f(n) ≤ 2·3^{n/2}`
- `JSPProblem/Asymptotic.lean`, `AsymptoticReduction.lean` — `SharpAsymptotic`
  Prop, lower half proved, equivalence with `EventualRatioUpper (1/4)`
- `JSPProblem/ContainerReduction.lean` — `MaxContainerBound → SharpAsymptotic`
- `JSPProblem/MinElement.lean`, `MaxCard.lean`, `Extremal.lean`,
  `SharpThreshold.lean` — structural lemmas (min-element translate bound,
  `|s| ≤ ⌈n/2⌉`, uniqueness of odds/upper-half, sharpness of the `1/4` threshold)
- `Main.lean` — catalog-facing summary theorems (`jsp_000728_*`)

## Verification

```sh
lake build                                   # must succeed
grep -rn "sorry\|admit" JSPProblem/ Main.lean # must be empty
```

`#print axioms` on every theorem reports only `propext`, `Classical.choice`,
`Quot.sound` — no custom axioms.
