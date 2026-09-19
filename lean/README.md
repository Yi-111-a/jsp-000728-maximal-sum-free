# JSP-000728 — maximal sum-free subsets of `{1,…,n}` (Lean 4 + Mathlib)

How many inclusion-maximal sum-free subsets does a finite integer interval have?
Catalog answer (Balogh–Liu–Sharifzadeh–Treglown, JEMS 2018; Proc. AMS 2015):

    f(n) = 2^((1/4 + o(1)) · n)

## Status

**WIP / partial formalization — not prize_ready.** Zero `sorry`/`admit`, standard
axioms only. Proved: definitions, exact counts `f(0)…f(12)`, the sharp-rate lower
bound `f(n) ≥ 2^{⌊n/4⌋}`, the elementary upper bound `f(n) ≤ 2·3^{n/2}`,
the unconditional limsup bound `limsup log₂ f(n)/n ≤ 111/160 = 0.69375`
(`eventualRatioUpper_111_160`, assembled from a five-regime per-cell engine),
monotonicity, obstruction/covering lemmas, container-method vocabulary,
Moon–Moser/Hujter–Tuza link-graph MIS bounds (`3^{n/3}` general, `2^{n/2}`
triangle-free), link-graph triangle-freeness on the upper half, the
fingerprint entropy count `#{s ⊆ [n] : |s| ≤ δn} ≤ 2^{εn}`, Schur-triple
supersaturation (`3t²−2tn−t ≤ 2·#triples`, sparse sets ≤ `2n/3 + o(n)`),
the linear removal fragment, and the sharpened reduction
`ContainerExistence → SparseFingerprintBound → SharpAsymptotic`. The remaining
gap is the container-method upper bound `f(n) ≤ 2^{(1/4+o(1))n}` (Green/BMS
container existence + per-container fingerprint counting); see
`JSPProblem/Removal.lean` and `JSPProblem/FingerprintBuild.lean` for the
conditional closing theorems.

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
