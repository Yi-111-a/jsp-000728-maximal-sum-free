# ACCEPTANCE — JSP-000728 (prize-ready gate)

## Catalog

- Anchor: https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0701-0800.md#JSP-000728
- Index: https://github.com/TheJustinSunPrize/awards/blob/main/problems/README.md (search `JSP-000728`)
- Awards CONTRIBUTING (complete original solution only; no Lean source in awards repo; pin full 40-char SHA): https://github.com/TheJustinSunPrize/awards/blob/main/CONTRIBUTING.md

## Exact original question (English)

> How many inclusion-maximal sum-free subsets does a finite integer interval have?

Catalog problem description matches the above. The accepted mathematical answer (BLST15/18) is the sharp count / asymptotic for the number \(f(n)\) of inclusion-maximal sum-free subsets of \(\{1,\ldots,n\}\):

\[
f(n)=2^{(1/4+o(1))n}.
\]

Weaker lower bounds (e.g. \(f(n)\ge 2\), \(f(n)\ge 3\)) or exact small-\(n\) tables alone are **not** the original problem.

## Required Lean theorem name(s) (FULL statement)

These names must exist as `theorem`/`lemma` and be fully proved (no `sorry`/`admit`):

| Lean name | Intended statement |
|---|---|
| `maxSumFreeCount_sharp_asymptotic` | BLST18 sharp asymptotic: \(\log_2 f(n)=(1/4+o(1))n\) (formalization of the catalog answer for all large \(n\)). |

Optional supporting headline (also full-scope if used for claim):

| Lean name | Intended statement |
|---|---|
| `jsp_000728_blst18` | Alias / wrapper theorem stating the same BLST18 result in catalog language. |

**Not sufficient for prize_ready:** `jsp_000728_lower_two`, `jsp_000728_lower_three`, `jsp_000728_exact`, family maximality lemmas, or any partial lower-bound development.

## Checklist (all must pass)

- [ ] `lake build` succeeds in `lean/`
- [ ] Zero `sorry` / `admit` in all `*.lean` (excluding `.lake`)
- [ ] `#print axioms` on headline theorem(s) shows only standard axioms (no custom axioms standing in for proof)
- [ ] Public repo HEAD is a full 40-character commit SHA
- [ ] README documents build instructions (`elan`/`lake`, toolchain pin)
- [ ] `formalization.yaml` and/or `ATTRIBUTION.md` name `Yi-111-a` / operators for this formalization
- [ ] Named headline theorem(s) above exist and are proved (not merely declared)

## Harness rule

`prize_ready=true` **only** when every checklist item passes **and** the named headline theorem(s) exist and are proved.

Harness-green builds of partial lower bounds may set `partial_ok=true` but must keep `prize_ready=false`. Legacy discovery `SUCCESS` files are invalidated as `SUCCESS_PARTIAL_HARNESS_LEGACY`.
