# JSP-000728 — How many inclusion-maximal sum-free subsets does a finite integer interval have?

- **id:** JSP-000728
- **title:** How many inclusion-maximal sum-free subsets does a finite integer interval have?
- **area:** Additive combinatorics
- **status:** Solved
- **Lean:** No
- **Eligible / Claim:** No / Unavailable
- **role:** Default harness target (trial order #1)

## Statement

How many inclusion-maximal sum-free subsets does a finite integer interval have?

## Catalog

- Anchor: https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0701-0800.md#JSP-000728
- Index: https://github.com/TheJustinSunPrize/awards/blob/main/problems/README.md (search `JSP-000728`)
- Awards home: https://github.com/TheJustinSunPrize/awards

## Primary papers

- [LuSc01] On the number of maximal sum-free sets — Proc. AMS (2001). DOI: https://doi.org/10.1090/s0002-9939-00-05815-9
- [BLST15] The number of maximal sum-free subsets of integers — Proc. AMS (2015). arXiv: https://arxiv.org/abs/1409.5661
- [BLST18] Sharp bound on the number of maximal sum-free subsets of integers — JEMS (2018). arXiv: https://arxiv.org/abs/1502.07605

Prefer **BLST15/18** as the main formalization sources.

## Lean / related libraries

- No complete sorry-free Lean proof of this theorem located.
- Reusable definition: `IsSumFree` in google-deepmind/formal-conjectures — https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjecturesForMathlib/Combinatorics/Basic.lean
- Related but **not** this problem: other sum-free Erdős/Green items in formal-conjectures (e.g. GreensOpenProblems/1–2, ErdosProblems/867). Do not treat those as a completed proof of JSP-000728.

## Success criteria

- `lake build` succeeds
- `sorry` and `admit` counts are zero
- no new axioms
- final commit SHA and build evidence recorded for JSP submission format

## Notes

Practice slot; may still be hard. Exact official wording and paper theorem statement must match before any submission. Completing Lean here does not by itself guarantee prize eligibility or payment. Harness KPI: eliminate `sorry` within a day of useful progress, else switch to the next problem in order.
