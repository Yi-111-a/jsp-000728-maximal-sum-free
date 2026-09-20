import JSPProblem.Trichotomy
import JSPProblem.OddBound

/-!
# JSP-000728 — the prize path, fully assembled modulo the paper's own
black boxes

The upper bound of BLST18 (`f(n) = 2^{(1/4+o(1))n}` for the number `f` of
inclusion-maximal sum-free subsets of `{1,…,n}`) is now proved *modulo
exactly the three statements the paper itself cites as external theorems*:

* `ContainerExistence` — Green's container lemma (Prop. 6 of Green's
  Cameron–Erdős paper; the Fourier-granularization fingerprint);
* `SchurRemoval` — Green's arithmetic removal lemma for `x + y = z`
  (Green05 Cor. 1.6);
* `DFST` — the Deshouillers–Freiman–Sós–Temkin trichotomy for large
  sum-free sets.

Every other ingredient is proved unconditionally in this development:

* container size `|C| ≤ (1/2+o(1))n` for sparse `C` (`SparseCard`, a new
  elementary first-passage argument replacing the removal lemma);
* the per-container trichotomy (`Trichotomy.container_trichotomy`, from
  removal + DFST);
* the three counting lemmas: Moon–Moser for small containers,
  Hujter–Tuza on the upper half for interval-type containers, and the
  odd-type bound `oddContainerBound` (`OddBound.lean` — Sapozhenko's
  almost-regular MIS bound + the `≤ 24|S|³` triangle estimate + the
  almost-triangle-free upgrade `AlmostTF`).
-/

namespace JSP000728

/-- **BLST18 modulo the three cited theorems.**  Container existence, the
Schur removal lemma, and the DFST trichotomy together imply
`log₂ f(n) / n → 1/4`.  The odd-type per-container MIS bound
(`OddContainerBound`) is discharged unconditionally by `oddContainerBound`. -/
theorem sharpAsymptotic_of_containerExistence_removal_dfst
    (hCE : ContainerExistence) (hSR : SchurRemoval) (hDFST : DFST) :
    SharpAsymptotic :=
  sharpAsymptotic_of_containerExistence_removal_dfst_odd hCE hSR hDFST
    oddContainerBound

/-- The same conditional headline in `EventualRatioUpper` form. -/
theorem eventualRatioUpper_quarter_of_containerExistence_removal_dfst
    (hCE : ContainerExistence) (hSR : SchurRemoval) (hDFST : DFST) :
    EventualRatioUpper (1 / 4) :=
  sharpAsymptotic_iff_eventualRatioUpper.mp
    (sharpAsymptotic_of_containerExistence_removal_dfst hCE hSR hDFST)

end JSP000728
