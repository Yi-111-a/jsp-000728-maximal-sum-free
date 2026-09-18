import JSPProblem

/-!
# JSP-000728 — How many inclusion-maximal sum-free subsets does a finite
integer interval have?

Writing `f(n)` for the number of inclusion-maximal sum-free subsets of
`{1, …, n}` (here `JSP000728.maxSumFreeCount`), the sharp asymptotic answer is

    f(n) = 2 ^ ((1/4 + o(1)) * n)

(Balogh–Liu–Sharifzadeh–Treglown, JEMS 2018, arXiv:1502.07605, building on
Proc. AMS 2015, arXiv:1409.5661).

This development formalizes:

* the definitions (`IsSumFree`, `IsMaxSumFree`, `maxSumFreeCount`);
* exact values `f(0), …, f(12)` verified by kernel `decide`;
* the Cameron–Erdős / BLST lower bound `f(n) ≥ 2^{⌊n/4⌋}` for `n ≥ 4`
  (sharp exponential rate), via the `blstSet` family and extension of
  sum-free sets to maximal ones;
* the elementary upper bound `f(n) ≤ 2·3^{n/2}` (max-element pairing on
  sum-free sets), improving the trivial `2^n`; in asymptotic form
  `limsup log₂ f(n)/n ≤ log₂ 3 / 2 < 4/5`;
* monotonicity of `f` (`monotone_maxSumFreeCount`);
* the maximality obstruction/covering lemmas (`IsMaxSumFree.exists_obstruction`);
* container-method vocabulary (`schurTripleCount`, `IsContainerFamily`,
  `IsGoodContainerFamily`) with the elementary counting consequences;
* the asymptotic statement `SharpAsymptotic` (`log₂ f(n)/n → 1/4`) as a
  formal `Prop`, proved equivalent to the single missing hypothesis
  `EventualRatioUpper (1/4)` (`sharpAsymptotic_iff_eventualRatioUpper`);
* structural lemmas: the min-element translate bound
  `2·|s| ≤ n + min s` (`two_mul_card_le_of_min`), the maximum cardinality
  `|s| ≤ ⌈n/2⌉` of a sum-free set (`card_le_of_isSumFree`, attained by the
  odds), and uniqueness of the odds and the upper half as maximal sum-free
  sets inside their ambient family (`eq_odds_of_isMaxSumFree_subset`,
  `eq_upperHalf_of_isMaxSumFree_subset`);
* sharpness of the `1/4` threshold: `EventualRatioUpper c` is false for
  every `c < 1/4` (`not_eventualRatioUpper_of_lt_quarter`), and
  `SharpAsymptotic ↔ ∀ c ≥ 1/4, EventualRatioUpper c`;
* the conditional closing theorem: the BLST18 container hypothesis
  `MaxContainerBound` (exponentially few containers, each housing
  `≤ 2^{(1/4+o(1))n}` maximal sum-free sets) implies `SharpAsymptotic`
  (`sharpAsymptotic_of_maxContainerBound`);
* a decomposition of that hypothesis into the named `Prop`s
  `ContainerExistence`, `SchurRemoval` and `FingerprintBound`
  (Removal.lean): `ContainerExistence + SchurRemoval` already yields the
  conditional `EventualRatioUpper (1/2)`, and
  `ContainerExistence + FingerprintBound` yields `SharpAsymptotic`;
* Schur-triple supersaturation (Supersaturation.lean): the fiber formula
  `schurTripleCount s = ∑ z ∈ s, |{x ∈ s : z − x ∈ s}|`, the
  inclusion–exclusion bound, the quantitative
  `2·|s| ≤ n + 1 + schurTripleCount s`, and the removal-lemma converse
  `schurTripleCount s ≤ 3·|s∖t|·|s|²` for sum-free `t ⊆ s`;
* per-container vocabulary (Fingerprint.lean): `IsMaxSumFreeIn`,
  `maxSumFreeSetsIn`, the descent `IsMaxSumFree n M → M ⊆ C →
  IsMaxSumFreeIn C M`, and the singleton counts for the `odds`/`upperHalf`
  containers;
* the min-element decomposition (MinDecomp.lean):
  `maxSumFreeCount n = ∑ m, (minClass n m).card` with per-class bounds
  `≤ 2^{n+1−m}` and `≤ 1` for `2m > n` (upper-half uniqueness);
* interval-relative sum-free counting (IntervalCount.lean):
  `sumFreeCountIn` with `≤ min(2^{b+1−a}, 2·3^{b/2})` on `Icc a b`.

The remaining gap to the full BLST18 theorem is exactly the container-method
upper bound — `EventualRatioUpper (1/4)`, i.e. `f(n) ≤ 2^{(1/4+o(1))n}` —
which relies on Green's container lemma, an arithmetic removal lemma and the
BLST18 fingerprint counting; only the conditional reductions are proved here.
-/

open JSP000728

/-- `f n ≥ 2` for every `n ≥ 2` (the odds and the upper half). -/
theorem jsp_000728_lower_two {n : ℕ} (hn : 2 ≤ n) :
    2 ≤ maxSumFreeCount n :=
  two_le_maxSumFreeCount hn

/-- `f n ≥ 3` for every `n ≥ 6` (a third maximal sum-free family exists in
every residue class mod 3). -/
theorem jsp_000728_lower_three {n : ℕ} (hn : 6 ≤ n) :
    3 ≤ maxSumFreeCount n :=
  three_le_maxSumFreeCount hn

/-- Cameron–Erdős / BLST lower bound: `f n ≥ 2^{⌊n/4⌋}` for every `n`.  The
constant `1/4` in the exponent is sharp. -/
theorem jsp_000728_lower_pow_quarter (n : ℕ) :
    2 ^ (n / 4) ≤ maxSumFreeCount n :=
  two_pow_quarter_le_maxSumFreeCount' n

/-- `log₂` form: `log₂ f(n) ≥ n/4 − 1` for `n ≥ 4`. -/
theorem jsp_000728_logb_lower {n : ℕ} (hn : 4 ≤ n) :
    (n : ℝ) / 4 - 1 ≤ Real.logb 2 (maxSumFreeCount n : ℝ) :=
  quarter_sub_one_le_logb_maxSumFreeCount hn

/-- Trivial upper bound `f n ≤ 2^n`. -/
theorem jsp_000728_upper (n : ℕ) : maxSumFreeCount n ≤ 2 ^ n :=
  maxSumFreeCount_le_two_pow n

/-- Elementary improved upper bound `f n ≤ 2·3^{n/2}` (max-element pairing). -/
theorem jsp_000728_upper_pair (n : ℕ) : maxSumFreeCount n ≤ 2 * 3 ^ (n / 2) :=
  maxSumFreeCount_le_two_mul_three_pow n

/-- `f` is nondecreasing. -/
theorem jsp_000728_monotone : Monotone maxSumFreeCount :=
  monotone_maxSumFreeCount

/-- The pairing bound yields `limsup log₂ f(n)/n ≤ log₂ 3 / 2`. -/
theorem jsp_000728_eventual_upper : EventualRatioUpper (Real.logb 2 3 / 2) :=
  fun ε hε => logb_ratio_eventually_le_logb3_half hε

/-- The Fibonacci-path bound improves the proved upper bound to
`limsup log₂ f(n)/n ≤ log₂ φ ≈ 0.6942` (was `log₂ 3 / 2 ≈ 0.7925`). -/
theorem jsp_000728_eventual_upper_fib :
    EventualRatioUpper (Real.logb 2 Real.goldenRatio) :=
  eventualRatioUpper_goldenRatio

/-- Pointwise form: `f n ≤ n·φ^n` for `n ≥ 1`. -/
theorem jsp_000728_upper_fib (n : ℕ) (hn : 1 ≤ n) :
    (maxSumFreeCount n : ℝ) ≤ n * Real.goldenRatio ^ n :=
  maxSumFreeCount_le_goldenRatio hn

/-- Eventually `log₂ f(n)/n ≤ 4/5`. -/
theorem jsp_000728_ratio_le_four_fifths :
    ∀ᶠ n : ℕ in Filter.atTop,
      Real.logb 2 (maxSumFreeCount n : ℝ) / (n : ℝ) ≤ 4 / 5 :=
  logb_ratio_eventually_le_four_fifths

/-- A sum-free subset of `{1,…,n}` has at most `⌈n/2⌉` elements. -/
theorem jsp_000728_sumfree_max_card {n : ℕ} {M : Finset ℤ}
    (hM : M ∈ maxSumFreeSets n) : M.card ≤ (n + 1) / 2 :=
  card_le_of_isMaxSumFree hM

/-- The constant `1/4` is the sharp threshold: no smaller eventual upper
bound on `log₂ f(n)/n` is possible. -/
theorem jsp_000728_sharp_threshold {c : ℝ} (h : c < 1 / 4) :
    ¬ EventualRatioUpper c :=
  not_eventualRatioUpper_of_lt_quarter h

/-- Conditional closing theorem: the BLST18 container hypothesis implies the
sharp asymptotic `log₂ f(n)/n → 1/4`. -/
theorem jsp_000728_conditional (h : MaxContainerBound) : SharpAsymptotic :=
  sharpAsymptotic_of_maxContainerBound h

/-- Decomposed conditional headline: Green/BMS container existence plus the
BLST18 per-container fingerprint count imply the sharp asymptotic. -/
theorem jsp_000728_conditional_decomposed (hCE : ContainerExistence)
    (hFB : FingerprintBound) : SharpAsymptotic :=
  sharpAsymptotic_of_containerExistence_fingerprint hCE hFB

/-- Weaker conditional bound: container existence plus the arithmetic removal
lemma already yield `limsup log₂ f(n)/n ≤ 1/2`. -/
theorem jsp_000728_conditional_half (hCE : ContainerExistence)
    (hSR : SchurRemoval) : EventualRatioUpper (1 / 2) :=
  eventualRatioUpper_half_of_removal_containers hCE hSR

/-- Exact counts for the smallest intervals. -/
theorem jsp_000728_exact :
    maxSumFreeCount 0 = 1 ∧ maxSumFreeCount 1 = 1 ∧ maxSumFreeCount 2 = 2 ∧
      maxSumFreeCount 3 = 2 ∧ maxSumFreeCount 4 = 4 ∧ maxSumFreeCount 5 = 5 ∧
        maxSumFreeCount 6 = 6 ∧ maxSumFreeCount 7 = 8 ∧
          maxSumFreeCount 8 = 13 :=
  ⟨count_zero, count_one, count_two, count_three, count_four, count_five,
    count_six, count_seven, count_eight⟩
