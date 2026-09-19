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

/-- Second-minimum refinement: the class with minimum `m` is the disjoint
union over `s` of the classes with second-least element `s`, each member
satisfying the double translate constraint (`shiftFree2`). -/
theorem jsp_000728_second_min_decomp {n : ℕ} {m : ℤ} :
    (minClass n m).card =
      ∑ s ∈ Finset.Icc m (n : ℤ), (secondMinClass n m s).card :=
  minClass_card_eq_sum_secondMinClass

/-- The `s = 2m` second-minimum class is empty: `m, 2m ∈ M` would be a
Schur triple inside a sum-free set. -/
theorem jsp_000728_second_min_two_mul (n : ℕ) (m : ℤ) :
    secondMinClass n m (2 * m) = ∅ :=
  secondMinClass_two_mul n m

/-- Maximal sets whose even part is the singleton `{e}` have at most
`φ^n` members (odd part is `e`-shift-free). -/
theorem jsp_000728_single_even_bound {n : ℕ} {e : ℤ} (hpar : Even e)
    (he : 2 ≤ e) (hen : e ≤ (n : ℤ)) :
    ((singleEvenClass n e).card : ℝ) ≤ Real.goldenRatio ^ n :=
  card_singleEvenClass_le_goldenRatio hpar he hen

/-- Covering at the top: for every maximal sum-free `M ⊆ {1,…,n}`,
either `n ∈ M` or `n` is a sum of two elements of `M`; in particular
`2·max M ≥ n`. -/
theorem jsp_000728_max_cover {n : ℕ} (hn : 1 ≤ n) {M : Finset ℤ}
    (hM : M ∈ maxSumFreeSets n) :
    (n : ℤ) ∈ M ∨ ∃ a ∈ M, ∃ b ∈ M, a + b = (n : ℤ) :=
  maxSumFree_covers_top hn hM

/-- Ladder independent-set count: the `2×L` ladder has `a(L)` independent
sets with `a(L+2) = 2·a(L+1) + a(L)` (Pell) and `a(L)·2^{L-1} ≤ 3·5^{L-1}`
(per-vertex rate `√(5/2) ≈ 1.5811 < φ`).  This is the counting engine for
the distance-`{m,s}` cylinder classes in the second-minimum refinement. -/
theorem jsp_000728_ladder_rec (L : ℕ) :
    (ladSets (L + 2)).card =
      2 * (ladSets (L + 1)).card + (ladSets L).card :=
  ladSets_card_add_two L

theorem jsp_000728_ladder_bound {L : ℕ} (hL : 1 ≤ L) :
    (ladSets L).card * 2 ^ (L - 1) ≤ 3 * 5 ^ (L - 1) :=
  ladSets_card_mul_two_pow_le hL

/-- Uniform second-minimum class bound: every `(m,s)` class has at most
`φ^{(n-s) + min(m, n-s)}` members. -/
theorem jsp_000728_second_min_bound {n : ℕ} {m s : ℤ} (hm : 1 ≤ m) :
    ((secondMinClass n m s).card : ℝ) ≤
      Real.goldenRatio ^
        (((n : ℤ) - s).toNat + (min m ((n : ℤ) - s)).toNat) :=
  secondMinClass_card_le_goldenRatio hm

/-- Rail-pair engine: a matched pair `{r, r+m}` of mod-`s` residue rails
(`r ≤ s−m`, no wrap) carries at most `(ladSets L)` double-shift-free subsets —
per-vertex rate `√(1+√2) ≈ 1.5538 < φ` with **no** constant slack. -/
theorem jsp_000728_pair_rail_ladder {n : ℕ} {m s r : ℤ} (hm : 1 ≤ m)
    (hms : m < s) (hr : 1 ≤ r) (hrsm : r ≤ s - m) :
    ((cls n s r ∪ cls n s (r + m)).powerset.filter (shiftFree2 m s)).card ≤
      4 * (ladSets ((((n : ℤ) - r) / s).toNat + 1)).card :=
  card_powerset_filter_shiftFree2_pair_cls_le hm hms hr hrsm

/-- Explicit rail pairing cover: `Icc (s+1) n` is covered by the `s−m`
rail pairs `{r, r+m}` (`r ≤ s−m`) plus the `2m−s` leftover rails
(`Icc (s−m+1) m`, empty for `s ≥ 2m`). -/
theorem jsp_000728_rail_pair_cover {n : ℕ} {m s : ℤ} (hm : 1 ≤ m)
    (hms : m < s) :
    Finset.Icc (s + 1) (n : ℤ) ⊆
      (Finset.Icc 1 (s - m)).biUnion
          (fun r => cls n s r ∪ cls n s (r + m)) ∪
        (Finset.Icc (s - m + 1) m).biUnion (cls n s) :=
  Icc_subset_biUnion_pairCls hm hms

/-- Assembled rail-pair product bound (conditional on the per-pair ladder
bound `hpair`, discharged by `card_powerset_filter_shiftFree2_pair_cls_le`). -/
theorem jsp_000728_shiftFree2_le_pairProd {n : ℕ} {m s : ℤ}
    (hm : 1 ≤ m) (hms : m < s) :
    ((Finset.Icc (s + 1) (n : ℤ)).powerset.filter (shiftFree2 m s)).card ≤
      (∏ r ∈ Finset.Icc 1 (s - m),
          4 * (ladSets ((((n : ℤ) - r) / s).toNat + 1)).card) *
        ∏ ρ ∈ Finset.Icc (s - m + 1) m,
          Nat.fib ((((n : ℤ) - ρ) / s).toNat + 2) :=
  card_powerset_filter_shiftFree2_Icc_le_pairProd hm hms fun r hr =>
    card_powerset_filter_shiftFree2_pair_cls_le hm hms
      (Finset.mem_Icc.mp hr).1 (Finset.mem_Icc.mp hr).2

/-- 3-rail cyclic strip (`s = 3m` orbits): the triangle-column transfer gives
`T_L·2^L ≤ 4·7^L`, per-vertex rate `(7/2)^{1/3} ≈ 1.518`. -/
theorem jsp_000728_tricyl_bound (L : ℕ) :
    (triSets L).card * 2 ^ L ≤ 4 * 7 ^ L :=
  triSets_card_mul_two_pow_le L

/-- Column-block engines: a single `s`-column carries at most
`3^{s−m}·2^{(2m−s)⁺}` and a double `2s`-column at most
`7^{s−m}·3^{(2m−s)⁺}` double-shift-free subsets. -/
theorem jsp_000728_col_bounds {m s a : ℤ} (hm : 1 ≤ m) (hms : m < s) :
    ((Finset.Icc a (a + s - 1)).powerset.filter (shiftFree2 m s)).card ≤
        3 ^ (s - m).toNat * 2 ^ (2 * m - s).toNat ∧
      ((Finset.Icc a (a + 2 * s - 1)).powerset.filter
          (shiftFree2 m s)).card ≤
        7 ^ (s - m).toNat * 3 ^ (2 * m - s).toNat :=
  ⟨card_powerset_filter_shiftFree2_col_le (n := 0) hm hms,
   card_powerset_filter_shiftFree2_colPair_le (n := 0) hm hms⟩

/-- Large-`s` regime (`n ≤ 2s`, vacuous `s`-shift): the `m`-matching bound
gives `(secondMinClass n m s).card ≤ 3^{n−s}` — sub-`φ` for `s ≥ n/2`. -/
theorem jsp_000728_second_min_large_s {n : ℕ} {m s : ℤ} (hm : 1 ≤ m)
    (hms : m < s) (hns : (n : ℤ) ≤ 2 * s) :
    (secondMinClass n m s).card ≤ 3 ^ ((n : ℤ) - s).toNat :=
  secondMinClass_card_le_of_half_le hm hms hns

/-- Cameron–Erdős/Wolfovitz determination: a maximal sum-free `M` with
`min M = m` is determined by its trace `M ∩ [1, n−m]` (elements of `(n−m, n]`
are either sums of two smaller members — excluded — or adjoinable — included).
Hence `minClass n m ≤ 2^{n−2m+1}`: the whole diagonal region `s ≈ m` collapses. -/
theorem jsp_000728_minClass_determined {n : ℕ} {m : ℤ} :
    (minClass n m).card ≤ 2 ^ ((n : ℤ) - 2 * m + 1).toNat :=
  minClass_card_le_two_pow_determined

/-- Sharper determined bound: the trace minus `m` is `m`-shift-free on
`Icc (m+1) (n−m)`, giving `minClass n m ≤ ∏_{r∈Icc 1 m} fib(L_r+2)`
— effectively `φ^{n−m}` for `m ≥ 1`. -/
theorem jsp_000728_minClass_prod_fib {n : ℕ} {m : ℤ} :
    (minClass n m).card ≤
      ∏ r ∈ Finset.Icc 1 m, Nat.fib ((((n : ℤ) - m - r) / m).toNat + 2) :=
  minClass_card_le_prod_fib

/-- Sharp ladder rate: `a(L) ≤ (5/4)·(1+√2)^L` (exact Perron root of
`a(L+2) = 2a(L+1) + a(L)`), per-vertex `√(1+√2) ≈ 1.5538`. -/
theorem jsp_000728_ladder_pell_bound (L : ℕ) :
    ((ladSets L).card : ℝ) ≤ 5 / 4 * (1 + Real.sqrt 2) ^ L :=
  ladSets_card_le_pell_pow L

/-- Exact counts for the smallest intervals. -/
theorem jsp_000728_exact :
    maxSumFreeCount 0 = 1 ∧ maxSumFreeCount 1 = 1 ∧ maxSumFreeCount 2 = 2 ∧
      maxSumFreeCount 3 = 2 ∧ maxSumFreeCount 4 = 4 ∧ maxSumFreeCount 5 = 5 ∧
        maxSumFreeCount 6 = 6 ∧ maxSumFreeCount 7 = 8 ∧
          maxSumFreeCount 8 = 13 :=
  ⟨count_zero, count_one, count_two, count_three, count_four, count_five,
    count_six, count_seven, count_eight⟩

/-- Exact counts extended to `n = 13, 14, 15` via the bitmask bridge
(`maxSumFreeCount_eq_maskCount`): `f(13) = 51`, `f(14) = 66`,
`f(15) = 86`, all kernel-verified. -/
theorem jsp_000728_exact_large :
    maxSumFreeCount 13 = 51 ∧ maxSumFreeCount 14 = 66 ∧
      maxSumFreeCount 15 = 86 :=
  ⟨count_thirteen, count_fourteen, count_fifteen⟩

/-- **Orbit decomposition** (`ZMod s` orbits of `+m`, `gcd(m,s)` orbits of
`s/gcd(m,s)` rails each): `Icc (s+1) n` is covered by the orbit rail-unions. -/
theorem jsp_000728_orbit_cover {n : ℕ} {m s : ℤ} (hm : 1 ≤ m)
    (hms : m < s) :
    Finset.Icc (s + 1) (n : ℤ) ⊆
      ((Finset.Icc 1 s).image (orbit m s)).biUnion
        (fun O => O.biUnion (cls n s)) :=
  Icc_subset_biUnion_orbitCls hm hms

/-- Per-orbit strip bound: double-shift-free subsets of one orbit's rail
union inject into `orbitStrips` (wrap edge dropped — a superset bound). -/
theorem jsp_000728_orbit_strip {n : ℕ} {m s r : ℤ} (hm : 1 ≤ m)
    (hms : m < s) :
    (((orbit m s r).biUnion (cls n s)).powerset.filter
        (shiftFree2 m s)).card ≤
      (orbitStrips (orbitTwist m s r) (orbitLen m s)
        (((n : ℤ) - 1) / s).toNat).card :=
  card_powerset_filter_shiftFree2_orbitCls_le hm hms

/-- **Staircase ladder** (ascending rungs `(f,j)→(t,j+1)` only): the count
satisfies `a(L+3) = a(L+2) + 3·a(L+1) + a(L)` (Perron root `≈ 2.4115`,
per-vertex `≈ 1.5529`). -/
theorem jsp_000728_stair_rec (L : ℕ) :
    (stairSets (L + 3)).card =
      (stairSets (L + 2)).card + 3 * (stairSets (L + 1)).card +
        (stairSets L).card :=
  stairSets_card_add_three L

theorem jsp_000728_stair_bound {L : ℕ} (hL : 1 ≤ L) :
    (stairSets L).card * 2 ^ (L - 1) ≤ 4 * 5 ^ (L - 1) :=
  stairSets_card_mul_two_pow_le hL

/-- **Mod-`m` staircase pairing** (regime `s ≤ 3m/2`): a matched rail pair
`{r, r+(s−m)}` carries at most `stairSets L` double-shift-free subsets —
the `m`-shift is vertical, the `s`-shift an ascending rung. -/
theorem jsp_000728_modm_stair_pair {n : ℕ} {m s r : ℤ} (hm : 1 ≤ m)
    (hms : m < s) (hsm : 2 * s ≤ 3 * m) (hr : 1 ≤ r) (hrsm : r ≤ s - m) :
    ((cls n m r ∪ cls n m (r + s - m)).powerset.filter
        (shiftFree2 m s)).card ≤
      (stairSets (((n : ℤ) - r) / m).toNat).card :=
  card_powerset_filter_shiftFree2_modm_pair_cls_le hm hms hsm hr hrsm

/-- The mod-`m` staircase pairing cover: `Icc (m+1) n` is covered by the
`s−m` pairs `{r, r+(s−m)}` plus `3m−2s` leftover rails (empty at `s=3m/2`). -/
theorem jsp_000728_modm_cover {n : ℕ} {m s : ℤ} (hm : 1 ≤ m)
    (hms : m < s) (hsm : 2 * s ≤ 3 * m) :
    Finset.Icc (m + 1) (n : ℤ) ⊆
      (Finset.Icc 1 (s - m)).biUnion
          (fun r => cls n m r ∪ cls n m (r + s - m)) ∪
        (Finset.Icc (2 * (s - m) + 1) m).biUnion (cls n m) :=
  Icc_subset_biUnion_modm_pairCls hm hms hsm

/-- **4-rail cyclic strip** (`c = 4` orbits): `T(L)·2^L ≤ 2·11^L`,
per-vertex rate `(11/2)^{1/4} ≈ 1.5317 < √(1+√2)`. -/
theorem jsp_000728_quad_bound (L : ℕ) :
    (quadSets L).card * 2 ^ L ≤ 2 * 11 ^ L :=
  quadSets_card_mul_two_pow_le L

/-- **Wrap-strip** (the honest `c = 3` orbit model: cyclic `+m` edges
`(0,j)→(1,j)→(2,j)→(0,j+1)`): `W(L)·2^L ≤ 27·7^L`. -/
theorem jsp_000728_wsets_bound (L : ℕ) :
    (wSets L).card * 2 ^ L ≤ 27 * 7 ^ L :=
  wSets_card_mul_two_pow_le L

/-- **`s = 3m` bridge**: double-shift-free subsets of one `{r, r+m, r+2m}`
orbit union inject into `wSets` — the `s = 3m` second-minimum cell is
bounded by wrap-strips. -/
theorem jsp_000728_tri_bridge {n : ℕ} {m r : ℤ} (hm : 1 ≤ m) (hr : 1 ≤ r)
    (hrm : r ≤ m) :
    ((cls n (3 * m) r ∪ cls n (3 * m) (r + m) ∪
        cls n (3 * m) (r + 2 * m)).powerset.filter
          (shiftFree2 m (3 * m))).card ≤
      (wSets (((n : ℤ) - r) / (3 * m)).toNat).card :=
  card_powerset_filter_shiftFree2_tri_cls_le hm hr hrm

/-- Assembled `s = 3m` product bound. -/
theorem jsp_000728_tri_prod {n : ℕ} {m : ℤ} (hm : 1 ≤ m) :
    ((Finset.Icc (3 * m + 1) (n : ℤ)).powerset.filter
        (shiftFree2 m (3 * m))).card *
        2 ^ (∑ r ∈ Finset.Icc 1 m, (((n : ℤ) - r) / (3 * m)).toNat) ≤
      27 ^ m.toNat * 7 ^ ((n : ℤ) - 3 * m).toNat :=
  card_powerset_filter_shiftFree2_triIcc_mul_le hm

/-- **Frontier reduction**: the `m ≥ n/4` min-classes contribute at most
`n·2^{⌊n/2⌋+1}` (determined bound summed geometrically), so
`f(n) ≤ smallMinSum n + n·2^{n/2+1}` — only the `m < n/4` frontier remains. -/
theorem jsp_000728_small_min {n : ℕ} (hn : 1 ≤ n) :
    maxSumFreeCount n ≤ smallMinSum n + n * 2 ^ (n / 2 + 1) :=
  maxSumFreeCount_le_smallMin_add hn

/-- Conditional closing via the small-minimum frontier: a `2^{(c+o(1))n}`
bound on `smallMinSum` yields `EventualRatioUpper (max c (1/2))`. -/
theorem jsp_000728_conditional_smallmin {c : ℝ} (h : SmallMinBound c) :
    EventualRatioUpper (max c (1 / 2)) :=
  eventualRatioUpper_of_smallMinBound h

/-- **Block-parity staircase matching** (unified for all `k = s−m ∈ [1,m)`):
bases `{r ≤ m−k : (r−1)/k even}` paired with `{r+k}` cover `Icc (m+1) n`
up to `≤ k` leftover rails — subsumes both the near-diagonal (`k ≪ m`) and
the `(3m/2, 2m)` overlap regimes. -/
theorem jsp_000728_stairmatch_cover {n : ℕ} {m k : ℤ} (hm : 1 ≤ m)
    (hk : 1 ≤ k) :
    Finset.Icc (m + 1) (n : ℤ) ⊆
      (stairBases m k).biUnion
          (fun r => cls n m r ∪ cls n m (r + k)) ∪
        (stairLeftover m k).biUnion (cls n m) :=
  Icc_subset_biUnion_stairMatchCls hm hk

/-- **Near-diagonal cell bound**: the `s = m+k` second-minimum class is
bounded by the staircase-matching closed form `4^{m−k}·5^{n−m}·2^k`
(per-vertex `≈ 2^{0.66}` for `k ≪ m` — the former `φ`-frontier cell). -/
theorem jsp_000728_stairmatch_cell {n : ℕ} {m k : ℤ} (hm : 1 ≤ m)
    (hk : 1 ≤ k) (hkm : k < m) :
    (secondMinClass n m (m + k)).card ≤
      4 ^ (m - k).toNat * (5 ^ ((n : ℤ) - m).toNat * 2 ^ k.toNat) :=
  secondMinClass_card_le_stairProd_conditional (s := m + k) (by omega)
    (card_powerset_filter_shiftFree2_Icc_le_stairMatchClosed hm hk hkm)

/-- **Piecewise cell bound** (`cellBoundReal`): `s = m` → `1`, `s = 2m` → `0`,
`n ≤ 2s` → `3^{n−s}`, otherwise the vacuous `φ`-bound — an unconditional
per-cell `ℝ` bound for every second-minimum class. -/
theorem jsp_000728_cell_bound {n : ℕ} {m s : ℤ} (hm : 1 ≤ m) (hms : m ≤ s) :
    ((secondMinClass n m s).card : ℝ) ≤ cellBoundReal n m s :=
  secondMinClass_card_le_cellBoundReal hm hms

/-- **Link-graph characterization** (Wolfovitz route): for fingerprint
`S ⊆ Icc 1 K` and `t` above `K`, `S ∪ t` is sum-free iff `S`, `t` are
sum-free and `t` is link-`S`-independent — maximal sum-free sets are counted
by maximal independent sets of link graphs. -/
theorem jsp_000728_link_union {S t : Finset ℤ} {K : ℤ} (hK : 0 ≤ K)
    (hS : S ⊆ Finset.Icc 1 K) (htK : ∀ x ∈ t, K < x) :
    IsSumFree (S ∪ t) ↔
      IsSumFree S ∧ IsSumFree t ∧ linkIndepSet S t :=
  isSumFree_union_iff_linkIndepSet hK hS htK

/-- Every min-class is counted by fingerprints: `minClass n m` is at most
the sum over `S ⊆ Icc 1 K` of the link-`S`-independent subsets of
`Icc (K+1) n`. -/
theorem jsp_000728_minclass_linksets {n : ℕ} {m K : ℤ} :
    (minClass n m).card ≤
      ∑ S ∈ (Finset.Icc 1 K).powerset,
        (linkSets S (Finset.Icc (K + 1) (n : ℤ))).card :=
  minClass_card_le_sum_linkSets

/-- **5-rail cyclic strip** (`c = 5` orbits): `P(L)·4^L ≤ 2·31^L`,
per-vertex rate `(31/4)^{1/5} ≈ 1.5049`. -/
theorem jsp_000728_pent_bound (L : ℕ) :
    (pentSets L).card * 4 ^ L ≤ 2 * 31 ^ L :=
  pentSets_card_mul_four_pow_le L

/-- **Universal orbit bound** (discharges the orbit product): every orbit
strip counts at most `ladSets^{c/2}·fib^{c%2}` subsets (column-pairing +
shear map flattening the twist), so the whole `Icc (s+1) n` double-shift-free
count is bounded by the `gcd(m,s)`-fold power — per-vertex rate
`√(1+√2) ≈ 1.5538` uniformly in the orbit size. -/
theorem jsp_000728_orbit_closed {n : ℕ} {m s : ℤ} (hm : 1 ≤ m)
    (hms : m < s) :
    ((Finset.Icc (s + 1) (n : ℤ)).powerset.filter (shiftFree2 m s)).card ≤
      ((ladSets ((((n : ℤ) - 1) / s).toNat + 1)).card ^ (orbitLen m s / 2) *
          Nat.fib ((((n : ℤ) - 1) / s).toNat + 2) ^ (orbitLen m s % 2)) ^
        Int.gcd s m :=
  card_powerset_filter_shiftFree2_Icc_le_orbitPow hm hms

/-- **Sharp staircase-matching rate**: the `5/2`-rate multiplied bound —
`card·2^{Σ_B(L−1)} ≤ 4^{|B|}·5^{Σ_B(L−1)}·2^{Σ_Λ(L+1)}`, i.e. per-vertex
`√(5/2) ≈ 1.581` on the matched rails plus `2`-per-leftover-rail-level.
This is the frontier-quality near-diagonal bound (`Σ_B L ≈ (n−m)/2`). -/
theorem jsp_000728_stairmatch_rate {n : ℕ} {m k : ℤ} (hm : 1 ≤ m)
    (hk : 1 ≤ k) (hkm : k < m) :
    ((Finset.Icc (m + 1) (n : ℤ)).powerset.filter
        (shiftFree2 m (m + k))).card *
        2 ^ (∑ r ∈ stairBases m k,
          ((((n : ℤ) - r) / m).toNat - 1)) ≤
      4 ^ (stairBases m k).card *
        5 ^ (∑ r ∈ stairBases m k,
          ((((n : ℤ) - r) / m).toNat - 1)) *
        2 ^ (∑ ρ ∈ stairLeftover m k,
          ((((n : ℤ) - ρ) / m).toNat + 1)) :=
  card_powerset_filter_shiftFree2_Icc_mul_two_pow_le_stairMatch hm hk hkm

/-- `ℝ`-form of the near-diagonal class bound. -/
theorem jsp_000728_stairmatch_real {n : ℕ} {m k : ℤ} (hm : 1 ≤ m)
    (hk : 1 ≤ k) (hkm : k < m) :
    ((secondMinClass n m (m + k)).card : ℝ) ≤
      (4 : ℝ) ^ (m - k).toNat *
        Real.goldenRatio ^ (((n : ℤ) - m).toNat + m.toNat) :=
  secondMinClass_card_le_stairMatchSharp_real hm hk hkm

/-- Sharp `ℝ`-rate for the near-diagonal class: `√(5/2)·2^{k/m}` per vertex. -/
theorem jsp_000728_staircell_rate {n : ℕ} {m k : ℤ} (hm : 1 ≤ m)
    (hk : 1 ≤ k) (hkm : k < m) (hmn : m ≤ (n : ℤ)) :
    ((secondMinClass n m (m + k)).card : ℝ) ≤
      (4 : ℝ) ^ (m - k).toNat * (2 : ℝ) ^ k.toNat *
        stairCellRate m k ^ n :=
  secondMinClass_card_le_stairCellRate_pow hm hk hkm hmn

/-- **Frontier milestone:** the limsup exponent is at most `347/500 = 0.694`,
strictly below `log₂ φ ≈ 0.6942`.  Unconditional — assembled from the
five-regime per-cell bound (`secondMinClass_card_le_cell`). -/
theorem jsp_000728_eventual_upper_sharp :
    EventualRatioUpper (max (347 / 500 : ℝ) (1 / 2)) :=
  eventualRatioUpper_347_500

/-- **Frontier milestone (sharpened):** the limsup exponent is at most
`111/160 = 0.69375`, improving on `347/500 = 0.694` — the orbit regime
coefficient is now `1777/2700` and the staircase threshold is `40k ≤ m`. -/
theorem jsp_000728_eventual_upper_111_160 :
    EventualRatioUpper (max (111 / 160 : ℝ) (1 / 2)) :=
  eventualRatioUpper_111_160

/-- **Moon–Moser bound** for the link graph: the number of maximal
link-independent subsets of `B` is at most `3^{|B|/3}` (Wolfovitz ingredient). -/
theorem jsp_000728_moon_moser (S B : Finset ℤ) :
    ((linkMaxSets S B).card : ℝ) ≤ (3 : ℝ) ^ ((B.card : ℝ) / 3) :=
  card_linkMaxSets_le_three_rpow S B

/-- **Fingerprint count:** for every `ε > 0` there is `δ > 0` such that
eventually the number of subsets of `{1,…,n}` of size `≤ δn` is at most
`2^{εn}` — the container-count input for the BMS fingerprint method. -/
theorem jsp_000728_fingerprint_count {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n : ℕ in Filter.atTop,
      (((interval n).powerset.filter
          (fun s => s.card ≤ ⌊δ * (n : ℝ)⌋₊)).card : ℝ) ≤
        (2 : ℝ) ^ (ε * (n : ℝ)) :=
  smallPowersetCard_le_two_rpow hε

/-- **Schur supersaturation:** every `s ⊆ {1,…,n}` satisfies
`3|s|² − 2|s|n − |s| ≤ 2·(number of Schur triples in s)`. -/
theorem jsp_000728_supersaturation {n : ℕ} {s : Finset ℤ}
    (hs : s ⊆ interval n) :
    3 * (s.card : ℤ) ^ 2 - 2 * (s.card : ℤ) * (n : ℤ) - (s.card : ℤ) ≤
      2 * (schurTripleCount s : ℤ) :=
  two_mul_schurTripleCount_ge hs

/-- **Link graphs are triangle-free on the upper half:** for `S` sum-free in
`{1,…,n}` and `x, y, z > n/2` pairwise distinct, `{x,y,z}` is not a link
triangle — the Wolfovitz/Hujter–Tuza input. -/
theorem jsp_000728_link_triangle_free {n : ℕ} {S B : Finset ℤ}
    (hS : S ⊆ Finset.Icc 1 (n : ℤ)) (hSf : IsSumFree S)
    (hB : ∀ x ∈ B, (n : ℤ) < 2 * x) :
    ∀ x ∈ B, ∀ y ∈ B, ∀ z ∈ B, x ≠ y → y ≠ z → x ≠ z →
      ¬ (linkAdj S x y ∧ linkAdj S y z ∧ linkAdj S x z) :=
  linkTriangleFree hS hSf hB

/-- **Hujter–Tuza bound for link graphs:** on the upper half the link graph
of a sum-free `S` is triangle-free, so it has at most `2^{|B|/2}` maximal
independent sets — the Wolfovitz counting ingredient. -/
theorem jsp_000728_hujter_tuza {n : ℕ} {S B : Finset ℤ}
    (hS : S ⊆ Finset.Icc 1 (n : ℤ)) (hSf : IsSumFree S)
    (hB : ∀ x ∈ B, (n : ℤ) < 2 * x) :
    ((linkMaxSets S B).card : ℝ) ≤ (2 : ℝ) ^ ((B.card : ℝ) / 2) :=
  card_linkMaxSets_le_two_rpow hS hSf hB

/-- **Fingerprint determination:** for `n < 2(K+1)` every maximal sum-free
`M ⊆ {1,…,n}` is recovered from its fingerprint `M ∩ {1,…,K}` and the
link-maximal upper trace `M ∩ {K+1,…,n}`; hence `f(n)` is bounded by the
fingerprint-weighted sum of link-MIS counts. -/
theorem jsp_000728_fingerprint_count_link {n : ℕ} {K : ℤ}
    (hK : (n : ℤ) < 2 * (K + 1)) :
    maxSumFreeCount n ≤
      ∑ S ∈ (Finset.Icc 1 K).powerset,
        (linkMaxSets S (Finset.Icc (K + 1) (n : ℤ))).card :=
  maxSumFreeCount_le_sum_linkMaxSets hK

/-- **Linear removal fragment:** deleting one vertex per Schur triple —
every `s` contains a sum-free `t` with `(s ∖ t).card ≤ schurTripleCount s`.
(The full removal lemma `δn² → εn` remains a named hypothesis.) -/
theorem jsp_000728_removal_linear (s : Finset ℤ) :
    ∃ t : Finset ℤ, t ⊆ s ∧ IsSumFree t ∧
      (s \ t).card ≤ schurTripleCount s :=
  exists_isSumFree_sub_card_le s

/-- **Sharpened prize reduction:** the BLST18 headline follows from
`ContainerExistence` plus `SparseFingerprintBound` — the per-container
maximal-set count only needs to hold on containers with `o(n²)` Schur
triples (unlike `FingerprintBound`, which `interval n` itself satisfies
and is therefore tautological). -/
theorem jsp_000728_sparse_reduction
    (hCE : ContainerExistence) (hSFB : SparseFingerprintBound) :
    SharpAsymptotic :=
  sharpAsymptotic_of_sparse_container_fingerprint hCE hSFB

/-- **Large-min containers are cheap:** a container `C ⊆ {1,…,n}` avoiding
`{1,…,K}` houses at most `2^{(n−2K−1)₊}` maximal sum-free sets. -/
theorem jsp_000728_mintail_container {n : ℕ} {C : Finset ℤ} {K : ℕ}
    (hC : C ⊆ interval n) (hK : ∀ x ∈ C, (K : ℤ) < x) :
    ((maxSumFreeSets n).filter (· ⊆ C)).card ≤
      2 ^ ((n : ℤ) - 2 * K - 1).toNat :=
  card_maxSumFreeSets_filter_subset_of_lower hC hK

/-- **Container construction:** the fingerprint container `containerOf n T`
covers every sum-free `I ⊇ T` — the scan only needs `a + b = x` with earlier
`T`-elements, which `I`'s sum-freeness rules out.  The remaining kernel is
`SmallFingerprint`: every sum-free `I` admitting a fingerprint `T ⊆ I` of
size `o(n)`. -/
theorem jsp_000728_container_covers {n : ℕ} {I T : Finset ℤ}
    (hI : I ⊆ interval n) (hSf : IsSumFree I) (hT : T ⊆ I) :
    I ⊆ containerOf n T :=
  containerOf_covers hI hSf hT

/-- The fingerprint container family has `≤ 2^{εn}` members eventually. -/
theorem jsp_000728_container_family_small {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n : ℕ in Filter.atTop,
      ((containerFamily n ⌊δ * (n : ℝ)⌋₊).card : ℝ) ≤
        (2 : ℝ) ^ (ε * (n : ℝ)) :=
  containerFamily_card_le_two_rpow hε

/-- **Sum-free via maximal:** every sum-free set sits inside a maximal one
with `≤ (n+1)/2` elements, so `sumFreeCount n ≤ f(n)·2^{(n+1)/2}`. -/
theorem jsp_000728_sumFreeCount_le (n : ℕ) :
    sumFreeCount n ≤ maxSumFreeCount n * 2 ^ ((n + 1) / 2) :=
  sumFreeCount_le_maxSumFreeCount_mul_pow n
