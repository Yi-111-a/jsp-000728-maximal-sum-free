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
* the trivial upper bound `f(n) ≤ 2^n`;
* the asymptotic statement `SharpAsymptotic` (`log₂ f(n)/n → 1/4`) as a
  formal `Prop` together with its proved one-sided consequences.

The remaining gap to the full BLST18 theorem is the upper bound
`f(n) ≤ 2^{(1/4+o(1))n}`, which relies on Green's container lemma — not yet
formalized here.
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

/-- Exact counts for the smallest intervals. -/
theorem jsp_000728_exact :
    maxSumFreeCount 0 = 1 ∧ maxSumFreeCount 1 = 1 ∧ maxSumFreeCount 2 = 2 ∧
      maxSumFreeCount 3 = 2 ∧ maxSumFreeCount 4 = 4 ∧ maxSumFreeCount 5 = 5 ∧
        maxSumFreeCount 6 = 6 ∧ maxSumFreeCount 7 = 8 ∧
          maxSumFreeCount 8 = 13 :=
  ⟨count_zero, count_one, count_two, count_three, count_four, count_five,
    count_six, count_seven, count_eight⟩
