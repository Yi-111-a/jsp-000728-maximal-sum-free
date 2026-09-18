import JSPProblem

/-!
# JSP-000728 — How many inclusion-maximal sum-free subsets does a finite
integer interval have?

Writing `f(n)` for the number of inclusion-maximal sum-free subsets of
`{1, …, n}` (here `JSP000728.maxSumFreeCount`), the sharp asymptotic answer is

    f(n) = 2 ^ ((1/4 + o(1)) * n)

(Balogh–Liu–Sharifzadeh–Treglown, JEMS 2018, arXiv:1502.07605, building on
Proc. AMS 2015, arXiv:1409.5661).  Formalizing that asymptotic is future work;
this development formalizes the definitions and proves exact small values and
uniform lower bounds.
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

/-- Exact counts for the smallest intervals. -/
theorem jsp_000728_exact :
    maxSumFreeCount 0 = 1 ∧ maxSumFreeCount 1 = 1 ∧ maxSumFreeCount 2 = 2 ∧
      maxSumFreeCount 3 = 2 ∧ maxSumFreeCount 4 = 4 ∧ maxSumFreeCount 5 = 5 :=
  ⟨count_zero, count_one, count_two, count_three, count_four, count_five⟩
