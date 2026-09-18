import JSPProblem.Basic
import JSPProblem.SumFreeCount
import JSPProblem.UpperBound
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# JSP-000728 — an elementary `2 * 3^(n/2)` upper bound

A better-than-trivial exponential bound on the number of sum-free subsets
of `{1,…,n}` (and hence on `maxSumFreeCount n`).

**Pairing argument.** If `S ⊆ {1,…,n+1}` is sum-free and `n+1 ∈ S`, then for
each `i ∈ {1,…,⌊n/2⌋}` the pair `{i, n+1−i}` contributes at most one element
of `S` (since `i + (n+1−i) = n+1 ∈ S`).  The only element of `{1,…,n}` not in
any pair is a possible middle point `m` with `2m = n+1`, and `m ∉ S` since
`m + m = n+1 ∈ S`.  Hence `S` is determined by one of three statuses per
pair index, giving `#{S : n+1 ∈ S} ≤ 3^(n/2)`.

Splitting on whether `n+1 ∈ S` yields
`sumFreeCount (n+1) ≤ sumFreeCount n + 3^(n/2)`, and two-step induction
gives `sumFreeCount n ≤ 2 * 3^(n/2)`.  Taking `log₂` shows the exponential
rate is at most `log₂ 3 / 2 ≈ 0.7925`.
-/

namespace JSP000728

/-- The pair index set `1,…,⌊n/2⌋` used in the pairing argument. -/
def pairIdx (n : ℕ) : Finset ℤ := Finset.Icc 1 ((n / 2 : ℕ) : ℤ)

theorem card_pairIdx (n : ℕ) : (pairIdx n).card = n / 2 := by
  rw [pairIdx, Int.card_Icc]
  have h : ((n / 2 : ℕ) : ℤ) + 1 - 1 = ((n / 2 : ℕ) : ℤ) := by omega
  rw [h, Int.toNat_natCast]

/-- The pairing status of a set `S` at pair index `i`:
`0` if `i ∈ S`, `1` if `n+1−i ∈ S` (but `i ∉ S`), `2` if neither. -/
def pairStatus (n : ℕ) (S : Finset ℤ) (i : ↥(pairIdx n)) : Fin 3 :=
  if (i : ℤ) ∈ S then 0 else if (n : ℤ) + 1 - (i : ℤ) ∈ S then 1 else 2

/-- Rebuild a candidate set from a table of pairing statuses: take `n+1`,
every first member `i` with status `0`, and every second member `n+1−i`
with status `1`. -/
def pairRecover (n : ℕ) (g : ↥(pairIdx n) → Fin 3) : Finset ℤ :=
  insert ((n : ℤ) + 1)
    ((((Finset.univ : Finset ↥(pairIdx n)).filter fun i => g i = 0).image
        fun i : ↥(pairIdx n) => (i : ℤ)) ∪
     (((Finset.univ : Finset ↥(pairIdx n)).filter fun i => g i = 1).image
        fun i : ↥(pairIdx n) => (n : ℤ) + 1 - (i : ℤ)))

/-- A sum-free `S ⊆ {1,…,n+1}` containing `n+1` is recovered from its pairing
statuses. -/
theorem pairRecover_pairStatus {n : ℕ} {S : Finset ℤ}
    (hS : S ∈ (sumFreeSets (n + 1)).filter fun s => ((n : ℤ) + 1) ∈ s) :
    pairRecover n (pairStatus n S) = S := by
  rw [Finset.mem_filter, mem_sumFreeSets] at hS
  obtain ⟨⟨hsub, hsf⟩, hMS⟩ := hS
  ext j
  constructor
  · intro hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact hMS
    rcases Finset.mem_union.mp hj with hj | hj
    · rcases Finset.mem_image.mp hj with ⟨i, hi, rfl⟩
      obtain ⟨_, h0⟩ := Finset.mem_filter.mp hi
      by_contra hc
      have h0' : pairStatus n S i = 0 := h0
      unfold pairStatus at h0'
      rw [ite_eq_right hc] at h0'
      split at h0' <;> exact absurd h0' (by decide)
    · rcases Finset.mem_image.mp hj with ⟨i, hi, hieq⟩
      obtain ⟨_, h1⟩ := Finset.mem_filter.mp hi
      subst hieq
      by_contra hc
      have h1' : pairStatus n S i = 1 := h1
      unfold pairStatus at h1'
      by_cases hmem : (i : ℤ) ∈ S
      · rw [ite_eq_left hmem] at h1'; exact absurd h1' (by decide)
      · rw [ite_eq_right hmem, ite_eq_right hc] at h1'; exact absurd h1' (by decide)
  · intro hj
    have hjI : j ∈ Finset.Icc (1 : ℤ) (((n + 1 : ℕ)) : ℤ) := hsub hj
    rw [Finset.mem_Icc] at hjI
    rcases eq_or_ne j ((n : ℤ) + 1) with rfl | hne
    · exact Finset.mem_insert_self _ _
    have hjn : j ≤ (n : ℤ) := by omega
    by_cases hjk : j ≤ ((n / 2 : ℕ) : ℤ)
    · -- `j` is the first member of its pair
      have hmemI : j ∈ pairIdx n := by
        show j ∈ Finset.Icc (1 : ℤ) ((n / 2 : ℕ) : ℤ)
        rw [Finset.mem_Icc]; exact ⟨hjI.1, hjk⟩
      apply Finset.mem_insert.mpr; right
      apply Finset.mem_union.mpr; left
      apply Finset.mem_image.mpr
      refine ⟨⟨j, hmemI⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
      unfold pairStatus
      exact ite_eq_left hj
    · -- `j > ⌊n/2⌋`; either it is a second member, or the excluded middle
      have hjk' : ((n / 2 : ℕ) : ℤ) < j := lt_of_not_ge hjk
      by_cases hik : (n : ℤ) + 1 - j ≤ ((n / 2 : ℕ) : ℤ)
      · have hmemI : (n : ℤ) + 1 - j ∈ pairIdx n := by
          show (n : ℤ) + 1 - j ∈ Finset.Icc (1 : ℤ) ((n / 2 : ℕ) : ℤ)
          rw [Finset.mem_Icc]; constructor <;> omega
        have hnot : ¬ ((⟨(n : ℤ) + 1 - j, hmemI⟩ : ↥(pairIdx n)) : ℤ) ∈ S := by
          intro h1
          have hsum := hsf _ h1 _ hj
          have heq : ((⟨(n : ℤ) + 1 - j, hmemI⟩ : ↥(pairIdx n)) : ℤ) + j
              = (n : ℤ) + 1 := by
            show (n : ℤ) + 1 - j + j = (n : ℤ) + 1
            ring
          rw [heq] at hsum
          exact hsum hMS
        have hin : (n : ℤ) + 1 -
            ((⟨(n : ℤ) + 1 - j, hmemI⟩ : ↥(pairIdx n)) : ℤ) ∈ S := by
          rw [show ((⟨(n : ℤ) + 1 - j, hmemI⟩ : ↥(pairIdx n)) : ℤ)
              = (n : ℤ) + 1 - j from rfl]
          rw [show (n : ℤ) + 1 - ((n : ℤ) + 1 - j) = j from by ring]
          exact hj
        apply Finset.mem_insert.mpr; right
        apply Finset.mem_union.mpr; right
        apply Finset.mem_image.mpr
        refine ⟨⟨(n : ℤ) + 1 - j, hmemI⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
        · unfold pairStatus
          rw [ite_eq_right hnot, ite_eq_left hin]
        · show (n : ℤ) + 1 - ((n : ℤ) + 1 - j) = j
          ring
      · -- the excluded middle: `2j = n+1`, so `j + j = n+1 ∈ S` contradicts
        -- sum-freeness
        have hik' : ((n / 2 : ℕ) : ℤ) < (n : ℤ) + 1 - j := lt_of_not_ge hik
        exfalso
        have hjj : j + j = (n : ℤ) + 1 := by omega
        have hsum := hsf _ hj _ hj
        rw [hjj] at hsum
        exact hsum hMS

/-- At most `3^(n/2)` sum-free subsets of `{1,…,n+1}` contain `n+1`:
inject into `{1,…,⌊n/2⌋} → Fin 3` via the pairing statuses. -/
theorem card_sumFreeSets_mem_succ_le (n : ℕ) :
    ((sumFreeSets (n + 1)).filter fun s => ((n : ℤ) + 1) ∈ s).card
      ≤ 3 ^ (n / 2) := by
  classical
  have hinj : Set.InjOn (pairStatus n)
      ((sumFreeSets (n + 1)).filter fun s => ((n : ℤ) + 1) ∈ s) := by
    intro S₁ h₁ S₂ h₂ hst
    rw [← pairRecover_pairStatus h₁, ← pairRecover_pairStatus h₂, hst]
  calc ((sumFreeSets (n + 1)).filter fun s => ((n : ℤ) + 1) ∈ s).card
      ≤ (Finset.univ : Finset (↥(pairIdx n) → Fin 3)).card :=
        Finset.card_le_card_of_injOn _ (fun _ _ => Finset.mem_univ _) hinj
    _ = 3 ^ (n / 2) := by
        rw [Finset.card_univ, Fintype.card_fun, Fintype.card_coe, card_pairIdx,
          Fintype.card_fin]

/-- The sum-free subsets of `{1,…,n+1}` avoiding `n+1` are exactly the
sum-free subsets of `{1,…,n}`. -/
theorem sumFreeSets_succ_filter_neg (n : ℕ) :
    (sumFreeSets (n + 1)).filter (fun s => ((n : ℤ) + 1) ∉ s) = sumFreeSets n := by
  ext S
  simp only [Finset.mem_filter, mem_sumFreeSets]
  constructor
  · rintro ⟨⟨hsub, hsf⟩, hn⟩
    refine ⟨fun x hx => ?_, hsf⟩
    have hxI : x ∈ Finset.Icc (1 : ℤ) (((n + 1 : ℕ)) : ℤ) := hsub hx
    rw [Finset.mem_Icc] at hxI
    have hle : x ≤ (n : ℤ) := by
      rcases eq_or_ne x ((n : ℤ) + 1) with rfl | hne
      · exact absurd hx hn
      · omega
    show x ∈ Finset.Icc (1 : ℤ) ((n : ℕ) : ℤ)
    rw [Finset.mem_Icc]; exact ⟨hxI.1, hle⟩
  · rintro ⟨hsub, hsf⟩
    refine ⟨⟨fun x hx => ?_, hsf⟩, ?_⟩
    · have hxI : x ∈ Finset.Icc (1 : ℤ) ((n : ℕ) : ℤ) := hsub hx
      rw [Finset.mem_Icc] at hxI
      show x ∈ Finset.Icc (1 : ℤ) (((n + 1 : ℕ)) : ℤ)
      rw [Finset.mem_Icc]; exact ⟨hxI.1, by omega⟩
    · intro hn
      have hxI : (n : ℤ) + 1 ∈ Finset.Icc (1 : ℤ) ((n : ℕ) : ℤ) := hsub hn
      rw [Finset.mem_Icc] at hxI
      omega

/-- The recurrence `sumFreeCount (n+1) ≤ sumFreeCount n + 3^(n/2)`. -/
theorem sumFreeCount_succ_le (n : ℕ) :
    sumFreeCount (n + 1) ≤ sumFreeCount n + 3 ^ (n / 2) := by
  have h := Finset.card_filter_add_card_filter_not (s := sumFreeSets (n + 1))
    (p := fun s => ((n : ℤ) + 1) ∈ s)
  rw [sumFreeSets_succ_filter_neg] at h
  have hle := card_sumFreeSets_mem_succ_le n
  unfold sumFreeCount
  omega

/-- Weaker bound used for the base cases. -/
theorem sumFreeCount_le_two_pow (n : ℕ) : sumFreeCount n ≤ 2 ^ n := by
  calc sumFreeCount n ≤ ((interval n).powerset).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
    _ = 2 ^ n := by rw [Finset.card_powerset, card_interval]

/-- `sumFreeCount n ≤ 2 * 3^(n/2)` by two-step induction. -/
theorem sumFreeCount_le_two_mul_three_pow (n : ℕ) :
    sumFreeCount n ≤ 2 * 3 ^ (n / 2) := by
  induction n using Nat.twoStepInduction with
  | zero =>
      exact le_trans (sumFreeCount_le_two_pow 0) (by norm_num)
  | one =>
      exact le_trans (sumFreeCount_le_two_pow 1) (by norm_num)
  | more k hk _ =>
      have h1 : sumFreeCount (k + 2) ≤ sumFreeCount (k + 1) + 3 ^ ((k + 1) / 2) :=
        sumFreeCount_succ_le (k + 1)
      have h2 := sumFreeCount_succ_le k
      have hpow : 3 ^ ((k + 1) / 2) ≤ 3 * 3 ^ (k / 2) := by
        calc 3 ^ ((k + 1) / 2) ≤ 3 ^ (k / 2 + 1) :=
              pow_le_pow_right₀ (by norm_num) (by omega)
          _ = 3 * 3 ^ (k / 2) := by rw [pow_succ']
      have hdiv : (k + 2) / 2 = k / 2 + 1 := by omega
      rw [hdiv, pow_succ']
      omega

/-- The bound transfers to `maxSumFreeCount`. -/
theorem maxSumFreeCount_le_two_mul_three_pow (n : ℕ) :
    maxSumFreeCount n ≤ 2 * 3 ^ (n / 2) :=
  le_trans (maxSumFreeCount_le_sumFreeCount n) (sumFreeCount_le_two_mul_three_pow n)

/-- Taking `log₂`: `log₂ f(n) ≤ 1 + (n/2) log₂ 3`. -/
theorem logb_two_maxSumFreeCount_le_pair (n : ℕ) :
    Real.logb 2 (maxSumFreeCount n : ℝ) ≤ 1 + (n : ℝ) / 2 * Real.logb 2 3 := by
  have hb : (1 : ℝ) < 2 := by norm_num
  have hpos : (0 : ℝ) < (maxSumFreeCount n : ℝ) := by
    exact_mod_cast maxSumFreeCount_pos n
  have hbound : (0 : ℝ) < ((2 * 3 ^ (n / 2) : ℕ) : ℝ) := by
    have h : 0 < 2 * 3 ^ (n / 2) := by positivity
    exact_mod_cast h
  have hle : (maxSumFreeCount n : ℝ) ≤ ((2 * 3 ^ (n / 2) : ℕ) : ℝ) := by
    exact_mod_cast maxSumFreeCount_le_two_mul_three_pow n
  calc Real.logb 2 (maxSumFreeCount n : ℝ)
      ≤ Real.logb 2 ((2 * 3 ^ (n / 2) : ℕ) : ℝ) :=
        (Real.logb_le_logb hb hpos hbound).mpr hle
    _ = Real.logb 2 2 + Real.logb 2 ((3 : ℝ) ^ (n / 2)) := by
        push_cast
        rw [Real.logb_mul (by norm_num) (pow_ne_zero _ (by norm_num))]
    _ = 1 + (n / 2 : ℕ) * Real.logb 2 3 := by
        rw [Real.logb_pow, Real.logb_self_eq_one hb]
    _ ≤ 1 + (n : ℝ) / 2 * Real.logb 2 3 := by
        have hL : (0 : ℝ) ≤ Real.logb 2 3 :=
          (Real.logb_pos hb (by norm_num)).le
        have hd : ((n / 2 : ℕ) : ℝ) ≤ (n : ℝ) / 2 := Nat.cast_div_le
        gcongr

/-- Dividing by `n`: eventually `log₂ f(n)/n ≤ log₂ 3 / 2 + ε`. -/
theorem logb_ratio_eventually_le_logb3_half {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in Filter.atTop,
      Real.logb 2 (maxSumFreeCount n : ℝ) / (n : ℝ) ≤ Real.logb 2 3 / 2 + ε := by
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
  have hε' : (0 : ℝ) < 1 / ε := by positivity
  have hNpos : (0 : ℝ) < N := hε'.trans hN
  filter_upwards [Filter.eventually_ge_atTop N] with n hn
  have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := hNpos.trans_le hNn
  have hn0 : (n : ℝ) ≠ 0 := hnpos.ne'
  have hinv : (1 : ℝ) / n ≤ ε := by
    have h1 : (1 : ℝ) / n ≤ 1 / N := one_div_le_one_div_of_le hNpos hNn
    have h2 : (1 : ℝ) / N < ε := by
      rw [← one_div_one_div ε]
      exact one_div_lt_one_div_of_lt hε' hN
    exact h1.trans h2.le
  have hbound := logb_two_maxSumFreeCount_le_pair n
  calc Real.logb 2 (maxSumFreeCount n : ℝ) / (n : ℝ)
      ≤ (1 + (n : ℝ) / 2 * Real.logb 2 3) / (n : ℝ) := by
        apply div_le_div_of_nonneg_right hbound
        exact hnpos.le
    _ = 1 / n + Real.logb 2 3 / 2 := by field_simp
    _ ≤ ε + Real.logb 2 3 / 2 := by linarith
    _ = Real.logb 2 3 / 2 + ε := by ring

/-- `log₂ 3 < 8/5` since `3^5 = 243 < 256 = 2^8`. -/
theorem logb_two_three_lt : Real.logb 2 3 < 8 / 5 := by
  have hb : (1 : ℝ) < 2 := by norm_num
  have h1 : Real.logb 2 ((3 : ℝ) ^ 5) < Real.logb 2 ((2 : ℝ) ^ 8) :=
    Real.logb_lt_logb hb (by positivity) (by norm_num)
  rw [Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one hb] at h1
  norm_num at h1
  linarith

/-- Consequently `log₂ f(n)/n ≤ 4/5` eventually. -/
theorem logb_ratio_eventually_le_four_fifths :
    ∀ᶠ n : ℕ in Filter.atTop,
      Real.logb 2 (maxSumFreeCount n : ℝ) / (n : ℝ) ≤ 4 / 5 := by
  have hε : (0 : ℝ) < 4 / 5 - Real.logb 2 3 / 2 := by
    have h := logb_two_three_lt
    linarith
  filter_upwards [logb_ratio_eventually_le_logb3_half hε] with n hn
  have : Real.logb 2 3 / 2 + (4 / 5 - Real.logb 2 3 / 2) = 4 / 5 := by ring
  linarith

end JSP000728
