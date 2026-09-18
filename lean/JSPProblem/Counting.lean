import JSPProblem.Basic
import JSPProblem.UpperHalf
import JSPProblem.Odds
import JSPProblem.ThirdFamily
import JSPProblem.PairFamily
import JSPProblem.SingleFamily

/-!
# JSP-000728 — counting inclusion-maximal sum-free subsets: lower bounds

The sharp asymptotic is `f(n) = 2 ^ ((1/4 + o(1)) * n)` (BLST 2015/2018).
Here we record the elementary lower bounds obtainable from the explicit
maximal sum-free families proved in the sibling files:

* `upperHalf n` and `odds n` are maximal sum-free for every `n`, and distinct
  for `n ≥ 2`  ⇒  `f n ≥ 2`.
* `thirdSet m` is maximal sum-free in `{1, …, 3m}` for `m ≥ 1`, and distinct
  from the first two for `m ≥ 2`  ⇒  `f (3m) ≥ 3`.
* `pairSet m` is maximal sum-free in `{1, …, 3m+2}` for `m ≥ 2`, and distinct
  from the first two  ⇒  `f (3m + 2) ≥ 3`.
-/

namespace JSP000728

private theorem ne_of_mem_not_mem {s t : Finset ℤ} {x : ℤ} (hx : x ∈ s)
    (hx' : x ∉ t) : s ≠ t := fun h => hx' (h ▸ hx)

private theorem mem_thirdSet {m : ℕ} {x : ℤ} :
    x ∈ thirdSet m ↔
      x = (m : ℤ) ∨ (2 * (m : ℤ) + 1 ≤ x ∧ x ≤ 3 * (m : ℤ)) := by
  rw [thirdSet, Finset.mem_insert, Finset.mem_Icc]

private theorem mem_pairSet {m : ℕ} {x : ℤ} :
    x ∈ pairSet m ↔
      x = (m : ℤ) ∨ x = (m : ℤ) + 1 ∨
        (2 * (m : ℤ) + 3 ≤ x ∧ x ≤ 3 * (m : ℤ) + 2) := by
  rw [pairSet, Finset.mem_insert, Finset.mem_insert, Finset.mem_Icc]

private theorem one_mem_odds {n : ℕ} (hn : 2 ≤ n) : (1 : ℤ) ∈ odds n := by
  rw [mem_odds]
  have hn' : (2 : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
  exact ⟨Finset.mem_Icc.mpr ⟨le_refl _, by omega⟩, by norm_num⟩

private theorem one_not_mem_upperHalf {n : ℕ} (hn : 2 ≤ n) :
    (1 : ℤ) ∉ upperHalf n := by
  rw [mem_upperHalf]
  have hn' : (2 : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
  rintro ⟨_, hlt⟩
  omega

/-- Every interval `{1, …, n}` with `n ≥ 2` has at least two
inclusion-maximal sum-free subsets: the odds and the upper half. -/
theorem two_le_maxSumFreeCount {n : ℕ} (hn : 2 ≤ n) :
    2 ≤ maxSumFreeCount n := by
  have hu : upperHalf n ∈ maxSumFreeSets n :=
    mem_maxSumFreeSets.mpr (upperHalf_isMaxSumFree n)
  have ho : odds n ∈ maxSumFreeSets n :=
    mem_maxSumFreeSets.mpr (odds_isMaxSumFree n)
  have hne : upperHalf n ≠ odds n :=
    (ne_of_mem_not_mem (one_mem_odds hn) (one_not_mem_upperHalf hn)).symm
  have hsub : ({upperHalf n, odds n} : Finset (Finset ℤ)) ⊆ maxSumFreeSets n := by
    intro s hs
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl
    · exact hu
    · exact ho
  have hcard : ({upperHalf n, odds n} : Finset (Finset ℤ)).card = 2 :=
    Finset.card_pair hne
  calc 2 = _ := hcard.symm
    _ ≤ maxSumFreeCount n := Finset.card_le_card hsub

/-- For `m ≥ 2` the interval `{1, …, 3m}` has at least three
inclusion-maximal sum-free subsets. -/
theorem three_le_maxSumFreeCount_mul_three {m : ℕ} (hm : 2 ≤ m) :
    3 ≤ maxSumFreeCount (3 * m) := by
  have h1m : (1 : ℤ) ≤ (m : ℤ) := by exact_mod_cast (by omega : (1 : ℕ) ≤ m)
  have ht : thirdSet m ∈ maxSumFreeSets (3 * m) :=
    mem_maxSumFreeSets.mpr (thirdSet_isMaxSumFree (by omega))
  have hu : upperHalf (3 * m) ∈ maxSumFreeSets (3 * m) :=
    mem_maxSumFreeSets.mpr (upperHalf_isMaxSumFree _)
  have ho : odds (3 * m) ∈ maxSumFreeSets (3 * m) :=
    mem_maxSumFreeSets.mpr (odds_isMaxSumFree _)
  have hne_tu : thirdSet m ≠ upperHalf (3 * m) := by
    apply ne_of_mem_not_mem (x := (m : ℤ)) (Finset.mem_insert_self _ _)
    rw [mem_upperHalf]
    rintro ⟨_, hlt⟩
    norm_num at hlt
    omega
  have hne_to : thirdSet m ≠ odds (3 * m) := by
    rcases Int.emod_two_eq_zero_or_one (m : ℤ) with hm2 | hm2
    · apply ne_of_mem_not_mem (x := (m : ℤ)) (Finset.mem_insert_self _ _)
      rw [mem_odds]
      rintro ⟨_, hlt⟩
      omega
    · apply ne_of_mem_not_mem (x := 2 * (m : ℤ) + 2)
      · rw [mem_thirdSet]; right; omega
      · rw [mem_odds]
        rintro ⟨_, hlt⟩
        omega
  have hne_uo : upperHalf (3 * m) ≠ odds (3 * m) :=
    (ne_of_mem_not_mem (one_mem_odds (by omega)) (one_not_mem_upperHalf (by omega))).symm
  have hsub :
      ({thirdSet m, upperHalf (3 * m), odds (3 * m)} : Finset (Finset ℤ)) ⊆
        maxSumFreeSets (3 * m) := by
    intro s hs
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl | rfl
    · exact ht
    · exact hu
    · exact ho
  have hcard :
      ({thirdSet m, upperHalf (3 * m), odds (3 * m)} : Finset (Finset ℤ)).card = 3 :=
    Finset.card_triple_eq_three_iff.mpr ⟨hne_tu, hne_to, hne_uo⟩
  calc 3 = _ := hcard.symm
    _ ≤ maxSumFreeCount (3 * m) := Finset.card_le_card hsub

/-- For `m ≥ 2` the interval `{1, …, 3m + 2}` has at least three
inclusion-maximal sum-free subsets. -/
theorem three_le_maxSumFreeCount_mul_three_add_two {m : ℕ} (hm : 2 ≤ m) :
    3 ≤ maxSumFreeCount (3 * m + 2) := by
  have h1m : (1 : ℤ) ≤ (m : ℤ) := by exact_mod_cast (by omega : (1 : ℕ) ≤ m)
  have ht : pairSet m ∈ maxSumFreeSets (3 * m + 2) :=
    mem_maxSumFreeSets.mpr (pairSet_isMaxSumFree hm)
  have hu : upperHalf (3 * m + 2) ∈ maxSumFreeSets (3 * m + 2) :=
    mem_maxSumFreeSets.mpr (upperHalf_isMaxSumFree _)
  have ho : odds (3 * m + 2) ∈ maxSumFreeSets (3 * m + 2) :=
    mem_maxSumFreeSets.mpr (odds_isMaxSumFree _)
  have hne_pu : pairSet m ≠ upperHalf (3 * m + 2) := by
    apply ne_of_mem_not_mem (x := (m : ℤ))
    · rw [mem_pairSet]; left; rfl
    · rw [mem_upperHalf]
      rintro ⟨_, hlt⟩
      norm_num at hlt
      omega
  have hne_po : pairSet m ≠ odds (3 * m + 2) := by
    rcases Int.emod_two_eq_zero_or_one (m : ℤ) with hm2 | hm2
    · apply ne_of_mem_not_mem (x := (m : ℤ))
      · rw [mem_pairSet]; left; rfl
      · rw [mem_odds]
        rintro ⟨_, hlt⟩
        omega
    · apply ne_of_mem_not_mem (x := (m : ℤ) + 1)
      · rw [mem_pairSet]; right; left; rfl
      · rw [mem_odds]
        rintro ⟨_, hlt⟩
        omega
  have hne_uo : upperHalf (3 * m + 2) ≠ odds (3 * m + 2) :=
    (ne_of_mem_not_mem (one_mem_odds (by omega)) (one_not_mem_upperHalf (by omega))).symm
  have hsub :
      ({pairSet m, upperHalf (3 * m + 2), odds (3 * m + 2)} : Finset (Finset ℤ)) ⊆
        maxSumFreeSets (3 * m + 2) := by
    intro s hs
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl | rfl
    · exact ht
    · exact hu
    · exact ho
  have hcard :
      ({pairSet m, upperHalf (3 * m + 2), odds (3 * m + 2)} : Finset (Finset ℤ)).card
        = 3 :=
    Finset.card_triple_eq_three_iff.mpr ⟨hne_pu, hne_po, hne_uo⟩
  calc 3 = _ := hcard.symm
    _ ≤ maxSumFreeCount (3 * m + 2) := Finset.card_le_card hsub

/-- For `m ≥ 2` the interval `{1, …, 3m + 1}` has at least three
inclusion-maximal sum-free subsets. -/
theorem three_le_maxSumFreeCount_mul_three_add_one {m : ℕ} (hm : 2 ≤ m) :
    3 ≤ maxSumFreeCount (3 * m + 1) := by
  have ht : singleSet m ∈ maxSumFreeSets (3 * m + 1) :=
    mem_maxSumFreeSets.mpr (singleSet_isMaxSumFree (by omega))
  have hu : upperHalf (3 * m + 1) ∈ maxSumFreeSets (3 * m + 1) :=
    mem_maxSumFreeSets.mpr (upperHalf_isMaxSumFree _)
  have ho : odds (3 * m + 1) ∈ maxSumFreeSets (3 * m + 1) :=
    mem_maxSumFreeSets.mpr (odds_isMaxSumFree _)
  have hne_su : singleSet m ≠ upperHalf (3 * m + 1) := by
    apply ne_of_mem_not_mem (x := (m : ℤ))
    · rw [mem_singleSet]; left; rfl
    · rw [mem_upperHalf]
      rintro ⟨_, hlt⟩
      norm_num at hlt
      omega
  have hne_so : singleSet m ≠ odds (3 * m + 1) := by
    rcases Int.emod_two_eq_zero_or_one (m : ℤ) with hm2 | hm2
    · apply ne_of_mem_not_mem (x := (m : ℤ))
      · rw [mem_singleSet]; left; rfl
      · rw [mem_odds]
        rintro ⟨_, hlt⟩
        omega
    · apply ne_of_mem_not_mem (x := 2 * (m : ℤ) + 2)
      · rw [mem_singleSet]; right; omega
      · rw [mem_odds]
        rintro ⟨_, hlt⟩
        omega
  have hne_uo : upperHalf (3 * m + 1) ≠ odds (3 * m + 1) :=
    (ne_of_mem_not_mem (one_mem_odds (by omega)) (one_not_mem_upperHalf (by omega))).symm
  have hsub :
      ({singleSet m, upperHalf (3 * m + 1), odds (3 * m + 1)} : Finset (Finset ℤ)) ⊆
        maxSumFreeSets (3 * m + 1) := by
    intro s hs
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl | rfl
    · exact ht
    · exact hu
    · exact ho
  have hcard :
      ({singleSet m, upperHalf (3 * m + 1), odds (3 * m + 1)} : Finset (Finset ℤ)).card
        = 3 :=
    Finset.card_triple_eq_three_iff.mpr ⟨hne_su, hne_so, hne_uo⟩
  calc 3 = _ := hcard.symm
    _ ≤ maxSumFreeCount (3 * m + 1) := Finset.card_le_card hsub

/-- Every interval `{1, …, n}` with `n ≥ 6` has at least three
inclusion-maximal sum-free subsets. -/
theorem three_le_maxSumFreeCount {n : ℕ} (hn : 6 ≤ n) :
    3 ≤ maxSumFreeCount n := by
  have hdiv : n = 3 * (n / 3) + n % 3 := (Nat.div_add_mod n 3).symm
  have hmod : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases hmod with h | h | h
  · rw [show n = 3 * (n / 3) by omega]
    exact three_le_maxSumFreeCount_mul_three (by omega)
  · rw [show n = 3 * (n / 3) + 1 by omega]
    exact three_le_maxSumFreeCount_mul_three_add_one (by omega)
  · rw [show n = 3 * (n / 3) + 2 by omega]
    exact three_le_maxSumFreeCount_mul_three_add_two (by omega)

end JSP000728
