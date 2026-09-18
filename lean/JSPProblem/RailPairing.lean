import JSPProblem.TwoMin
import JSPProblem.Ladder

/-!
# JSP-000728 — rail pairing for the two-shift bound

Fix `1 ≤ m < s`.  Inside `Icc (s + 1) n` the `s`-shift acts within each
residue class `cls n s r` (`r ∈ Icc 1 s`), while the `m`-shift couples
class `r` to class `r + m`.  For `r ≤ s - m` the pair `{r, r + m}` stays
inside `Icc 1 s` (no wrap-around); the *leftover* rails are
`r ∈ Icc (s - m + 1) m`, an empty interval when `s ≥ 2m`.

* `Icc_subset_biUnion_pairCls` : `Icc (s+1) n` is covered by the paired
  unions `cls n s r ∪ cls n s (r + m)` (`r ∈ Icc 1 (s-m)`) together with
  the leftover classes `cls n s ρ` (`ρ ∈ Icc (s-m+1) m`).
* `card_powerset_filter_shiftFree2_Icc_le_pairProd` : conditional product
  bound — given a per-pair estimate `4 · ladSets (L+1)`, the
  `shiftFree2 m s` subsets of `Icc (s+1) n` are at most the paired product
  times the Fibonacci factors of the leftover rails (which only retain
  the `s`-shift constraint, `shiftFree2.2`).
* `fib_add_two_le_two_pow` : `F_{L+2} ≤ 2^{L+1}`.
* `card_powerset_filter_shiftFree2_Icc_le_twelve_mul` : the closed bound
  `card ≤ 12^{(s-m)₊} · (5^{(n-s)₊ + (s-m)₊} · 2^{(2m-s)₊})`, obtained by
  `ladSets_card_le_three_mul_five_pow`, `fib_add_two_le_two_pow` and the
  length accounting `Σ_{pairs} L + Σ_{leftover} L ≤ (n-s)₊`.
-/

namespace JSP000728

/-- **Pairing cover.**  Every `x ∈ Icc (s+1) n` lies in some class
`cls n s r` with `r ∈ Icc 1 s`; if `r ≤ s - m` it is the first member of
pair `r`, if `m < r` it is the second member of pair `r - m`, and
otherwise `s - m < r ≤ m` is a leftover rail. -/
theorem Icc_subset_biUnion_pairCls {n : ℕ} {m s : ℤ} (hm : 1 ≤ m)
    (hms : m < s) :
    Finset.Icc (s + 1) (n : ℤ) ⊆
      (Finset.Icc 1 (s - m)).biUnion (fun r => cls n s r ∪ cls n s (r + m)) ∪
        (Finset.Icc (s - m + 1) m).biUnion (cls n s) := by
  have hs : 1 ≤ s := by omega
  intro x hx
  obtain ⟨r, hr, hxr⟩ := Finset.mem_biUnion.mp (Icc_subset_biUnion_cls hs hx)
  rw [Finset.mem_Icc] at hr
  rw [Finset.mem_union, Finset.mem_biUnion, Finset.mem_biUnion]
  rcases lt_or_ge (s - m) r with h | h
  · rcases lt_or_ge m r with h2 | h2
    · refine Or.inl ⟨r - m, ?_, ?_⟩
      · rw [Finset.mem_Icc]
        omega
      · rw [Finset.mem_union]
        refine Or.inr ?_
        have e : r - m + m = r := by omega
        rwa [e]
    · exact Or.inr ⟨r, by rw [Finset.mem_Icc]; omega, hxr⟩
  · exact Or.inl ⟨r, by rw [Finset.mem_Icc]; omega,
      Finset.mem_union.mpr (Or.inl hxr)⟩

/-- **Conditional paired product bound.**  If each pair of rails
`cls n s r ∪ cls n s (r + m)` admits the estimate `4 · ladSets (L+1)`,
the double-shift-free subsets of `Icc (s+1) n` are bounded by the product
over pairs times the Fibonacci counts of the leftover rails. -/
theorem card_powerset_filter_shiftFree2_Icc_le_pairProd {n : ℕ} {m s : ℤ}
    (hm : 1 ≤ m) (hms : m < s)
    (hpair : ∀ r ∈ Finset.Icc 1 (s - m),
      ((cls n s r ∪ cls n s (r + m)).powerset.filter (shiftFree2 m s)).card ≤
        4 * (ladSets ((((n : ℤ) - r) / s).toNat + 1)).card) :
    ((Finset.Icc (s + 1) (n : ℤ)).powerset.filter (shiftFree2 m s)).card ≤
      (∏ r ∈ Finset.Icc 1 (s - m),
          4 * (ladSets ((((n : ℤ) - r) / s).toNat + 1)).card) *
        ∏ ρ ∈ Finset.Icc (s - m + 1) m,
          Nat.fib ((((n : ℤ) - ρ) / s).toNat + 2) := by
  have hs : 1 ≤ s := by omega
  have hT := Icc_subset_biUnion_pairCls (n := n) hm hms
  have hA := card_powerset_filter_shiftFree2_le_prod (m := m) (s := s)
    (Finset.Icc 1 (s - m)) (fun r => cls n s r ∪ cls n s (r + m)) _
    Finset.Subset.rfl
  have hB := card_powerset_filter_shiftFree2_le_prod (m := m) (s := s)
    (Finset.Icc (s - m + 1) m) (cls n s) _ Finset.Subset.rfl
  have hA' : (((Finset.Icc 1 (s - m)).biUnion
        (fun r => cls n s r ∪ cls n s (r + m))).powerset.filter
        (shiftFree2 m s)).card ≤
      ∏ r ∈ Finset.Icc 1 (s - m),
        4 * (ladSets ((((n : ℤ) - r) / s).toNat + 1)).card :=
    hA.trans (Finset.prod_le_prod fun r hr => hpair r hr)
  have hB' : (((Finset.Icc (s - m + 1) m).biUnion (cls n s)).powerset.filter
        (shiftFree2 m s)).card ≤
      ∏ ρ ∈ Finset.Icc (s - m + 1) m,
        Nat.fib ((((n : ℤ) - ρ) / s).toNat + 2) := by
    refine hB.trans (Finset.prod_le_prod fun ρ hρ => ?_)
    have hmono : (cls n s ρ).powerset.filter (shiftFree2 m s) ⊆
        (cls n s ρ).powerset.filter (shiftFree s) := by
      intro t ht
      rw [Finset.mem_filter] at ht ⊢
      exact ⟨ht.1, ht.2.2⟩
    exact (Finset.card_le_card hmono).trans
      (le_of_eq (card_powerset_filter_shiftFree_cls (n := n) (m := s) (r := ρ) hs))
  exact (card_powerset_filter_shiftFree2_le_mul hT).trans
    (Nat.mul_le_mul hA' hB')

/-- `F_{L+2} ≤ 2^{L+1}`: the two-step recursion gives
`fib (k+4) = fib (k+2) + fib (k+3) ≤ 2^{k+1} + 2^{k+2} = 3·2^{k+1}
≤ 4·2^{k+1} = 2^{k+3}`. -/
theorem fib_add_two_le_two_pow (L : ℕ) : Nat.fib (L + 2) ≤ 2 ^ (L + 1) := by
  induction L using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more k ih ih1 =>
      show Nat.fib (k + 2 + 2) ≤ 2 ^ (k + 2 + 1)
      rw [Nat.fib_add_two]
      calc Nat.fib (k + 2) + Nat.fib (k + 2 + 1)
          ≤ 2 ^ (k + 1) + 2 ^ (k + 1 + 1) := add_le_add ih ih1
        _ = 3 * 2 ^ (k + 1) := by rw [pow_succ']; ring
        _ ≤ 4 * 2 ^ (k + 1) := by omega
        _ = 2 ^ (k + 2 + 1) := by
            rw [show k + 2 + 1 = k + 1 + 2 from rfl, pow_add]
            ring

/-- **Closed bound.**  Combining the paired product bound with
`ladSets_card_le_three_mul_five_pow` and `fib_add_two_le_two_pow`: the
pair factors contribute `12^{(s-m)₊} · 5^{Σ(L+1)}` and the leftover
factors `2^{Σ L + (2m-s)₊}`; since the two length sums total at most
`(n-s)₊` and `2 ≤ 5`, this collapses to
`12^{(s-m)₊} · 5^{(n-s)₊ + (s-m)₊} · 2^{(2m-s)₊}`. -/
theorem card_powerset_filter_shiftFree2_Icc_le_twelve_mul {n : ℕ} {m s : ℤ}
    (hm : 1 ≤ m) (hms : m < s)
    (hpair : ∀ r ∈ Finset.Icc 1 (s - m),
      ((cls n s r ∪ cls n s (r + m)).powerset.filter (shiftFree2 m s)).card ≤
        4 * (ladSets ((((n : ℤ) - r) / s).toNat + 1)).card) :
    ((Finset.Icc (s + 1) (n : ℤ)).powerset.filter (shiftFree2 m s)).card ≤
      12 ^ (s - m).toNat *
        (5 ^ (((n : ℤ) - s).toNat + (s - m).toNat) * 2 ^ (2 * m - s).toNat) := by
  have hs : 1 ≤ s := by omega
  have hcardP : (Finset.Icc 1 (s - m)).card = (s - m).toNat := by
    rw [Int.card_Icc]
    congr 1
    omega
  have hcardL : (Finset.Icc (s - m + 1) m).card = (2 * m - s).toNat := by
    rw [Int.card_Icc]
    congr 1
    omega
  have hpairProd :
      ∏ r ∈ Finset.Icc 1 (s - m),
          4 * (ladSets ((((n : ℤ) - r) / s).toNat + 1)).card ≤
        12 ^ (s - m).toNat *
          5 ^ ((∑ r ∈ Finset.Icc 1 (s - m), (((n : ℤ) - r) / s).toNat) +
            (s - m).toNat) := by
    calc ∏ r ∈ Finset.Icc 1 (s - m),
            4 * (ladSets ((((n : ℤ) - r) / s).toNat + 1)).card
        ≤ ∏ r ∈ Finset.Icc 1 (s - m),
            12 * 5 ^ ((((n : ℤ) - r) / s).toNat + 1) := by
          apply Finset.prod_le_prod
          intro r _
          calc 4 * (ladSets ((((n : ℤ) - r) / s).toNat + 1)).card
              ≤ 4 * (3 * 5 ^ ((((n : ℤ) - r) / s).toNat + 1)) :=
                Nat.mul_le_mul (le_refl 4)
                  (ladSets_card_le_three_mul_five_pow _)
            _ = 12 * 5 ^ ((((n : ℤ) - r) / s).toNat + 1) := by ring
      _ = 12 ^ (s - m).toNat *
            5 ^ ((∑ r ∈ Finset.Icc 1 (s - m), (((n : ℤ) - r) / s).toNat) +
              (s - m).toNat) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const,
            Finset.prod_pow_eq_pow_sum, hcardP, Finset.sum_add_distrib,
            Finset.sum_const, hcardP]
          simp only [smul_eq_mul, mul_one]
  have hleftProd :
      ∏ ρ ∈ Finset.Icc (s - m + 1) m,
          Nat.fib ((((n : ℤ) - ρ) / s).toNat + 2) ≤
        2 ^ ((∑ ρ ∈ Finset.Icc (s - m + 1) m, (((n : ℤ) - ρ) / s).toNat) +
          (2 * m - s).toNat) := by
    calc ∏ ρ ∈ Finset.Icc (s - m + 1) m,
            Nat.fib ((((n : ℤ) - ρ) / s).toNat + 2)
        ≤ ∏ ρ ∈ Finset.Icc (s - m + 1) m,
            2 ^ ((((n : ℤ) - ρ) / s).toNat + 1) :=
          Finset.prod_le_prod fun ρ _ => fib_add_two_le_two_pow _
      _ = 2 ^ ((∑ ρ ∈ Finset.Icc (s - m + 1) m, (((n : ℤ) - ρ) / s).toNat) +
            (2 * m - s).toNat) := by
          rw [Finset.prod_pow_eq_pow_sum, Finset.sum_add_distrib,
            Finset.sum_const, hcardL]
          simp only [smul_eq_mul, mul_one]
  have hdisj : Disjoint (Finset.Icc 1 (s - m)) (Finset.Icc (s - m + 1) m) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    rw [Finset.mem_Icc] at hx1 hx2
    omega
  have hsub12 : Finset.Icc 1 (s - m) ∪ Finset.Icc (s - m + 1) m ⊆
      Finset.Icc 1 s := by
    intro r hr
    rw [Finset.mem_union] at hr
    rcases hr with hr | hr <;> rw [Finset.mem_Icc] at hr ⊢ <;> omega
  have hsum12 :
      (∑ r ∈ Finset.Icc 1 (s - m), (((n : ℤ) - r) / s).toNat) +
        (∑ ρ ∈ Finset.Icc (s - m + 1) m, (((n : ℤ) - ρ) / s).toNat) ≤
          ((n : ℤ) - s).toNat := by
    rw [← Finset.sum_union hdisj]
    calc ∑ r ∈ Finset.Icc 1 (s - m) ∪ Finset.Icc (s - m + 1) m,
            (((n : ℤ) - r) / s).toNat
        ≤ ∑ r ∈ Finset.Icc 1 s, (((n : ℤ) - r) / s).toNat :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub12
            (fun r _ _ => Nat.zero_le _)
      _ = ((n : ℤ) - s).toNat := sum_cls_card hs
  have h2le : 2 ^ (∑ ρ ∈ Finset.Icc (s - m + 1) m, (((n : ℤ) - ρ) / s).toNat) ≤
      5 ^ (∑ ρ ∈ Finset.Icc (s - m + 1) m, (((n : ℤ) - ρ) / s).toNat) :=
    pow_le_pow_left₀ (Nat.zero_le _) (by norm_num) _
  have h5le : 5 ^ ((∑ r ∈ Finset.Icc 1 (s - m), (((n : ℤ) - r) / s).toNat) +
        (∑ ρ ∈ Finset.Icc (s - m + 1) m, (((n : ℤ) - ρ) / s).toNat)) ≤
      5 ^ ((n : ℤ) - s).toNat :=
    pow_le_pow_right₀ (by norm_num) hsum12
  calc ((Finset.Icc (s + 1) (n : ℤ)).powerset.filter (shiftFree2 m s)).card
      ≤ (∏ r ∈ Finset.Icc 1 (s - m),
            4 * (ladSets ((((n : ℤ) - r) / s).toNat + 1)).card) *
          ∏ ρ ∈ Finset.Icc (s - m + 1) m,
            Nat.fib ((((n : ℤ) - ρ) / s).toNat + 2) :=
        card_powerset_filter_shiftFree2_Icc_le_pairProd hm hms hpair
    _ ≤ (12 ^ (s - m).toNat *
          5 ^ ((∑ r ∈ Finset.Icc 1 (s - m), (((n : ℤ) - r) / s).toNat) +
            (s - m).toNat)) *
        2 ^ ((∑ ρ ∈ Finset.Icc (s - m + 1) m, (((n : ℤ) - ρ) / s).toNat) +
          (2 * m - s).toNat) :=
        Nat.mul_le_mul hpairProd hleftProd
    _ = (12 ^ (s - m).toNat *
          (5 ^ (s - m).toNat * 2 ^ (2 * m - s).toNat)) *
        (5 ^ (∑ r ∈ Finset.Icc 1 (s - m), (((n : ℤ) - r) / s).toNat) *
          2 ^ (∑ ρ ∈ Finset.Icc (s - m + 1) m, (((n : ℤ) - ρ) / s).toNat)) := by
        rw [pow_add, pow_add]
        ring
    _ ≤ (12 ^ (s - m).toNat *
          (5 ^ (s - m).toNat * 2 ^ (2 * m - s).toNat)) *
        (5 ^ (∑ r ∈ Finset.Icc 1 (s - m), (((n : ℤ) - r) / s).toNat) *
          5 ^ (∑ ρ ∈ Finset.Icc (s - m + 1) m, (((n : ℤ) - ρ) / s).toNat)) :=
        Nat.mul_le_mul (le_refl _) (Nat.mul_le_mul (le_refl _) h2le)
    _ = (12 ^ (s - m).toNat *
          (5 ^ (s - m).toNat * 2 ^ (2 * m - s).toNat)) *
        5 ^ ((∑ r ∈ Finset.Icc 1 (s - m), (((n : ℤ) - r) / s).toNat) +
          (∑ ρ ∈ Finset.Icc (s - m + 1) m, (((n : ℤ) - ρ) / s).toNat)) := by
        rw [← pow_add]
    _ ≤ (12 ^ (s - m).toNat *
          (5 ^ (s - m).toNat * 2 ^ (2 * m - s).toNat)) *
        5 ^ ((n : ℤ) - s).toNat :=
        Nat.mul_le_mul (le_refl _) h5le
    _ = 12 ^ (s - m).toNat *
          (5 ^ (((n : ℤ) - s).toNat + (s - m).toNat) *
            2 ^ (2 * m - s).toNat) := by
        rw [pow_add]
        ring

end JSP000728
