import JSPProblem.TwoMin
import JSPProblem.TwoMinBound
import JSPProblem.NoConsec

/-!
# JSP-000728 — the large-`s` regime: the matching bound on `Icc (s+1) n`

When `n ≤ 2s` the `s`-shift constraint is vacuous on `Icc (s + 1) n`
(every `x ≥ s + 1` has `x + s ≥ 2s + 1 > n`), so `shiftFree2 m s`
collapses to `shiftFree m` — see `shiftFree2_iff_shiftFree_of_vacuous`
in `TwoMinBound` for the strict version and
`shiftFree2_iff_shiftFree_of_vacuous_le` below for the boundary `n = 2s`.

This file bounds the `m`-shift-free subset count of `Icc (s + 1) n` by a
**matching argument** rather than by the residue-class factorisation
(`card_powerset_filter_shiftFree_Icc_le` = `∏ fib` in `TwoMinBound`):
the `N = n - s` elements are covered by the (overlapping, but the product
bound tolerates that) shift-pairs `{x, x + m}` for `x ∈ Icc (s+1) (n-m)`
together with the leftover middle interval `Icc (n-m+1) (s+m)` — which is
empty exactly when `n ≥ s + 2m`, and which is *disjoint* from the
pair-partners when `n ≤ s + 2m`, where the bound is sharp:

  `card ≤ 3^{(n-s-m)₊} · 2^{(s+2m-n)₊}`
  (`card_powerset_filter_shiftFree_Icc_le_matchBound`).

Each pair contributes its `3` shift-free subsets (`∅`, `{x}`, `{x+m}` —
`card_powerset_filter_shiftFree_pair`), each leftover element `2`.

In the regime `n ≤ s + 2m` the pairs are disjoint and cover all but the
`2m - (n-s)` middle elements, so this is the honest matching bound
`3^{#pairs}·2^{#singles}`.  It beats the golden-ratio bound
`φ^{(n-s) + min(m, n-s)}` when `m` is close to `s` (e.g. `m = s - 1`,
`n = 2s` gives `3·2^{s-2}` vs `φ^{2s-1}`).

The `≤ 3^{n-s}` corollary (`secondMinClass_card_le_of_half_le`) is the
clean packaged form: when `n - s ≤ m` every subset is shift-free and
`card ≤ 2^{n-s} ≤ 3^{n-s}`; when `m < n - s` the matching bound applies
with `2^{(s+2m-n)₊} ≤ 3^{(s+2m-n)₊}` and
`(n-s-m)₊ + (s+2m-n)₊ ≤ (n-s)₊`.
-/

namespace JSP000728

/-- **A single shift-pair contributes a factor of `3`.**  Of the four
subsets of `{x, x + m}` (with `m ≠ 0`), only `{x, x + m}` itself fails
`shiftFree m`. -/
theorem card_powerset_filter_shiftFree_pair {x m : ℤ} (hm : m ≠ 0) :
    (({x, x + m} : Finset ℤ).powerset.filter (shiftFree m)).card = 3 := by
  have hxm : x ≠ x + m := by
    intro h
    exact hm (by omega)
  have hsf_iff : ∀ t : Finset ℤ, t ⊆ ({x, x + m} : Finset ℤ) →
      (shiftFree m t ↔ t ≠ ({x, x + m} : Finset ℤ)) := by
    intro t ht
    constructor
    · intro hsf heq
      subst heq
      exact hsf x (Finset.mem_insert_self _ _)
        (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self _)))
    · intro hne y hy hym
      apply hne
      have hy1 := Finset.mem_insert.mp (ht hy)
      have hy2 := Finset.mem_insert.mp (ht hym)
      have hyx : y = x := by
        rcases hy1 with h | h
        · exact h
        · rw [Finset.mem_singleton] at h
          rcases hy2 with h2 | h2
          · omega
          · rw [Finset.mem_singleton] at h2
            omega
      subst hyx
      apply Finset.Subset.antisymm ht
      intro z hz
      rw [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact hy
      · exact hym
  have hset : ({x, x + m} : Finset ℤ).powerset.filter (shiftFree m) =
      ({x, x + m} : Finset ℤ).powerset.erase {x, x + m} := by
    ext t
    rw [Finset.mem_filter, Finset.mem_powerset, Finset.mem_erase,
      Finset.mem_powerset]
    constructor
    · rintro ⟨ht, hsf⟩
      exact ⟨(hsf_iff t ht).mp hsf, ht⟩
    · rintro ⟨hne, ht⟩
      exact ⟨ht, (hsf_iff t ht).mpr hne⟩
  rw [hset,
    Finset.card_erase_of_mem
      (Finset.mem_powerset.mpr (Finset.Subset.refl _)),
    Finset.card_powerset, Finset.card_pair hxm]
  norm_num

/-- **Matching bound.**  The shift-pairs `{x, x + m}` for
`x ∈ Icc (s+1) (n-m)` cover `Icc (s+1) (n-m)` (as bases) and
`Icc (s+1+m) n` (as partners); the only uncovered elements are the middle
`Icc (n-m+1) (s+m)` of size `(s + 2m - n)₊`.  Each pair has exactly `3`
shift-free subsets and each leftover element at most `2`, giving

  `card ≤ 3^{(n-s-m)₊} · 2^{(s+2m-n)₊}`.

For `n ≤ s + 2m` the pairs are pairwise disjoint, so this is the genuine
`3^{#pairs}·2^{#singles}` matching bound. -/
theorem card_powerset_filter_shiftFree_Icc_le_matchBound {n : ℕ} {m s : ℤ}
    (hm : 1 ≤ m) :
    ((Finset.Icc (s + 1) (n : ℤ)).powerset.filter (shiftFree m)).card ≤
      3 ^ ((n : ℤ) - s - m).toNat * 2 ^ (s + 2 * m - (n : ℤ)).toNat := by
  have hm0 : m ≠ 0 := by omega
  have hcov : Finset.Icc (s + 1) (n : ℤ) ⊆
      (Finset.Icc (s + 1) ((n : ℤ) - m)).biUnion
          (fun x => ({x, x + m} : Finset ℤ)) ∪
        Finset.Icc ((n : ℤ) - m + 1) (s + m) := by
    intro y hy
    rw [Finset.mem_Icc] at hy
    rw [Finset.mem_union, Finset.mem_biUnion]
    rcases le_or_gt y ((n : ℤ) - m) with h | h
    · exact Or.inl ⟨y, Finset.mem_Icc.mpr ⟨hy.1, h⟩,
        Finset.mem_insert_self _ _⟩
    · rcases le_or_gt (s + 1 + m) y with h2 | h2
      · exact Or.inl ⟨y - m, Finset.mem_Icc.mpr ⟨by omega, by omega⟩,
          Finset.mem_insert.mpr
            (Or.inr (Finset.mem_singleton.mpr (by ring)))⟩
      · exact Or.inr (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
  calc ((Finset.Icc (s + 1) (n : ℤ)).powerset.filter (shiftFree m)).card
      ≤ (((Finset.Icc (s + 1) ((n : ℤ) - m)).biUnion
            (fun x => ({x, x + m} : Finset ℤ))).powerset.filter
            (shiftFree m)).card *
          ((Finset.Icc ((n : ℤ) - m + 1) (s + m)).powerset.filter
            (shiftFree m)).card :=
        card_powerset_filter_shiftFree_le_mul hcov
    _ ≤ (∏ x ∈ Finset.Icc (s + 1) ((n : ℤ) - m),
            (({x, x + m} : Finset ℤ).powerset.filter (shiftFree m)).card) *
          2 ^ (Finset.Icc ((n : ℤ) - m + 1) (s + m)).card := by
        apply Nat.mul_le_mul
        · exact card_powerset_filter_shiftFree_le_prod _ _ _
            (Finset.Subset.refl _)
        · calc ((Finset.Icc ((n : ℤ) - m + 1) (s + m)).powerset.filter
                (shiftFree m)).card
              ≤ (Finset.Icc ((n : ℤ) - m + 1) (s + m)).powerset.card :=
                Finset.card_le_card (Finset.filter_subset _ _)
            _ = 2 ^ (Finset.Icc ((n : ℤ) - m + 1) (s + m)).card :=
                Finset.card_powerset _
    _ = 3 ^ ((n : ℤ) - s - m).toNat * 2 ^ (s + 2 * m - (n : ℤ)).toNat := by
        congr 1
        · rw [Finset.prod_congr rfl
              (fun x _ => card_powerset_filter_shiftFree_pair hm0),
            Finset.prod_const, Int.card_Icc]
          congr 1
          omega
        · rw [Int.card_Icc]
          congr 1
          omega

/-- The matching bound applied to the class: since `shiftFree2 m s`
implies `shiftFree m`, the class count is at most the same
`3^{(n-s-m)₊}·2^{(s+2m-n)₊}` — no vacuity hypothesis needed. -/
theorem secondMinClass_card_le_matchBound {n : ℕ} {m s : ℤ} (hm : 1 ≤ m) :
    (secondMinClass n m s).card ≤
      3 ^ ((n : ℤ) - s - m).toNat * 2 ^ (s + 2 * m - (n : ℤ)).toNat := by
  refine secondMinClass_card_le_shiftFree2.trans ?_
  refine (Finset.card_le_card ?_).trans
    (card_powerset_filter_shiftFree_Icc_le_matchBound hm)
  intro t ht
  rw [Finset.mem_filter] at ht ⊢
  exact ⟨ht.1, ht.2.1⟩

/-- Exponent bookkeeping: for `m ≤ n - s` one has
`(n-s-m)₊ + (s+2m-n)₊ ≤ (n-s)₊`, hence
`3^{(n-s-m)₊}·2^{(s+2m-n)₊} ≤ 3^{(n-s)₊}`. -/
theorem three_pow_mul_two_pow_le_three_pow {n : ℕ} {m s : ℤ}
    (hm : 1 ≤ m) (hmN : m ≤ (n : ℤ) - s) :
    3 ^ ((n : ℤ) - s - m).toNat * 2 ^ (s + 2 * m - (n : ℤ)).toNat ≤
      3 ^ ((n : ℤ) - s).toNat := by
  have h1 : (((n : ℤ) - s - m).toNat : ℤ) = (n : ℤ) - s - m :=
    Int.toNat_of_nonneg (by omega)
  have h3 : (((n : ℤ) - s).toNat : ℤ) = (n : ℤ) - s :=
    Int.toNat_of_nonneg (by omega)
  have hab : ((n : ℤ) - s - m).toNat + (s + 2 * m - (n : ℤ)).toNat ≤
      ((n : ℤ) - s).toNat := by
    rcases le_or_gt (s + 2 * m) (n : ℤ) with h | h
    · have h2 : (s + 2 * m - (n : ℤ)).toNat = 0 :=
        Int.toNat_eq_zero.mpr (by omega)
      rw [h2, add_zero]
      exact Int.toNat_le_toNat (by omega)
    · have h2 : ((s + 2 * m - (n : ℤ)).toNat : ℤ) =
          s + 2 * m - (n : ℤ) := Int.toNat_of_nonneg (by omega)
      omega
  calc 3 ^ ((n : ℤ) - s - m).toNat * 2 ^ (s + 2 * m - (n : ℤ)).toNat
      ≤ 3 ^ ((n : ℤ) - s - m).toNat * 3 ^ (s + 2 * m - (n : ℤ)).toNat :=
        Nat.mul_le_mul (le_refl _)
          (Nat.pow_le_pow_left (by norm_num) _)
    _ = 3 ^ (((n : ℤ) - s - m).toNat + (s + 2 * m - (n : ℤ)).toNat) :=
        (pow_add _ _ _).symm
    _ ≤ 3 ^ ((n : ℤ) - s).toNat :=
        Nat.pow_le_pow_right (by norm_num) hab

/-- **Vacuous `s`-shift, boundary included.**  The strict version
`shiftFree2_iff_shiftFree_of_vacuous` uses `n < 2s`; the boundary
`n = 2s` is still vacuous since `x ≥ s + 1` gives `x + s ≥ 2s + 1 > n`. -/
theorem shiftFree2_iff_shiftFree_of_vacuous_le {n : ℕ} {m s : ℤ}
    (hns : (n : ℤ) ≤ 2 * s) {t : Finset ℤ}
    (ht : t ⊆ Finset.Icc (s + 1) (n : ℤ)) :
    shiftFree2 m s t ↔ shiftFree m t := by
  rcases eq_or_lt_of_le hns with he | hlt
  · refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
    intro x hx hC
    have h1 := Finset.mem_Icc.mp (ht hx)
    have h2 := Finset.mem_Icc.mp (ht hC)
    omega
  · exact shiftFree2_iff_shiftFree_of_vacuous hlt ht

/-- In the vacuous regime `n ≤ 2s` the two filtered powersets over
`Icc (s+1) n` coincide (boundary included). -/
theorem powerset_filter_shiftFree2_eq_of_vacuous_le {n : ℕ} {m s : ℤ}
    (hns : (n : ℤ) ≤ 2 * s) :
    (Finset.Icc (s + 1) (n : ℤ)).powerset.filter (shiftFree2 m s) =
      (Finset.Icc (s + 1) (n : ℤ)).powerset.filter (shiftFree m) := by
  apply Finset.filter_congr
  intro t ht
  exact shiftFree2_iff_shiftFree_of_vacuous_le hns
    (Finset.mem_powerset.mp ht)

/-- For `n ≤ 2s` the class injects into the `m`-shift-free subsets of
`Icc (s+1) n` *exactly* (no `shiftFree2 → shiftFree` loss). -/
theorem secondMinClass_card_le_shiftFree_of_vacuous_le {n : ℕ} {m s : ℤ}
    (hns : (n : ℤ) ≤ 2 * s) :
    (secondMinClass n m s).card ≤
      ((Finset.Icc (s + 1) (n : ℤ)).powerset.filter (shiftFree m)).card := by
  rw [← powerset_filter_shiftFree2_eq_of_vacuous_le hns]
  exact secondMinClass_card_le_shiftFree2

/-- The filtered count is at most `3^{(n-s)₊}` — weak on its own
(`card ≤ 2^{(n-s)₊}` already), but packaged for downstream use; the
matching bound proves it through the sharper `3^a·2^b` route whenever
`m < n - s`. -/
theorem card_powerset_filter_shiftFree_Icc_le_three_pow {n : ℕ} {m s : ℤ}
    (hm : 1 ≤ m) :
    ((Finset.Icc (s + 1) (n : ℤ)).powerset.filter (shiftFree m)).card ≤
      3 ^ ((n : ℤ) - s).toNat := by
  rcases le_or_gt ((n : ℤ) - s) m with hNm | hNm
  · calc ((Finset.Icc (s + 1) (n : ℤ)).powerset.filter (shiftFree m)).card
        ≤ (Finset.Icc (s + 1) (n : ℤ)).powerset.card :=
          Finset.card_le_card (Finset.filter_subset _ _)
      _ = 2 ^ (Finset.Icc (s + 1) (n : ℤ)).card := Finset.card_powerset _
      _ = 2 ^ ((n : ℤ) - s).toNat := by
          rw [Int.card_Icc]
          congr 1
          congr 1
          omega
      _ ≤ 3 ^ ((n : ℤ) - s).toNat :=
          Nat.pow_le_pow_left (by norm_num) _
  · exact (card_powerset_filter_shiftFree_Icc_le_matchBound hm).trans
      (three_pow_mul_two_pow_le_three_pow hm (le_of_lt hNm))

/-- **Large-`s` headliner.**  For `1 ≤ m < s` and `n ≤ 2s` the
second-minimum class is at most `3^{(n-s)₊}`:

  `(secondMinClass n m s).card ≤ 3^{(n-s)₊}`.

The bound is the matching bound `3^{(n-s-m)₊}·2^{(s+2m-n)₊}` of
`secondMinClass_card_le_matchBound` (much sharper when `m` is close to
`s`), coarsened to a pure power of `3`; the `n - s ≤ m` case is handled
by `card ≤ 2^{(n-s)₊} ≤ 3^{(n-s)₊}`. -/
theorem secondMinClass_card_le_of_half_le {n : ℕ} {m s : ℤ}
    (hm : 1 ≤ m) (_hms : m < s) (_hns : (n : ℤ) ≤ 2 * s) :
    (secondMinClass n m s).card ≤ 3 ^ ((n : ℤ) - s).toNat := by
  rcases le_or_gt ((n : ℤ) - s) m with hNm | hNm
  · refine secondMinClass_card_le_shiftFree2.trans ?_
    refine (Finset.card_le_card ?_).trans
      (card_powerset_filter_shiftFree_Icc_le_three_pow hm)
    intro t ht
    rw [Finset.mem_filter] at ht ⊢
    exact ⟨ht.1, ht.2.1⟩
  · exact (secondMinClass_card_le_matchBound hm).trans
      (three_pow_mul_two_pow_le_three_pow hm (le_of_lt hNm))

/-- Real-valued form of the large-`s` bound. -/
theorem secondMinClass_card_le_of_half_le_real {n : ℕ} {m s : ℤ}
    (hm : 1 ≤ m) (hms : m < s) (hns : (n : ℤ) ≤ 2 * s) :
    ((secondMinClass n m s).card : ℝ) ≤
      (3 : ℝ) ^ ((n : ℤ) - s).toNat := by
  exact_mod_cast secondMinClass_card_le_of_half_le hm hms hns

end JSP000728
