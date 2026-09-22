/-
The **elementary remove-max route** to `Freiman3k4Residual`
(`JSPProblem/Freiman3k4.lean`).

For `A ⊆ [0, l]` with `0, l ∈ A` and `l > 0`, write `A' = A ∖ {l}` and let

  `R := {a' ∈ A' : l − a' ∉ A' − A'}`,   `r := |R|`.

Since `A − A = (A' − A') ∪ (l − A') ∪ (A' − l)` and the elements `l − a'`
(resp. `a' − l`) with `a' ∈ R` are all positive (resp. negative) and pairwise
distinct, one has the **remove-max identity**

  `|A − A| = |A' − A'| + 2r`.

Moreover `r ≥ 1` (`l = l − 0` is never an `A'`-difference), and if all
differences of `A'` are divisible by some `d ≥ 2` then the coprimality
hypothesis on `A` forces `d ∤ l`, hence `r = |A| − 1` and
`|A − A| ≥ 4|A| − 5 ≥ 3|A| − 3` — the *easy case* of Freiman's `3k−4`.

The induction closes provided one can handle the configurations where the
count is genuinely tight: `r = 1` (every `l − a'`, `a' ≠ 0`, is already an
`A'`-difference, forcing `A' ∖ {0} ⊆ [l − l', l']` and making `A'`
near-symmetric about `l/2`) or `l' + 2r < 2|A| − 2` where `l' = max A'`.
These configurations are isolated as the hypothesis `RemoveMaxResidual`, and
the main theorem `freiman3k4Residual_of_removeMaxResidual` proves

  `RemoveMaxResidual → Freiman3k4Residual`

by strong induction on `|A|` (the diameter `l'` of `A'` either satisfies
`2|A'| − 2 ≤ l'`, in which case the induction hypothesis applies, or
`l' ≤ 2|A'| − 3`, in which case the small-diameter bound
`|A' − A'| ≥ l' + |A'|` of `card_sub_self_ge_diam_add_card` applies).

* `image₂_sub_eq_erase_union` — the decomposition
  `A − A = (A' − A') ∪ (l − A') ∪ (A' − l)`.
* `removeMaxR` / `card_sub_self_eq_erase_add_two_mul_r` — the remove-max
  identity `|A − A| = |A' − A'| + 2r`.
* `one_le_removeMaxR` — `r ≥ 1`.
* `card_filter_lt_sub_le_removeMaxR` — the elementary lower bound
  `r ≥ #{a' ∈ A' : a' < l − l'}`.
* `three_mul_le_card_sub_self_of_dvd_erase` — the `gcd A' ≥ 2` easy case.
* `RemoveMaxResidual` — the named residual hypothesis (the `r = 1` / small-`r`
  inverse configurations).
* `three_mul_sub_three_le_card_sub_self` — the induction.
* `freiman3k4Residual_of_removeMaxResidual` — the full reduction.
-/

import JSPProblem.Freiman3k4

namespace JSP000728

open Finset
open scoped Pointwise

/-! ### The remove-max decomposition -/

section RemoveMax

variable {A : Finset ℤ} {l : ℤ}

/-- Decomposition of the difference set after removing the maximum `l`:
`A − A = (A' − A') ∪ (l − A') ∪ (A' − l)` for `A' = A ∖ {l}`
(the summand `l − l = 0` is absorbed by `A' − A'` since `0 ∈ A'`). -/
lemma image₂_sub_eq_erase_union (h0 : 0 ∈ A) (hl : l ∈ A) (hl0 : 0 < l) :
    A.image₂ (· - ·) A =
      (A.erase l).image₂ (· - ·) (A.erase l) ∪
        ((A.erase l).image (l - ·)) ∪ ((A.erase l).image (· - l)) := by
  have h0' : (0 : ℤ) ∈ A.erase l := Finset.mem_erase.2 ⟨ne_of_lt hl0, h0⟩
  ext z
  simp only [Finset.mem_image₂, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro ⟨x, hx, y, hy, rfl⟩
    by_cases hxl : x = l
    · by_cases hyl : y = l
      · refine Or.inl (Or.inl ⟨0, h0', 0, h0', ?_⟩)
        rw [hxl, hyl]; ring
      · refine Or.inl (Or.inr ⟨y, Finset.mem_erase.2 ⟨hyl, hy⟩, ?_⟩)
        rw [hxl]
    · by_cases hyl : y = l
      · refine Or.inr ⟨x, Finset.mem_erase.2 ⟨hxl, hx⟩, ?_⟩
        rw [hyl]
      · exact Or.inl (Or.inl ⟨x, Finset.mem_erase.2 ⟨hxl, hx⟩, y,
          Finset.mem_erase.2 ⟨hyl, hy⟩, rfl⟩)
  · intro h
    rcases h with hDP | hN
    · rcases hDP with hD | hP
      · obtain ⟨x, hx, y, hy, rfl⟩ := hD
        exact ⟨x, (Finset.mem_erase.1 hx).2, y, (Finset.mem_erase.1 hy).2, rfl⟩
      · obtain ⟨y, hy, rfl⟩ := hP
        exact ⟨l, hl, y, (Finset.mem_erase.1 hy).2, rfl⟩
    · obtain ⟨x, hx, rfl⟩ := hN
      exact ⟨x, (Finset.mem_erase.1 hx).2, l, hl, rfl⟩

/-- The number of genuinely new differences contributed by the maximum:
`removeMaxR A l = #{a' ∈ A ∖ {l} : l − a' ∉ (A ∖ {l}) − (A ∖ {l})}`. -/
def removeMaxR (A : Finset ℤ) (l : ℤ) : ℕ :=
  ((A.erase l).filter
    (fun a' => l - a' ∉ (A.erase l).image₂ (· - ·) (A.erase l))).card

/-- **Remove-max identity.**  For `A ⊆ [0, l]` containing `0` and `l`
(with `l > 0`), writing `A' = A ∖ {l}` and
`r = #{a' ∈ A' : l − a' ∉ A' − A'}`, one has

  `|A − A| = |A' − A'| + 2r`.

Indeed `A − A = (A' − A') ∪ (l − A') ∪ (A' − l)`; the elements `l − a'` are
positive, the elements `a' − l` negative, and `A' − A'` is symmetric, so
exactly the `r` values `l − a'` with `a' ∈ R` (and their `r` negatives) are
new. -/
theorem card_sub_self_eq_erase_add_two_mul_r
    (h0 : 0 ∈ A) (hl : l ∈ A)
    (_hmin : ∀ x ∈ A, 0 ≤ x) (hmax : ∀ x ∈ A, x ≤ l) (hl0 : 0 < l) :
    ((A.image₂ (· - ·) A).card : ℤ) =
      ((A.erase l).image₂ (· - ·) (A.erase l)).card +
        2 * (removeMaxR A l : ℤ) := by
  classical
  set A' := A.erase l with hA'def
  set D' := A'.image₂ (· - ·) A' with hD'def
  set P := A'.image (l - ·) with hPdef
  set N := A'.image (· - l) with hNdef
  have hPpos : ∀ x ∈ P, 0 < x := by
    intro x hx
    obtain ⟨a', ha', rfl⟩ := Finset.mem_image.1 hx
    have h1 := hmax a' (Finset.mem_erase.1 ha').2
    have h2 := (Finset.mem_erase.1 ha').1
    omega
  have hNneg : ∀ x ∈ N, x < 0 := by
    intro x hx
    obtain ⟨a', ha', rfl⟩ := Finset.mem_image.1 hx
    have h1 := hmax a' (Finset.mem_erase.1 ha').2
    have h2 := (Finset.mem_erase.1 ha').1
    omega
  have hdecomp : A.image₂ (· - ·) A = D' ∪ (P \ D') ∪ (N \ D') := by
    rw [image₂_sub_eq_erase_union h0 hl hl0]
    ext z
    simp only [Finset.mem_union, Finset.mem_sdiff]
    tauto
  have hdisj : Disjoint (D' ∪ (P \ D')) (N \ D') := by
    rw [Finset.disjoint_left]
    intro z hz hzN
    rcases Finset.mem_union.1 hz with hzD | hzP
    · exact (Finset.mem_sdiff.1 hzN).2 hzD
    · have hp := hPpos z (Finset.mem_sdiff.1 hzP).1
      have hn := hNneg z (Finset.mem_sdiff.1 hzN).1
      omega
  have hcard : (A.image₂ (· - ·) A).card =
      D'.card + (P \ D').card + (N \ D').card := by
    rw [hdecomp, Finset.card_union_of_disjoint hdisj,
      Finset.card_union_of_disjoint Finset.disjoint_sdiff]
  -- `P ∖ D'` and `N ∖ D'` are the images of `R` under `l − ·` and `· − l`.
  have hPsd : P \ D' =
      (A'.filter (fun a' => l - a' ∉ D')).image (l - ·) := by
    ext z
    simp only [hPdef, hD'def, Finset.mem_sdiff, Finset.mem_image,
      Finset.mem_filter]
    constructor
    · rintro ⟨⟨a', ha', rfl⟩, hz⟩
      exact ⟨a', ⟨ha', hz⟩, rfl⟩
    · rintro ⟨a', ⟨ha', hz⟩, rfl⟩
      exact ⟨⟨a', ha', rfl⟩, hz⟩
  have hNsd : N \ D' =
      (A'.filter (fun a' => l - a' ∉ D')).image (· - l) := by
    ext z
    simp only [hNdef, hD'def, Finset.mem_sdiff, Finset.mem_image,
      Finset.mem_filter]
    constructor
    · rintro ⟨⟨a', ha', rfl⟩, hz⟩
      refine ⟨a', ⟨ha', ?_⟩, rfl⟩
      intro hmem
      apply hz
      obtain ⟨x, hx, y, hy, hxy⟩ := Finset.mem_image₂.1 hmem
      -- `l − a' = x − y` gives `a' − l = y − x ∈ D'`.
      have e : a' - l = y - x := by omega
      rw [e]
      exact Finset.mem_image₂_of_mem hy hx
    · rintro ⟨a', ⟨ha', hz⟩, rfl⟩
      refine ⟨⟨a', ha', rfl⟩, ?_⟩
      intro hmem
      apply hz
      obtain ⟨x, hx, y, hy, hxy⟩ := Finset.mem_image₂.1 hmem
      -- `a' − l = x − y` gives `l − a' = y − x ∈ D'`.
      have e : l - a' = y - x := by omega
      rw [e]
      exact Finset.mem_image₂_of_mem hy hx
  have hinjP : Function.Injective (fun a : ℤ => l - a) :=
    fun a b h => by simpa using h
  have hinjN : Function.Injective (fun a : ℤ => a - l) :=
    fun a b h => by simpa using h
  have hPcard : (P \ D').card = removeMaxR A l := by
    rw [hPsd, Finset.card_image_of_injective _ hinjP]
    unfold removeMaxR
    rw [← hA'def, ← hD'def]
  have hNcard : (N \ D').card = removeMaxR A l := by
    rw [hNsd, Finset.card_image_of_injective _ hinjN]
    unfold removeMaxR
    rw [← hA'def, ← hD'def]
  have hsum : (A.image₂ (· - ·) A).card = D'.card + 2 * removeMaxR A l := by
    rw [hcard, hPcard, hNcard]; ring
  rw [hsum]
  push_cast
  ring

/-- `0` always contributes to `R` (`l` is never an `A'`-difference), so
`r ≥ 1` and `|A − A| ≥ |A' − A'| + 2`. -/
theorem one_le_removeMaxR
    (h0 : 0 ∈ A) (_hl : l ∈ A)
    (hmin : ∀ x ∈ A, 0 ≤ x) (hmax : ∀ x ∈ A, x ≤ l) (hl0 : 0 < l) :
    1 ≤ removeMaxR A l := by
  have hpos : ((A.erase l).filter
      (fun a' => l - a' ∉ (A.erase l).image₂ (· - ·) (A.erase l))).Nonempty := by
    refine ⟨0, Finset.mem_filter.2 ⟨?_, ?_⟩⟩
    · exact Finset.mem_erase.2 ⟨ne_of_lt hl0, h0⟩
    · intro hmem
      obtain ⟨x, hx, y, hy, hxy⟩ := Finset.mem_image₂.1 hmem
      have hxl : x < l :=
        lt_of_le_of_ne (hmax x (Finset.mem_erase.1 hx).2)
          (Finset.mem_erase.1 hx).1
      have hy0 := hmin y (Finset.mem_erase.1 hy).2
      omega
  exact Finset.card_pos.2 hpos

/-- The elementary lower bound on `r`: every `a' ∈ A'` below `l − l'`
automatically has `l − a' > l'`, hence `l − a' ∉ A' − A' ⊆ [−l', l']`. -/
theorem card_filter_lt_sub_le_removeMaxR
    (hmin : ∀ x ∈ A, 0 ≤ x) {l' : ℤ}
    (hl'max : ∀ a' ∈ A.erase l, a' ≤ l') :
    ((A.erase l).filter (fun a' => a' < l - l')).card ≤ removeMaxR A l := by
  apply Finset.card_le_card
  intro a' ha'
  rw [Finset.mem_filter] at ha' ⊢
  refine ⟨ha'.1, ?_⟩
  intro hmem
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.mem_image₂.1 hmem
  have hx' := hl'max x hx
  have hy0 := hmin y (Finset.mem_erase.1 hy).2
  have ha'' := ha'.2
  omega

end RemoveMax

/-! ### The easy case: `A'` has a nontrivial common difference divisor -/

section GcdCase

variable {A : Finset ℤ} {l : ℤ}

/-- If some `d ≥ 2` divides every difference of `A' = A ∖ {l}`, then the
coprimality hypothesis on `A` forces `d ∤ l`, every `l − a'` lies outside
`A' − A'` (which is contained in `dℤ`), hence `r = |A| − 1` and
`|A − A| ≥ (2(|A| − 1) − 1) + 2(|A| − 1) = 4|A| − 5 ≥ 3|A| − 3`. -/
theorem three_mul_le_card_sub_self_of_dvd_erase
    (h0 : 0 ∈ A) (hl : l ∈ A)
    (hmem : ∀ x ∈ A, 0 ≤ x ∧ x ≤ l)
    (hgcd : ∀ d : ℤ, 2 ≤ d → ∃ x ∈ A, ∃ y ∈ A, ¬ d ∣ x - y)
    (hl2 : 2 ≤ l)
    (d : ℤ) (hd : 2 ≤ d)
    (hdvd : ∀ x ∈ A.erase l, ∀ y ∈ A.erase l, d ∣ x - y) :
    3 * (A.card : ℤ) - 3 ≤ ((A.image₂ (· - ·) A).card : ℤ) := by
  classical
  have hmin : ∀ x ∈ A, 0 ≤ x := fun x hx => (hmem x hx).1
  have hmax : ∀ x ∈ A, x ≤ l := fun x hx => (hmem x hx).2
  have hl0 : 0 < l := by omega
  have h0' : (0 : ℤ) ∈ A.erase l := Finset.mem_erase.2 ⟨ne_of_lt hl0, h0⟩
  -- `d` divides every element of `A'`.
  have hdvd' : ∀ a' ∈ A.erase l, d ∣ a' := by
    intro a' ha'
    have h := hdvd a' ha' 0 h0'
    rwa [sub_zero] at h
  -- Hence `d ∤ l`.
  have hdl : ¬ d ∣ l := by
    intro hl'
    obtain ⟨x, hx, y, hy, hxy⟩ := hgcd d hd
    apply hxy
    have hxd : d ∣ x := by
      rcases eq_or_ne x l with rfl | hxl
      · exact hl'
      · exact hdvd' x (Finset.mem_erase.2 ⟨hxl, hx⟩)
    have hyd : d ∣ y := by
      rcases eq_or_ne y l with rfl | hyl
      · exact hl'
      · exact hdvd' y (Finset.mem_erase.2 ⟨hyl, hy⟩)
    exact dvd_sub hxd hyd
  -- Every `a' ∈ A'` lies in `R`.
  have hR : (A.erase l).filter
      (fun a' => l - a' ∉ (A.erase l).image₂ (· - ·) (A.erase l)) =
      A.erase l := by
    apply Finset.filter_true_of_mem
    intro a' ha' hmem'
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.mem_image₂.1 hmem'
    have h1 : d ∣ l - a' := by
      rw [← hxy]
      exact hdvd x hx y hy
    have h2 : d ∣ a' := hdvd' a' ha'
    have h3 : d ∣ l := by
      have e : l = (l - a') + a' := by ring
      rw [e]
      exact dvd_add h1 h2
    exact hdl h3
  have hident := card_sub_self_eq_erase_add_two_mul_r h0 hl hmin hmax hl0
  have hcardA' : ((A.erase l).card : ℤ) = (A.card : ℤ) - 1 := by
    have h := Finset.card_erase_of_mem hl
    have h1 : 1 ≤ A.card := Finset.card_pos.2 ⟨l, hl⟩
    omega
  have hD'ge : 2 * ((A.erase l).card : ℤ) - 1 ≤
      (((A.erase l).image₂ (· - ·) (A.erase l)).card : ℤ) := by
    have h := card_sub_self_ge ⟨0, h0'⟩
    have h1 : 1 ≤ (A.erase l).card := Finset.card_pos.2 ⟨0, h0'⟩
    calc (2 * ((A.erase l).card : ℤ) - 1)
        = ((2 * (A.erase l).card - 1 : ℕ) : ℤ) := by
          rw [Nat.cast_sub (by omega : (1 : ℕ) ≤ 2 * (A.erase l).card)]
          push_cast; ring
      _ ≤ (((A.erase l).image₂ (· - ·) (A.erase l)).card : ℤ) := by
          exact_mod_cast h
  have hRcard : (removeMaxR A l : ℤ) = (A.card : ℤ) - 1 := by
    have h1 : removeMaxR A l = (A.erase l).card := by
      unfold removeMaxR
      rw [hR]
    rw [h1, hcardA']
  have hk2 : 2 ≤ (A.card : ℤ) := by
    have hsub : ({0, l} : Finset ℤ) ⊆ A := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact h0
      · exact hl
    have h := Finset.card_le_card hsub
    rw [Finset.card_pair (ne_of_lt hl0)] at h
    exact_mod_cast h
  omega

end GcdCase

/-! ### The residual inverse configurations and the main reduction -/

/-- The **residual inverse configurations** of the remove-max argument.

Let `A ⊆ [0, l]` satisfy the `Freiman3k4Residual` hypotheses and let
`A' = A ∖ {l}`, `l' = max A'` (witnessed by `l' ∈ A'`,
`∀ a' ∈ A', a' ≤ l'`) and
`r = #{a' ∈ A' : l − a' ∉ A' − A'}`.  The remove-max identity gives
`|A − A| = |A' − A'| + 2r`; the induction closes this estimate unless
`A'` is coprime (`∀ d ≥ 2`, some pair difference of `A'` is not divisible
by `d`) and either

* `r = 1` — the *near-symmetric extremal case*: every `l − a'` with
  `a' ≠ 0` is already an `A'`-difference, which forces
  `A' ∖ {0} ⊆ [l − l', l']` and makes `A'` near-symmetric about `l/2`, or
* `l' + 2r < 2|A| − 2` — `A'` is a *small-diameter* set (`l' ≤ 2|A'| − 3`)
  whose bound `|A' − A'| ≥ l' + |A'|` contributes too little for the number
  `r` of new differences.

`RemoveMaxResidual` asserts that `|A − A| ≥ 3|A| − 3` nevertheless holds in
those configurations; it is the precise inverse-theoretic content of the
elementary remove-max proof of Freiman's `3k − 4` bound. -/
def RemoveMaxResidual : Prop :=
  ∀ (A : Finset ℤ) (l l' : ℤ),
    0 ∈ A → l ∈ A → (∀ x ∈ A, 0 ≤ x ∧ x ≤ l) →
    (∀ d : ℤ, 2 ≤ d → ∃ x ∈ A, ∃ y ∈ A, ¬ d ∣ x - y) →
    2 * (A.card : ℤ) - 2 ≤ l →
    l' ∈ A.erase l → (∀ a' ∈ A.erase l, a' ≤ l') →
    (∀ d : ℤ, 2 ≤ d → ∃ x ∈ A.erase l, ∃ y ∈ A.erase l, ¬ d ∣ x - y) →
    (((A.erase l).filter (fun a' => l - a' ∉
        (A.erase l).image₂ (· - ·) (A.erase l))).card = 1 ∨
      l' + 2 * (((A.erase l).filter (fun a' => l - a' ∉
        (A.erase l).image₂ (· - ·) (A.erase l))).card : ℤ)
        < 2 * (A.card : ℤ) - 2) →
    3 * (A.card : ℤ) - 3 ≤ ((A.image₂ (· - ·) A).card : ℤ)

/-- **The remove-max induction.**  Under the residual hypothesis
`RemoveMaxResidual`, every `A ⊆ [0, l]` containing `0` and `l`, satisfying
the coprimality condition and `2|A| − 2 ≤ l`, has `|A − A| ≥ 3|A| − 3`.

The proof is by strong induction on `|A|`.  With `A' = A ∖ {l}`,
`l' = max A'` and `r = removeMaxR A l`:

* if `A'` has a common difference divisor `d ≥ 2`, the easy case
  `three_mul_le_card_sub_self_of_dvd_erase` applies (`r = |A| − 1`);
* if `A'` is coprime and `2|A'| − 2 ≤ l'`, the induction hypothesis gives
  `|A' − A'| ≥ 3|A'| − 3`; this closes the induction when `r ≥ 2`, while
  `r = 1` is exactly the first disjunct of `RemoveMaxResidual`;
* if `A'` is coprime and `l' ≤ 2|A'| − 3`, the small-diameter bound gives
  `|A' − A'| ≥ l' + |A'|`; this closes the induction when
  `l' + 2r ≥ 2|A| − 2`, and the complementary strict inequality is exactly
  the second disjunct of `RemoveMaxResidual`. -/
theorem three_mul_sub_three_le_card_sub_self (hres : RemoveMaxResidual) :
    ∀ n : ℕ, ∀ A : Finset ℤ, ∀ l : ℤ, A.card = n →
      0 ∈ A → l ∈ A → (∀ x ∈ A, 0 ≤ x ∧ x ≤ l) →
      (∀ d : ℤ, 2 ≤ d → ∃ x ∈ A, ∃ y ∈ A, ¬ d ∣ x - y) →
      2 * (A.card : ℤ) - 2 ≤ l →
      3 * (A.card : ℤ) - 3 ≤ ((A.image₂ (· - ·) A).card : ℤ) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro A l hkc h0 hl hmem hgcd hlarge
    classical
    have hmin : ∀ x ∈ A, 0 ≤ x := fun x hx => (hmem x hx).1
    have hmax : ∀ x ∈ A, x ≤ l := fun x hx => (hmem x hx).2
    -- `|A| ≥ 2`: the coprimality hypothesis at `d = 2` gives two distinct
    -- elements.
    obtain ⟨x₂, hx₂, y₂, hy₂, hxy₂⟩ := hgcd 2 (le_refl 2)
    have hne2 : x₂ ≠ y₂ := by
      intro h'
      subst h'
      exact hxy₂ (by simp)
    have hk2 : 2 ≤ A.card := by
      have hsub : ({x₂, y₂} : Finset ℤ) ⊆ A := by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact hx₂
        · exact hy₂
      have h := Finset.card_le_card hsub
      rwa [Finset.card_pair hne2] at h
    have hl2 : 2 ≤ l := by omega
    have hl0 : 0 < l := by omega
    have h0' : (0 : ℤ) ∈ A.erase l := Finset.mem_erase.2 ⟨ne_of_lt hl0, h0⟩
    have hne : (A.erase l).Nonempty := ⟨0, h0'⟩
    have hcardA' : ((A.erase l).card : ℤ) = (A.card : ℤ) - 1 := by
      have h := Finset.card_erase_of_mem hl
      omega
    set l' := (A.erase l).max' hne with hl'def
    have hl'mem : l' ∈ A.erase l := (A.erase l).max'_mem hne
    have hl'max : ∀ a' ∈ A.erase l, a' ≤ l' :=
      fun a' ha' => (A.erase l).le_max' a' ha'
    have hident := card_sub_self_eq_erase_add_two_mul_r h0 hl hmin hmax hl0
    have hr1 : 1 ≤ removeMaxR A l := one_le_removeMaxR h0 hl hmin hmax hl0
    by_cases hgcd' : ∃ d : ℤ, 2 ≤ d ∧
        ∀ x ∈ A.erase l, ∀ y ∈ A.erase l, d ∣ x - y
    · obtain ⟨d, hd, hdvd⟩ := hgcd'
      exact three_mul_le_card_sub_self_of_dvd_erase h0 hl hmem hgcd hl2
        d hd hdvd
    · -- `A'` is coprime.
      push Not at hgcd'
      by_cases hl'big : 2 * (A.card : ℤ) - 4 ≤ l'
      · -- `A'` has large diameter: the induction hypothesis applies.
        have hmem' : ∀ x ∈ A.erase l, 0 ≤ x ∧ x ≤ l' := by
          intro x hx
          have hxA := (Finset.mem_erase.1 hx).2
          exact ⟨hmin x hxA, hl'max x hx⟩
        have hbound' : 2 * ((A.erase l).card : ℤ) - 2 ≤ l' := by omega
        have hlt : (A.erase l).card < n := by
          have h := Finset.card_erase_of_mem hl
          omega
        have ihA' := ih (A.erase l).card hlt (A.erase l) l' rfl h0' hl'mem
          hmem' hgcd' hbound'
        -- `|A − A| ≥ 3k − 6 + 2r`; done if `r ≥ 2`, else `r = 1`.
        by_cases hr1eq : removeMaxR A l = 1
        · refine hres A l l' h0 hl hmem hgcd hlarge hl'mem hl'max hgcd'
            (Or.inl ?_)
          exact hr1eq
        · have hr2 : 2 ≤ removeMaxR A l := by omega
          omega
      · -- `A'` has small diameter: `l' ≤ 2|A'| − 3`.
        push Not at hl'big
        have hmin' : ∀ x ∈ A.erase l, 0 ≤ x := fun x hx =>
          hmin x (Finset.mem_erase.1 hx).2
        have hdiam : l' + 3 ≤ 2 * ((A.erase l).card : ℤ) := by omega
        have hD'ge : l' + ((A.erase l).card : ℤ) ≤
            (((A.erase l).image₂ (· - ·) (A.erase l)).card : ℤ) :=
          card_sub_self_ge_diam_add_card h0' hl'mem hmin' hl'max hdiam
        -- `|A − A| ≥ l' + k − 1 + 2r`; done unless `l' + 2r < 2k − 2`.
        by_cases hrgap : l' + 2 * (removeMaxR A l : ℤ) <
            2 * (A.card : ℤ) - 2
        · refine hres A l l' h0 hl hmem hgcd hlarge hl'mem hl'max hgcd'
            (Or.inr ?_)
          exact hrgap
        · omega

/-- **The elementary remove-max reduction of the residual case.**
`Freiman3k4Residual` follows from the residual inverse analysis
`RemoveMaxResidual`. -/
theorem freiman3k4Residual_of_removeMaxResidual
    (hres : RemoveMaxResidual) : Freiman3k4Residual := by
  intro A l h0 hl hmem hgcd hlarge _hmf
  exact three_mul_sub_three_le_card_sub_self hres A.card A l rfl
    h0 hl hmem hgcd hlarge

end JSP000728
