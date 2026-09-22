/-
# The **gap disjunct** of `RemoveMaxResidual`
(`l' + 2r < 2|A| − 2`, i.e. `A'` coprime of *small diameter*)

Let `A ⊆ [0, l]` satisfy the `RemoveMaxResidual` hypotheses, `A' = A ∖ {l}`,
`l' = max A'`, `k' = |A'| = |A| − 1`, `r = removeMaxR A l` and `t = l − l'`.
In the gap regime (`l' + 2r < 2k'`), `A'` is *dense* in `[0, l']`:
writing `h = l' + 1 − k'` for the number of holes, `2h ≤ l' − 1`.

This file proves the *bookkeeping* part of the disjunct and isolates the
remaining sharp inverse statement as `RemoveMaxGapResidual`:

* `image₂_sub_le` — differences of `A'` are `≤ l'`.
* `removeMaxR_eq` — the defect splits as `r = s + u` with
  `s = |A' ∩ [0, t)|` (automatic: `l − a' > l'`) and
  `u = |{a' ∈ A' ∩ [t, l'] : l − a' ∉ posDiff A'}|`.
* `card_top_le_holes_of_not_mem_posDiff` — a missed positive difference `x`
  satisfies `|A' ∩ [x, l']| ≤ h` (thin top), from
  `card_inter_Icc_le_of_not_mem_posDiff`.
* `mem_posDiff_of_gap_lt` — **no misses below `t`**: a missed `x < t`
  forces `s ≥ k' − h`, hence `2r ≥ 2(l' + 1 − 2h)`, contradicting the gap
  `2r ≤ l' + 1 − 2h`.
* `removeMaxGap_of_residual` — the conditional theorem
  `RemoveMaxGapResidual → RemoveMaxGap`, and
  `removeMaxResidual_of_disjuncts` which additionally takes the `r = 1`
  disjunct as input.

## The residual

Writing `P = posDiff A' ⊆ [1, l']` (`|P| = l' − m`, `m` the number of missed
positive differences), the remove-max identity `|A − A| = |D'| + 2r` with
`|D'| = 2|P| + 1` gives the goal `3k' ≤ |A − A|` iff `m ≤ r − c/2` where
`c = l' + 2 − 3h`.  Since `r = s + u` and `m = u + m'` (every miss `x` has
`l − x ∈ [t, l']`; `u` misses come from `A'`-reflections, `m'` from holes),
the goal is `m' ≤ s − c/2`, equivalently `m' + α ≤ (l' + h)/2` where
`α = |A' ∩ [t, l']|`, equivalently (via `m' = η − p'` with `η` the holes in
`[t, l']` and `p'` the holes whose `l`-reflection is a positive difference)

  `2·|{x ∈ [t, l'] ∖ A' : l − x ∈ P}| ≥ l' − h + 2 − 2t`.

This last form is `RemoveMaxGapResidual` below.  It is a *sharp* statement:
equality is attained e.g. for `A' = {0,3,6,7,9,10,12,13,15,16,19}`,
`l = 22` (`h = 9`, `t = 3`, `p' = 3 = (l' − h + 2)/2 − t`).
-/

import JSPProblem.FreimanResidualB
import JSPProblem.FreimanDiffSmall

namespace JSP000728

open Finset

/-! ### The `RemoveMaxGap` statement -/

/-- **The gap disjunct of `RemoveMaxResidual`**: under the same hypotheses,
when `l' + 2r < 2|A| − 2` (the small-diameter branch of the remove-max
induction), the difference set satisfies `|A − A| ≥ 3|A| − 3`. -/
def RemoveMaxGap : Prop :=
  ∀ (A : Finset ℤ) (l l' : ℤ),
    0 ∈ A → l ∈ A → (∀ x ∈ A, 0 ≤ x ∧ x ≤ l) →
    (∀ d : ℤ, 2 ≤ d → ∃ x ∈ A, ∃ y ∈ A, ¬ d ∣ x - y) →
    2 * (A.card : ℤ) - 2 ≤ l →
    l' ∈ A.erase l → (∀ a' ∈ A.erase l, a' ≤ l') →
    (∀ d : ℤ, 2 ≤ d → ∃ x ∈ A.erase l, ∃ y ∈ A.erase l, ¬ d ∣ x - y) →
    l' + 2 * (((A.erase l).filter (fun a' => l - a' ∉
        (A.erase l).image₂ (· - ·) (A.erase l))).card : ℤ)
        < 2 * (A.card : ℤ) - 2 →
    3 * (A.card : ℤ) - 3 ≤ ((A.image₂ (· - ·) A).card : ℤ)

/-- **The `r = 1` (near-symmetric) disjunct of `RemoveMaxResidual`. -/
def RemoveMaxEqOne : Prop :=
  ∀ (A : Finset ℤ) (l l' : ℤ),
    0 ∈ A → l ∈ A → (∀ x ∈ A, 0 ≤ x ∧ x ≤ l) →
    (∀ d : ℤ, 2 ≤ d → ∃ x ∈ A, ∃ y ∈ A, ¬ d ∣ x - y) →
    2 * (A.card : ℤ) - 2 ≤ l →
    l' ∈ A.erase l → (∀ a' ∈ A.erase l, a' ≤ l') →
    (∀ d : ℤ, 2 ≤ d → ∃ x ∈ A.erase l, ∃ y ∈ A.erase l, ¬ d ∣ x - y) →
    (((A.erase l).filter (fun a' => l - a' ∉
        (A.erase l).image₂ (· - ·) (A.erase l))).card = 1) →
    3 * (A.card : ℤ) - 3 ≤ ((A.image₂ (· - ·) A).card : ℤ)

/-- `RemoveMaxResidual` follows from its two disjuncts. -/
theorem removeMaxResidual_of_disjuncts
    (h1 : RemoveMaxEqOne) (hg : RemoveMaxGap) : RemoveMaxResidual := by
  intro A l l' h0 hl hmem hgcd hlarge hl'mem hl'max hgcd' hdisj
  rcases hdisj with hr1 | hgp
  · exact h1 A l l' h0 hl hmem hgcd hlarge hl'mem hl'max hgcd' hr1
  · exact hg A l l' h0 hl hmem hgcd hlarge hl'mem hl'max hgcd' hgp

/-! ### Difference bounds and the `r = s + u` decomposition -/

section GapAux

variable {A' : Finset ℤ} {l l' : ℤ}

/-- Every difference of `A' ⊆ [0, l']` is at most `l'`. -/
lemma image₂_sub_le (hmin : ∀ x ∈ A', 0 ≤ x) (hmax : ∀ x ∈ A', x ≤ l') :
    ∀ z ∈ A'.image₂ (· - ·) A', z ≤ l' := by
  intro z hz
  obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_image₂.1 hz
  have h1 := hmax x hx
  have h2 := hmin y hy
  omega

/-- For `a' ∈ A'` with `a' ≥ t := l − l'`, the value `l − a'` is positive,
so `l − a' ∉ A' − A'` iff `l − a' ∉ posDiff A'`. -/
lemma not_mem_image₂_sub_iff_not_mem_posDiff
    (hmax : ∀ x ∈ A', x ≤ l') (hl'l : l' < l)
    {a' : ℤ} (ha' : a' ∈ A') (hat : l - l' ≤ a') :
    l - a' ∉ A'.image₂ (· - ·) A' ↔ l - a' ∉ posDiff A' := by
  have ha'' := hmax a' ha'
  have hpos : 0 < l - a' := by omega
  rw [mem_posDiff]
  constructor
  · intro h
    exact fun hp => h hp.1
  · intro h hmem
    exact h ⟨hmem, hpos⟩

/-- **The `r = s + u` decomposition.**  The remove-max defect splits at
`t = l − l'`: elements of `A'` below `t` contribute automatically
(`l − a' > l'` is never a difference), and elements `a' ≥ t` contribute iff
`l − a'` is not a positive difference of `A'`. -/
theorem removeMaxR_eq
    {A : Finset ℤ} (hmin : ∀ x ∈ A, 0 ≤ x) (hmax : ∀ x ∈ A, x ≤ l)
    (hl'mem : l' ∈ A.erase l) (hl'max : ∀ a' ∈ A.erase l, a' ≤ l') :
    removeMaxR A l =
      ((A.erase l).filter (fun a' => a' < l - l')).card +
        ((A.erase l).filter
          (fun a' => l - l' ≤ a' ∧ l - a' ∉ posDiff (A.erase l))).card := by
  classical
  have hl'l : l' < l :=
    lt_of_le_of_ne (hmax l' (Finset.mem_erase.1 hl'mem).2)
      (Finset.mem_erase.1 hl'mem).1
  have hmin' : ∀ x ∈ A.erase l, 0 ≤ x :=
    fun x hx => hmin x (Finset.mem_erase.1 hx).2
  have hD'le : ∀ z ∈ (A.erase l).image₂ (· - ·) (A.erase l), z ≤ l' :=
    image₂_sub_le hmin' hl'max
  have hR : (A.erase l).filter
      (fun a' => l - a' ∉ (A.erase l).image₂ (· - ·) (A.erase l)) =
      ((A.erase l).filter (fun a' => a' < l - l')) ∪
        ((A.erase l).filter
          (fun a' => l - l' ≤ a' ∧ l - a' ∉ posDiff (A.erase l))) := by
    ext a'
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨ha', hna⟩
      rcases lt_or_le a' (l - l') with h | h
      · exact Or.inl ⟨ha', h⟩
      · refine Or.inr ⟨ha', h, ?_⟩
        rwa [← not_mem_image₂_sub_iff_not_mem_posDiff hl'max hl'l ha' h]
    · rintro (⟨ha', ha't⟩ | ⟨ha', hat, hna⟩)
      · refine ⟨ha', ?_⟩
        intro hmem
        have := hD'le (l - a') hmem
        omega
      · refine ⟨ha', ?_⟩
        rwa [not_mem_image₂_sub_iff_not_mem_posDiff hl'max hl'l ha' hat]
  unfold removeMaxR
  rw [hR, Finset.card_union_of_disjoint]
  rw [Finset.disjoint_left]
  intro x hx hy
  have h1 := (Finset.mem_filter.1 hx).2
  have h2 := (Finset.mem_filter.1 hy).2
  omega

end GapAux

/-! ### Density: missed differences force thin tops -/

section Misses

variable {A' : Finset ℤ} {l' : ℤ}

/-- For `A' ⊆ [0, l']` with `l' ≥ 0`, the number of holes of `A'` inside
`[0, y]` is at most the total hole count `l' + 1 − |A'|`. -/
lemma card_sdiff_Icc_le
    (hmem : ∀ x ∈ A', 0 ≤ x ∧ x ≤ l') (hl'0 : 0 ≤ l') {y : ℤ} (hy : y ≤ l') :
    ((Finset.Icc 0 y \ A').card : ℤ) ≤ l' + 1 - (A'.card : ℤ) := by
  have hsub : Finset.Icc 0 y \ A' ⊆ Finset.Icc 0 l' \ A' := by
    intro z hz
    obtain ⟨hzI, hzA⟩ := Finset.mem_sdiff.1 hz
    have hz := Finset.mem_Icc.1 hzI
    exact Finset.mem_sdiff.2 ⟨Finset.mem_Icc.2 ⟨hz.1, le_trans hz.2 hy⟩, hzA⟩
  have hcard := Finset.card_le_card hsub
  have hAsub : A' ⊆ Finset.Icc 0 l' :=
    fun x hx => Finset.mem_Icc.2 ⟨(hmem x hx).1, (hmem x hx).2⟩
  have hsd : (Finset.Icc 0 l' \ A').card =
      (Finset.Icc 0 l').card - A'.card := Finset.card_sdiff_of_subset hAsub
  have hIcc : ((Finset.Icc (0 : ℤ) l').card : ℤ) = l' + 1 := by
    have h := Int.card_Icc_of_le (a := (0 : ℤ)) (b := l') hl'0
    omega
  rw [hsd] at hcard
  have hcast : (((Finset.Icc 0 y \ A').card : ℕ) : ℤ) ≤
      (((Finset.Icc 0 l').card - A'.card : ℕ) : ℤ) := by exact_mod_cast hcard
  rw [Nat.cast_sub (Finset.card_le_card hAsub), hIcc] at hcast
  exact hcast

/-- A missed positive difference forces a thin top:
`|A' ∩ [x, l']| ≤ l' + 1 − |A'|` (the number of holes). -/
lemma card_top_le_holes_of_not_mem_posDiff
    (hmem : ∀ x ∈ A', 0 ≤ x ∧ x ≤ l') {x : ℤ}
    (hx1 : 1 ≤ x) (hx2 : x ≤ l' - 1) (hxP : x ∉ posDiff A') :
    ((A' ∩ Finset.Icc x l').card : ℤ) ≤ l' + 1 - (A'.card : ℤ) := by
  have h1 := card_inter_Icc_le_of_not_mem_posDiff hx1 hx2 hxP
  have h2 := card_sdiff_Icc_le hmem (by omega) (show l' - x ≤ l' by omega)
  -- `|A' ∩ [0, l'−x]| ≥ (l'−x+1) − h` since `A' ∩ S = S ∖ (S ∖ A')`.
  have hS : Finset.Icc 0 (l' - x) \ (Finset.Icc 0 (l' - x) \ A') =
      A' ∩ Finset.Icc 0 (l' - x) := by
    ext z
    simp only [Finset.mem_sdiff, Finset.mem_inter, Finset.mem_Icc, not_and]
    constructor
    · rintro ⟨⟨hz0, hzl'⟩, hz⟩
      refine ⟨?_, hz0, hzl'⟩
      by_contra hzA
      exact hz hzA
    · rintro ⟨hzA, hz0, hzl'⟩
      exact ⟨⟨hz0, hzl'⟩, fun h => h hzA⟩
  have hdisj : Disjoint (Finset.Icc 0 (l' - x) \ A')
      (A' ∩ Finset.Icc 0 (l' - x)) := by
    rw [Finset.disjoint_left]
    intro z hz1 hz2
    exact (Finset.mem_sdiff.1 hz1).2 (Finset.mem_inter.1 hz2).1
  have hcardS : (A' ∩ Finset.Icc 0 (l' - x)).card +
      (Finset.Icc 0 (l' - x) \ A').card = (Finset.Icc 0 (l' - x)).card := by
    have hunion : (Finset.Icc 0 (l' - x) \ A') ∪
        (A' ∩ Finset.Icc 0 (l' - x)) = Finset.Icc 0 (l' - x) := by
      ext z
      simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter,
        Finset.mem_Icc]
      constructor
      · rintro (⟨h, -⟩ | ⟨-, h⟩) <;> exact h
      · intro h
        by_cases hz : z ∈ A'
        · exact Or.inr ⟨hz, h⟩
        · exact Or.inl ⟨h, hz⟩
    rw [← hunion]
    exact (Finset.card_union_of_disjoint hdisj).symm
  have hIcc : ((Finset.Icc (0 : ℤ) (l' - x)).card : ℤ) = l' - x + 1 := by
    have h := Int.card_Icc_of_le (a := (0 : ℤ)) (b := l' - x) (by omega)
    omega
  have hcastS : (((A' ∩ Finset.Icc 0 (l' - x)).card : ℕ) : ℤ) +
      (((Finset.Icc 0 (l' - x) \ A').card : ℕ) : ℤ) = l' - x + 1 := by
    rw [← hIcc]
    exact_mod_cast hcardS
  omega

end Misses

/-! ### No misses below `t` in the gap regime -/

section NoLowMisses

variable {A : Finset ℤ} {l l' : ℤ}

/-- In the gap regime (`2r ≤ l' + 1 − 2h`), every `x ∈ [1, t)` is a positive
difference of `A' = A ∖ {l}`.  Indeed a missed `x < t` makes the top
`A' ∩ [x, l']` thin (`≤ h`), so at least `k' − h` elements lie below `x < t`,
whence `s ≥ k' − h` and `2r ≥ 2(l' + 1 − 2h)` — contradiction. -/
lemma mem_posDiff_of_gap_lt
    (h0 : 0 ∈ A) (hl : l ∈ A)
    (hmem : ∀ x ∈ A, 0 ≤ x ∧ x ≤ l)
    (hl'mem : l' ∈ A.erase l) (hl'max : ∀ a' ∈ A.erase l, a' ≤ l')
    (hk : l' + 3 ≤ 2 * ((A.erase l).card : ℤ))
    (hr : 2 * ((removeMaxR A l : ℤ)) ≤
      l' + 1 - 2 * (l' + 1 - (A.erase l).card))
    {x : ℤ} (hx : x ∈ Finset.Icc 1 (l - l' - 1)) :
    x ∈ posDiff (A.erase l) := by
  classical
  have hmin : ∀ x ∈ A, 0 ≤ x := fun x hx => (hmem x hx).1
  have hmax : ∀ x ∈ A, x ≤ l := fun x hx => (hmem x hx).2
  have hmem' : ∀ x ∈ A.erase l, 0 ≤ x ∧ x ≤ l' := fun x hx =>
    ⟨hmin x (Finset.mem_erase.1 hx).2, hl'max x hx⟩
  have hxI := Finset.mem_Icc.1 hx
  -- `t ≤ l'`: otherwise `s = k'` and `r ≥ k'` contradicts the gap bound.
  have htle : l - l' ≤ l' := by
    by_contra hcon
    push Not at hcon
    have hsubs : (A.erase l).filter (fun a' => a' < l - l') = A.erase l := by
      apply Finset.filter_true_of_mem
      intro a' ha'
      have := hl'max a' ha'
      omega
    have hsr := card_filter_lt_sub_le_removeMaxR hmin hl'max
    have hcast : (((A.erase l).filter (fun a' => a' < l - l')).card : ℤ) ≤
        (removeMaxR A l : ℤ) := by exact_mod_cast hsr
    rw [hsubs] at hcast
    have hl'0 : 0 ≤ l' := (hmem' l' hl'mem).1
    omega
  by_contra hxP
  -- The missed `x` gives `|A' ∩ [x, l']| ≤ h`.
  have hx1 : 1 ≤ x := hxI.1
  have hx2 : x ≤ l' - 1 := by omega
  have hthin := card_top_le_holes_of_not_mem_posDiff hmem' hx1 hx2 hxP
  -- `A' ∩ [0, x)` and `A' ∩ [x, l']` partition `A'`.
  have hsplit : ((A.erase l).filter (· < x)).card +
      ((A.erase l) ∩ Finset.Icc x l').card = (A.erase l).card := by
    have hunion : ((A.erase l).filter (· < x)) ∪
        ((A.erase l) ∩ Finset.Icc x l') = A.erase l := by
      ext z
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_inter,
        Finset.mem_Icc]
      constructor
      · rintro (⟨hz, -⟩ | ⟨hz, -⟩) <;> exact hz
      · intro hz
        have hz' := hmem' z hz
        rcases lt_or_le z x with h | h
        · exact Or.inl ⟨hz, h⟩
        · exact Or.inr ⟨hz, h, hz'.2⟩
    have hdisj : Disjoint ((A.erase l).filter (· < x))
        ((A.erase l) ∩ Finset.Icc x l') := by
      rw [Finset.disjoint_left]
      intro z hz1 hz2
      have h1 := (Finset.mem_filter.1 hz1).2
      have h2 := Finset.mem_Icc.1 (Finset.mem_inter.1 hz2).2
      omega
    rw [← hunion]
    exact (Finset.card_union_of_disjoint hdisj).symm
  -- `s ≥ |A' ∩ [0, x)| ≥ k' − h`.
  have hslt : (A.erase l).filter (· < x) ⊆
      (A.erase l).filter (fun a' => a' < l - l') := by
    intro z hz
    have hz1 := (Finset.mem_filter.1 hz).2
    exact Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hz).1, by omega⟩
  have hscard : ((A.erase l).filter (· < x)).card ≤
      ((A.erase l).filter (fun a' => a' < l - l')).card :=
    Finset.card_le_card hslt
  have hsr := card_filter_lt_sub_le_removeMaxR hmin hl'max
  have hcastr : (((A.erase l).filter (fun a' => a' < l - l')).card : ℤ) ≤
      (removeMaxR A l : ℤ) := by exact_mod_cast hsr
  have hcastx : (((A.erase l).filter (· < x)).card : ℤ) +
      ((((A.erase l) ∩ Finset.Icc x l').card : ℕ) : ℤ) =
      ((A.erase l).card : ℤ) := by
    exact_mod_cast hsplit
  omega

end NoLowMisses

/-! ### The `RemoveMaxGapResidual` statement -/

/-- **The residual inverse statement of the gap disjunct**, in its sharpest
reduced form.  For `A' ⊆ [0, l']` containing `0, l'` and dense
(`l' + 3 ≤ 2|A'|`), with `l ≥ 2|A'|`, `t := l − l'`, `h := l' + 1 − |A'|` and
`r := s + u` (the remove-max defect: `s` elements of `A'` below `t` and `u`
top elements whose `l`-reflection is not a difference), if no positive
difference is missed below `t` and `2r ≤ l' + 1 − 2h`, then at least
`(l' − h + 2)/2 − t` of the holes of `A'` in the top window `[t, l']` have
their `l`-reflection realised as a positive difference:

  `2·|{x ∈ [t, l'] ∖ A' : l − x ∈ posDiff A'}| ≥ l' − h + 2 − 2t`.

Equivalently `m' + α ≤ (l' + h)/2` (the number of `m'`-misses plus the top
count is at most half of `l' + h`).  This is sharp: equality holds for
`A' = {0,3,6,7,9,10,12,13,15,16,19}`, `l = 22`. -/
def RemoveMaxGapResidual : Prop :=
  ∀ (A' : Finset ℤ) (l l' : ℤ),
    0 ∈ A' → l' ∈ A' → (∀ x ∈ A', 0 ≤ x ∧ x ≤ l') →
    l' + 3 ≤ 2 * (A'.card : ℤ) →
    2 * (A'.card : ℤ) ≤ l →
    (∀ x ∈ Finset.Icc 1 (l - l' - 1), x ∈ posDiff A') →
    2 * (((A'.filter fun a' => a' < l - l').card +
        (A'.filter fun a' => l - l' ≤ a' ∧ l - a' ∉ posDiff A').card : ℤ)) ≤
      l' + 1 - 2 * (l' + 1 - (A'.card : ℤ)) →
    l' - (l' + 1 - (A'.card : ℤ)) + 2 - 2 * (l - l') ≤
      2 * (((Finset.Icc (l - l') l' \ A').filter
        (fun x => l - x ∈ posDiff A')).card : ℤ)

/-! ### The conditional theorem -/

section Conditional

variable {A : Finset ℤ} {l l' : ℤ}

/-- `RemoveMaxGapResidual → RemoveMaxGap`.  The bookkeeping: misses lie in
`[t, l']`, `m = u + m'`, `p' + m' = η = w − α`, and the residual bound
`2p' ≥ l' − h + 2 − 2t` gives `|A − A| ≥ 3k'`. -/
theorem removeMaxGap_of_residual (hres : RemoveMaxGapResidual) : RemoveMaxGap := by
  classical
  intro A l l' h0 hl hmem hgcd hlarge hl'mem hl'max hgcd' hgap
  set A' := A.erase l with hA'
  set D' := A'.image₂ (· - ·) A' with hD'
  set P := posDiff A' with hP
  set t := l - l' with ht
  set r := removeMaxR A l with hr
  set s := (A'.filter fun a' => a' < t).card with hs
  set u := (A'.filter fun a' => t ≤ a' ∧ l - a' ∉ P).card with hu
  set M := (Finset.Icc 1 l').filter (· ∉ P) with hM
  set M' := M.filter (fun x => l - x ∉ A') with hM'
  set W := Finset.Icc t l' with hW
  set η := (W \ A').card with hη
  set p' := ((W \ A').filter (fun x => l - x ∈ P)).card with hp'
  set α := (A'.filter (t ≤ ·)).card with hα
  set h := l' + 1 - (A'.card : ℤ) with hh
  have hmin : ∀ x ∈ A, 0 ≤ x := fun x hx => (hmem x hx).1
  have hmax : ∀ x ∈ A, x ≤ l := fun x hx => (hmem x hx).2
  have hmem' : ∀ x ∈ A', 0 ≤ x ∧ x ≤ l' := fun x hx =>
    ⟨hmin x (Finset.mem_erase.1 hx).2, hl'max x hx⟩
  have hl'l : l' < l :=
    lt_of_le_of_ne (hmax l' (Finset.mem_erase.1 hl'mem).2)
      (Finset.mem_erase.1 hl'mem).1
  have htpos : 1 ≤ t := by omega
  -- `|A| ≥ 2` from the coprimality hypothesis at `d = 2`.
  obtain ⟨x₂, hx₂, y₂, hy₂, hxy₂⟩ := hgcd 2 (le_refl 2)
  have hne2 : x₂ ≠ y₂ := fun e => hxy₂ (e ▸ by simp)
  have hk2 : 2 ≤ A.card := by
    have hsub : ({x₂, y₂} : Finset ℤ) ⊆ A := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact hx₂
      · exact hy₂
    have h := Finset.card_le_card hsub
    rwa [Finset.card_pair hne2] at h
  have hl0 : 0 < l := by
    have := hmin l hl; omega
  have h0' : (0 : ℤ) ∈ A' := Finset.mem_erase.2 ⟨ne_of_lt hl0, h0⟩
  have hcardA' : ((A'.card : ℤ)) = (A.card : ℤ) - 1 := by
    have h := Finset.card_erase_of_mem hl
    omega
  have hr1 : 1 ≤ r := one_le_removeMaxR h0 hl hmin hmax hl0
  -- The gap gives `l' ≤ 2k' − 3` (density) and `2r ≤ l' + 1 − 2h`.
  have hdense : l' + 3 ≤ 2 * (A'.card : ℤ) := by omega
  have hrgap : 2 * (r : ℤ) ≤ l' + 1 - 2 * h := by omega
  have h2k'l : 2 * (A'.card : ℤ) ≤ l := by omega
  -- `r = s + u`.
  have hrsu : r = s + u := removeMaxR_eq hmin hmax hl'mem hl'max
  -- `[1, t) ⊆ P`.
  have hlow : ∀ x ∈ Finset.Icc 1 (t - 1), x ∈ P := by
    intro x hx
    exact mem_posDiff_of_gap_lt h0 hl hmem hl'mem hl'max hdense hrgap hx
  -- `M ⊆ W`.
  have hMW : M ⊆ W := by
    intro x hx
    obtain ⟨hxI, hxP⟩ := Finset.mem_filter.1 hx
    have hxB := Finset.mem_Icc.1 hxI
    have hxge : t ≤ x := by
      by_contra hxc
      push Not at hxc
      exact hxP (hlow x (Finset.mem_Icc.2 ⟨hxB.1, by omega⟩))
    exact Finset.mem_Icc.2 ⟨hxge, hxB.2⟩
  -- `t ≤ l'`.
  have htle : t ≤ l' := by
    by_contra hcon
    push Not at hcon
    have hsubs : A'.filter (fun a' => a' < t) = A' := by
      apply Finset.filter_true_of_mem
      intro a' ha'
      have := hl'max a' ha'
      omega
    have hscast : ((s : ℕ) : ℤ) = (A'.card : ℤ) := by rw [hs, hsubs]
    have hsr := card_filter_lt_sub_le_removeMaxR hmin hl'max
    have hcast : (((A'.filter (fun a' => a' < t)).card : ℕ) : ℤ) ≤
        (r : ℤ) := by exact_mod_cast hsr
    have hl'0 : 0 ≤ l' := (hmem' l' hl'mem).1
    omega
  -- `|M| = l' − |P|`.
  have hPsub : P ⊆ Finset.Icc 1 l' := by
    have h := posDiff_subset_Icc (s := A') (m := (0 : ℤ)) (ℓ := l')
      (fun x hx => (hmem' x hx).1) (fun x hx => (hmem' x hx).2)
    rwa [sub_zero] at h
  have hMeq : M = Finset.Icc 1 l' \ P := by
    ext x
    simp [hM, Finset.mem_sdiff, and_comm]
  have hMcard : (M.card : ℤ) = l' - (P.card : ℤ) := by
    have hIcc : ((Finset.Icc (1 : ℤ) l').card : ℤ) = l' := by
      have h' := Int.card_Icc_of_le (a := (1 : ℤ)) (b := l') (by omega)
      omega
    have hsub : P.card ≤ (Finset.Icc (1 : ℤ) l').card := Finset.card_le_card hPsub
    rw [hMeq, Finset.card_sdiff_of_subset hPsub, Nat.cast_sub hsub, hIcc]
  -- `|M| = u + m'` via `|M_u| = u`.
  have hMusplit : M.card =
      (M.filter (fun x => l - x ∈ A')).card + M'.card := by
    have h : M = M.filter (fun x => l - x ∈ A') ∪ M' := by
      ext x
      simp only [hM', Finset.mem_union, Finset.mem_filter]
      constructor
      · intro hx
        rcases em (l - x ∈ A') with h | h
        · exact Or.inl ⟨hx, h⟩
        · exact Or.inr ⟨hx, h⟩
      · rintro (⟨hx, -⟩ | ⟨hx, -⟩) <;> exact hx
    have hdisj : Disjoint (M.filter (fun x => l - x ∈ A')) M' := by
      rw [hM', Finset.disjoint_left]
      intro x hx1 hx2
      exact (Finset.mem_filter.1 hx2).2 (Finset.mem_filter.1 hx1).2
    rw [h]
    exact Finset.card_union_of_disjoint hdisj
  have hMu : (M.filter (fun x => l - x ∈ A')).card = u := by
    -- Bijection `x ↦ l − x` onto `U`.
    have hbij : (M.filter (fun x => l - x ∈ A')).image (l - ·) =
        A'.filter (fun a' => t ≤ a' ∧ l - a' ∉ P) := by
      ext z
      simp only [Finset.mem_image, Finset.mem_filter]
      constructor
      · rintro ⟨x, ⟨⟨hxI, hxP⟩, hxA⟩, rfl⟩
        have hxW := Finset.mem_Icc.1 (hMW x (Finset.mem_filter.2 ⟨hxI, hxP⟩))
        refine ⟨⟨hxA, by omega⟩, ?_⟩
        rw [show l - (l - x) = x by ring]
        exact hxP
      · rintro ⟨⟨hzA, hzt⟩, hzP⟩
        have hzle := (hmem' z hzA).2
        refine ⟨l - z, ⟨⟨Finset.mem_Icc.2 ⟨by omega, by omega⟩, ?_⟩, ?_⟩, by ring⟩
        · rw [show l - (l - z) = z by ring]
          exact hzP
        · exact hzA
    rw [← hbij, Finset.card_image_of_injective]
    · congr 1
    · intro a b hab
      have : l - a = l - b := hab
      omega
  -- `p' + m' = η`: the `l − ·` involution sends `M'` onto
  -- `{x ∈ W ∖ A' : l − x ∉ P}`.
  have hFmbij : (M'.image (l - ·)) =
      (W \ A').filter (fun x => l - x ∉ P) := by
    ext z
    simp only [hM', hM, hW, Finset.mem_image, Finset.mem_filter, Finset.mem_sdiff,
      Finset.mem_Icc]
    constructor
    · rintro ⟨x, ⟨⟨⟨hx1, hx2⟩, hxP⟩, hxA⟩, rfl⟩
      refine ⟨⟨⟨by omega, by omega⟩, hxA⟩, ?_⟩
      rw [show l - (l - x) = x by ring]
      exact hxP
    · rintro ⟨⟨⟨hz1, hz2⟩, hzA⟩, hzP⟩
      refine ⟨l - z, ⟨⟨⟨by omega, by omega⟩, ?_⟩, ?_⟩, by ring⟩
      · rw [show l - (l - z) = z by ring]
        exact hzP
      · exact hzA
  have hFmcard : ((W \ A').filter (fun x => l - x ∉ P)).card = M'.card := by
    rw [← hFmbij, Finset.card_image_of_injective]
    intro a b hab
    have : l - a = l - b := hab
    omega
  have hsplitη : (W \ A') =
      ((W \ A').filter (fun x => l - x ∈ P)) ∪
        ((W \ A').filter (fun x => l - x ∉ P)) := by
    ext x
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hx
      rcases em (l - x ∈ P) with h | h
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr ⟨hx, h⟩
    · rintro (⟨hx, -⟩ | ⟨hx, -⟩) <;> exact hx
  have hηsplit : η = p' + M'.card := by
    have hdisj : Disjoint ((W \ A').filter (fun x => l - x ∈ P))
        ((W \ A').filter (fun x => l - x ∉ P)) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      exact (Finset.mem_filter.1 hx2).2 (Finset.mem_filter.1 hx1).2
    have h := Finset.card_union_of_disjoint hdisj
    rw [← hsplitη, h] at *
    rw [hη]
    rw [← hFmcard]
  -- `η = w − α` with `w = l' − t + 1`.
  have hA'W : A' ∩ W = A'.filter (t ≤ ·) := by
    ext x
    simp only [hW, Finset.mem_inter, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨hxA, hxt, -⟩
      exact ⟨hxA, hxt⟩
    · rintro ⟨hxA, hxt⟩
      exact ⟨hxA, hxt, (hmem' x hxA).2⟩
  have hηeq : (η : ℤ) = l' - t + 1 - (α : ℤ) := by
    have hsd : (W \ A').card = W.card - (A' ∩ W).card := by
      have h' : W \ A' = W \ (A' ∩ W) := by
        ext x
        simp [Finset.mem_sdiff, Finset.mem_inter]
      rw [h']
      exact Finset.card_sdiff_of_subset Finset.inter_subset_right
    have hIcc : ((Finset.Icc t l').card : ℤ) = l' - t + 1 := by
      have h' := Int.card_Icc_of_le (a := t) (b := l') (by omega)
      omega
    have hα' : ((A' ∩ W).card : ℤ) = (α : ℤ) := by rw [hA'W]
    rw [hη]
    have hcast : ((W \ A').card : ℤ) = (W.card : ℤ) - ((A' ∩ W).card : ℤ) := by
      rw [hsd, Nat.cast_sub (Finset.card_le_card Finset.inter_subset_right)]
    rw [hcast]
    rw [hα']
    have hWcard : (W.card : ℤ) = l' - t + 1 := by rw [hW]; exact hIcc
    rw [hWcard]
  -- `s + α = k'`.
  have hsα : s + α = A'.card := by
    have h : A'.filter (· < t) ∪ A'.filter (t ≤ ·) = A' := by
      ext x
      simp only [Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro (⟨hx, -⟩ | ⟨hx, -⟩) <;> exact hx
      · intro hx
        rcases lt_or_le x t with h' | h'
        · exact Or.inl ⟨hx, h'⟩
        · exact Or.inr ⟨hx, h'⟩
    have hdisj : Disjoint (A'.filter (· < t)) (A'.filter (t ≤ ·)) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      have h1 := (Finset.mem_filter.1 hx1).2
      have h2 := (Finset.mem_filter.1 hx2).2
      omega
    have hc := Finset.card_union_of_disjoint hdisj
    rw [h] at hc
    rw [hs, hα]
    exact hc
  -- Apply the residual.
  have hres' := hres A' l l' h0' hl'mem hmem' hdense h2k'l hlow
    (by
      have hcast : (((s + u : ℕ) : ℤ)) ≤ l' + 1 - 2 * h := by
        rw [← hrsu]
        exact hrgap
      rw [hs, hu, ht, hh] at hcast
      exact_mod_cast hcast)
  -- Final assembly: `|A − A| = |D'| + 2r`, `|D'| = 2|P| + 1`,
  -- `|P| = l' − m`, `m = u + m'`, `p' + m' = η = l' − t + 1 − α`, `s + α = k'`.
  have hD'card : (D'.card : ℤ) = 2 * (P.card : ℤ) + 1 := by
    have hne : A'.Nonempty := ⟨0, h0'⟩
    have h' := card_image_sub_self hne
    rw [← hP] at h'
    rw [← hD'] at h'
    exact_mod_cast h'
  have hident := card_sub_self_eq_erase_add_two_mul_r h0 hl hmin hmax hl0
  rw [← hA', ← hD', ← hr] at hident
  have hmeq : (M.card : ℤ) = (u : ℤ) + (M'.card : ℤ) := by
    have h1 : ((M.filter (fun x => l - x ∈ A')).card : ℤ) = (u : ℤ) := by
      exact_mod_cast hMu
    have h2 : (M.card : ℤ) =
        ((M.filter (fun x => l - x ∈ A')).card : ℤ) + (M'.card : ℤ) := by
      exact_mod_cast hMusplit
    rw [h1] at h2
    exact h2
  have hηcast : (η : ℤ) = (p' : ℤ) + (M'.card : ℤ) := by exact_mod_cast hηsplit
  have hrsuZ : (r : ℤ) = (s : ℤ) + (u : ℤ) := by exact_mod_cast hrsu
  have hsαZ : (s : ℤ) + (α : ℤ) = (A'.card : ℤ) := by exact_mod_cast hsα
  omega

end Conditional

end JSP000728
