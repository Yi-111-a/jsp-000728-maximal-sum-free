/-
Freiman's `3k − 4` inverse theorem for subsets of the integers.

Target theorem: if `A : Finset ℤ` satisfies `4 ≤ |A|` and `|A + A| ≤ 3|A| − 4`,
then `A` is contained in an arithmetic progression of length at most
`|A + A| − |A| + 1` (and hence at most `2|A| − 3`).

This file contains the provable components of the classical proof:

* `card_add_self_ge` — the trivial bound `2|A| − 1 ≤ |A + A|` (ordered
  Cauchy–Davenport, already in Mathlib).
* `card_image₂_add_const`, `card_image₂_mul_const` — translation and dilation
  invariance of the sumset cardinality.
* `subset_image_progression` — every set inside `[0, l]` is contained in the
  difference-`1` progression `{0, 1, …, l}`.
* `card_add_self_ge_diam_add_card` — **the small-diameter case of Freiman's
  doubling lemma**: for `0, l ∈ A ⊆ [0, l]` with `l + 3 ≤ 2|A|` one has
  `l + |A| ≤ |A + A|`.  The proof is a fully elementary double-counting
  argument (no gcd hypothesis needed): if a hole `x ∈ [0, l) \ A` satisfied
  `x ∉ 2A` and `x + l ∉ 2A`, then `A ∩ [0, x]` and `x − (A ∩ [0, x])` would be
  disjoint subsets of `[0, x]` while `A ∩ [x, l]` and `x + l − (A ∩ [x, l])`
  would be disjoint subsets of `[x, l]`, forcing `2|A| ≤ l + 2`.
* `card_add_self_ge_card_add_zmod` — the **modular fiber bound**: writing
  `Ā` for the image of `A ∖ {l}` in `ZMod l`, one has
  `|A| + |Ā + Ā| ≤ |A + A|` (every residue class of `(Ā + Ā) ∖ Ā` is
  represented by an element of `A + A` outside `A ∪ (l + A)`).
* `card_add_self_ge_three_mul_sub_three_of_minFac` — **the large-diameter
  case when `l` has no small prime factor**: if `minFac l ≥ 2|A| − 3` (e.g.
  `l` prime) then `3|A| − 3 ≤ |A + A|`, by the Cauchy–Davenport bound
  `|Ā + Ā| ≥ min (minOrder (ZMod l)) (2|Ā| − 1)` with
  `minOrder (ZMod l) = minFac l`.
* `exists_gcd_normalize` — **gcd normalisation**: `A = d • A'` with
  `gcd A' = 1`, preserving `|A|` and `|A + A|`.
* `freiman_3k4_of_diam_or_minFac` — the `3k − 4` conclusion
  (`A ⊆` AP of length `≤ |A + A| − |A| + 1`) in the two cases covered above:
  diameter `l + 3 ≤ 2|A|`, or `minFac l ≥ 2|A| − 3`.

The final section works on the difference set `A − A` (the object of
`Freiman3k4` in `JSPProblem/DFSTBridge.lean`):

* `card_add_ge_diam_add_card` — **two-set small-diameter bound**: for
  `A, B ⊆ [0, l]` with `0 ∈ A ∩ B`, `l ∈ A` and `l + 3 ≤ |A| + |B|`, one has
  `|A + B| ≥ l + |B|` (the same hole-counting argument as for `A + A`).
* `card_sub_self_ge_diam_add_card` — `|A − A| ≥ l + |A|` when
  `l + 3 ≤ 2|A|`, via `B = l − A` and `A + B = l + (A − A)`.
* `card_sub_self_ge` — the trivial bound `2|A| − 1 ≤ |A − A|`.
* `card_sub_self_ge_zmod` — the **modular fiber bound for `A − A`**:
  `|A − A| ≥ |B − B| + |B ∪ (−B)| + 1` for the modular shadow
  `B = (A ∖ {l}) ⊆ ZMod l`.  This is sharper than the sumset analogue
  `card_add_self_ge_card_add_zmod`: every residue class of `B` or `−B`
  realises a difference `a − a'` in *both* directions `mod l`, so those
  classes contribute two elements of `A − A ⊆ [−l, l]` each.
* `card_sub_self_ge_three_mul_sub_three_of_minFac` — `|A − A| ≥ 3|A| − 3`
  when `minFac l ≥ 2|A| − 3`.
* `Freiman3k4Residual` — the **residual periodic-boundary case**
  (`2|A| − 2 ≤ l` and `minFac l ≤ 2|A| − 4`), and
  `freiman3k4 : Freiman3k4Residual → Freiman3k4`, which reduces the full
  Freiman `3k − 4` difference bound to exactly that case.

The remaining obstruction to the **full** `3k − 4` theorem is precisely
`Freiman3k4Residual`: for `l ≥ 2|A| − 2` with a small prime factor, the
stabiliser of `B − B` in `ZMod l` may be nontrivial, and one needs the
periodic-boundary part of Freiman's argument (equivalently an application of
Kneser's theorem for cyclic groups, which is not currently in Mathlib in
usable form) to derive the `3|A| − 3` bound from the coprimality hypothesis.
-/

import JSPProblem.DFSTBridge
import Mathlib.Combinatorics.Additive.CauchyDavenport

namespace JSP000728

open Finset
open scoped Pointwise

/-! ### Trivial bound -/

/-- For a nonempty set of integers, `|A + A| ≥ 2|A| − 1`.  This is the ordered
(torsion-free) Cauchy–Davenport theorem specialised to `s = t = A`. -/
theorem card_add_self_ge {A : Finset ℤ} (hA : A.Nonempty) :
    2 * A.card - 1 ≤ (A.image₂ (· + ·) A).card := by
  have h := cauchy_davenport_add_of_linearOrder_isCancelAdd hA hA
  have h2 : A + A = A.image₂ (· + ·) A := rfl
  rw [h2] at h
  omega

/-! ### Translation and dilation invariance -/

/-- Translating a set preserves the sumset cardinality. -/
theorem card_image₂_add_const (A : Finset ℤ) (t : ℤ) :
    ((A.image (· + t)).image₂ (· + ·) (A.image (· + t))).card =
      (A.image₂ (· + ·) A).card := by
  have hmap : (A.image (· + t)).image₂ (· + ·) (A.image (· + t)) =
      (A.image₂ (· + ·) A).image (· + 2 * t) := by
    ext x
    simp only [mem_image₂, mem_image]
    constructor
    · rintro ⟨a, ⟨a', ha', rfl⟩, b, ⟨b', hb', rfl⟩, rfl⟩
      exact ⟨a' + b', ⟨a', ha', b', hb', rfl⟩, by ring⟩
    · rintro ⟨x', ⟨a', ha', b', hb', rfl⟩, rfl⟩
      exact ⟨a' + t, ⟨a', ha', rfl⟩, b' + t, ⟨b', hb', rfl⟩, by ring⟩
  rw [hmap]
  exact card_image_of_injective _ (add_left_injective (2 * t))

/-- Translating a set preserves its cardinality. -/
theorem card_image_add_const (A : Finset ℤ) (t : ℤ) :
    (A.image (· + t)).card = A.card :=
  card_image_of_injective _ (add_left_injective t)

/-- Dilating a set by a nonzero factor preserves the sumset cardinality. -/
theorem card_image₂_mul_const {A : Finset ℤ} {d : ℤ} (hd : d ≠ 0) :
    ((A.image (d * ·)).image₂ (· + ·) (A.image (d * ·))).card =
      (A.image₂ (· + ·) A).card := by
  have hmap : (A.image (d * ·)).image₂ (· + ·) (A.image (d * ·)) =
      (A.image₂ (· + ·) A).image (d * ·) := by
    ext x
    simp only [mem_image₂, mem_image]
    constructor
    · rintro ⟨a, ⟨a', ha', rfl⟩, b, ⟨b', hb', rfl⟩, rfl⟩
      exact ⟨a' + b', ⟨a', ha', b', hb', rfl⟩, by ring⟩
    · rintro ⟨x', ⟨a', ha', b', hb', rfl⟩, rfl⟩
      exact ⟨d * a', ⟨a', ha', rfl⟩, d * b', ⟨b', hb', rfl⟩, by ring⟩
  rw [hmap]
  exact card_image_of_injective _ (mul_right_injective₀ hd)

/-- Dilating a set by a nonzero factor preserves its cardinality. -/
theorem card_image_mul_const {A : Finset ℤ} {d : ℤ} (hd : d ≠ 0) :
    (A.image (d * ·)).card = A.card :=
  card_image_of_injective _ (mul_right_injective₀ hd)

/-! ### Containment in a difference-`1` progression -/

/-- Every `x ∈ [0, l]` lies in the progression image
`image (fun i : ℕ => (i : ℤ)) (range (l.toNat + 1))`. -/
theorem mem_image_progression {x l : ℤ} (h0 : 0 ≤ x) (hx : x ≤ l) :
    x ∈ Finset.image (fun i : ℕ => (i : ℤ)) (Finset.range (l.toNat + 1)) := by
  refine Finset.mem_image.2 ⟨x.toNat, ?_, ?_⟩
  · exact Finset.mem_range.2 (by omega)
  · exact Int.toNat_of_nonneg h0

/-- A set inside `[0, l]` is contained in the difference-`1` progression of
length `l + 1`. -/
theorem subset_image_progression {A : Finset ℤ} {l : ℤ}
    (hmin : ∀ a ∈ A, 0 ≤ a) (hmax : ∀ a ∈ A, a ≤ l) :
    A ⊆ Finset.image (fun i : ℕ => (i : ℤ)) (Finset.range (l.toNat + 1)) := by
  intro a ha
  exact mem_image_progression (hmin a ha) (hmax a ha)

/-! ### The small-diameter doubling lemma -/

section SmallDiameter

variable {A : Finset ℤ} {x l : ℤ}

/-- If `x ∉ A + A`, then `A ∩ (−∞, x]` and its reflection `x − (A ∩ (−∞, x])`
are disjoint. -/
lemma disjoint_filter_le_image {A : Finset ℤ} {x : ℤ}
    (hx : x ∉ A.image₂ (· + ·) A) :
    Disjoint (A.filter (· ≤ x)) ((A.filter (· ≤ x)).image (x - ·)) := by
  rw [Finset.disjoint_left]
  intro a ha hb
  obtain ⟨b, hblo, hab⟩ := Finset.mem_image.1 hb
  have haA := (Finset.mem_filter.1 ha).1
  have hbA := (Finset.mem_filter.1 hblo).1
  apply hx
  have h : x = a + b := by omega
  rw [h]
  exact Finset.mem_image₂_of_mem haA hbA

/-- If `x + l ∉ A + A`, then `A ∩ [x, ∞)` and its reflection
`x + l − (A ∩ [x, ∞))` are disjoint. -/
lemma disjoint_filter_ge_image {A : Finset ℤ} {x l : ℤ}
    (hx : x + l ∉ A.image₂ (· + ·) A) :
    Disjoint (A.filter (x ≤ ·)) ((A.filter (x ≤ ·)).image (x + l - ·)) := by
  rw [Finset.disjoint_left]
  intro a ha hb
  obtain ⟨b, hbhi, hab⟩ := Finset.mem_image.1 hb
  have haA := (Finset.mem_filter.1 ha).1
  have hbA := (Finset.mem_filter.1 hbhi).1
  apply hx
  have h : x + l = a + b := by omega
  rw [h]
  exact Finset.mem_image₂_of_mem haA hbA

/-- Low-side doubling: `2 |A ∩ (−∞, x]| ≤ |[0, x]|` when `x ∉ A + A`. -/
lemma two_mul_card_filter_le {A : Finset ℤ} {x : ℤ}
    (hmin : ∀ a ∈ A, 0 ≤ a) (hx : x ∉ A.image₂ (· + ·) A) :
    2 * (A.filter (· ≤ x)).card ≤ (Finset.Icc 0 x).card := by
  classical
  set lo := A.filter (· ≤ x)
  have hsub : lo ∪ lo.image (x - ·) ⊆ Finset.Icc 0 x := by
    intro y hy
    rcases Finset.mem_union.1 hy with h | h
    · have hAy := (Finset.mem_filter.1 h).1
      have hyx := (Finset.mem_filter.1 h).2
      exact Finset.mem_Icc.2 ⟨hmin y hAy, hyx⟩
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 h
      have haA := (Finset.mem_filter.1 ha).1
      have hax := (Finset.mem_filter.1 ha).2
      have ha0 := hmin a haA
      exact Finset.mem_Icc.2 ⟨by omega, by omega⟩
  have hcard : (lo.image (x - ·)).card = lo.card :=
    Finset.card_image_of_injective _ (fun a b h => by omega)
  have hunion : (lo ∪ lo.image (x - ·)).card = 2 * lo.card := by
    rw [Finset.card_union_of_disjoint (disjoint_filter_le_image hx), hcard, two_mul]
  calc 2 * lo.card = (lo ∪ lo.image (x - ·)).card := hunion.symm
    _ ≤ (Finset.Icc 0 x).card := Finset.card_le_card hsub

/-- High-side doubling: `2 |A ∩ [x, ∞)| ≤ |[x, l]|` when `x + l ∉ A + A`. -/
lemma two_mul_card_filter_ge {A : Finset ℤ} {x l : ℤ}
    (hmax : ∀ a ∈ A, a ≤ l) (hx : x + l ∉ A.image₂ (· + ·) A) :
    2 * (A.filter (x ≤ ·)).card ≤ (Finset.Icc x l).card := by
  classical
  set hi := A.filter (x ≤ ·)
  have hsub : hi ∪ hi.image (x + l - ·) ⊆ Finset.Icc x l := by
    intro y hy
    rcases Finset.mem_union.1 hy with h | h
    · have hAy := (Finset.mem_filter.1 h).1
      have hxy := (Finset.mem_filter.1 h).2
      exact Finset.mem_Icc.2 ⟨hxy, hmax y hAy⟩
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 h
      have haA := (Finset.mem_filter.1 ha).1
      have hxa := (Finset.mem_filter.1 ha).2
      have hal := hmax a haA
      exact Finset.mem_Icc.2 ⟨by omega, by omega⟩
  have hcard : (hi.image (x + l - ·)).card = hi.card :=
    Finset.card_image_of_injective _ (fun a b h => by omega)
  have hunion : (hi ∪ hi.image (x + l - ·)).card = 2 * hi.card := by
    rw [Finset.card_union_of_disjoint (disjoint_filter_ge_image hx), hcard, two_mul]
  calc 2 * hi.card = (hi ∪ hi.image (x + l - ·)).card := hunion.symm
    _ ≤ (Finset.Icc x l).card := Finset.card_le_card hsub

/-- **Uncovered holes force large diameter.** If `x ∈ [0, l]` is a hole of `A`
with `x ∉ A + A` and `x + l ∉ A + A`, then `2|A| ≤ l + 2`. -/
lemma two_mul_card_le_of_uncovered {A : Finset ℤ} {x l : ℤ}
    (hmin : ∀ a ∈ A, 0 ≤ a) (hmax : ∀ a ∈ A, a ≤ l)
    (hx0 : 0 ≤ x) (hxl : x ≤ l)
    (hx : x ∉ A.image₂ (· + ·) A) (hxl' : x + l ∉ A.image₂ (· + ·) A) :
    2 * A.card ≤ l + 2 := by
  classical
  have hlo := two_mul_card_filter_le hmin hx
  have hhi := two_mul_card_filter_ge hmax hxl'
  have hcover : A ⊆ A.filter (· ≤ x) ∪ A.filter (x ≤ ·) := by
    intro a ha
    rcases le_total a x with h | h
    · exact Finset.mem_union.2 (Or.inl (Finset.mem_filter.2 ⟨ha, h⟩))
    · exact Finset.mem_union.2 (Or.inr (Finset.mem_filter.2 ⟨ha, h⟩))
  have hAc : A.card ≤ (A.filter (· ≤ x)).card + (A.filter (x ≤ ·)).card :=
    (Finset.card_le_card hcover).trans (Finset.card_union_le _ _)
  have hIcc0 : ((Finset.Icc (0 : ℤ) x).card : ℤ) = x + 1 := by
    have h := Int.card_Icc_of_le (a := (0 : ℤ)) (b := x) (by omega)
    omega
  have hIccx : ((Finset.Icc x l).card : ℤ) = l - x + 1 := by
    have h := Int.card_Icc_of_le (a := x) (b := l) (by omega)
    omega
  have hlo' : (2 * (A.filter (· ≤ x)).card : ℤ) ≤ x + 1 := by
    calc (2 * (A.filter (· ≤ x)).card : ℤ) ≤ ((Finset.Icc 0 x).card : ℤ) := by
          exact_mod_cast hlo
      _ = x + 1 := hIcc0
  have hhi' : (2 * (A.filter (x ≤ ·)).card : ℤ) ≤ l - x + 1 := by
    calc (2 * (A.filter (x ≤ ·)).card : ℤ) ≤ ((Finset.Icc x l).card : ℤ) := by
          exact_mod_cast hhi
      _ = l - x + 1 := hIccx
  have hAc' : (A.card : ℤ) ≤
      (A.filter (· ≤ x)).card + (A.filter (x ≤ ·)).card := by
    exact_mod_cast hAc
  omega

/-- **Small-diameter doubling lemma.** For `A ⊆ [0, l]` containing `0` and `l`
with `l + 3 ≤ 2|A|`, every hole of `A` in `[0, l]` contributes to `A + A`, and
`|A + A| ≥ l + |A|`. -/
theorem card_add_self_ge_diam_add_card {A : Finset ℤ} {l : ℤ}
    (h0 : 0 ∈ A) (hl : l ∈ A)
    (hmin : ∀ a ∈ A, 0 ≤ a) (hmax : ∀ a ∈ A, a ≤ l)
    (hk : l + 3 ≤ 2 * A.card) :
    l + A.card ≤ (A.image₂ (· + ·) A).card := by
  classical
  set S2 := A.image₂ (· + ·) A
  have hl0 : 0 ≤ l := hmin l hl
  -- `A ⊆ 2A` (via `0 ∈ A`) and `l + A ⊆ 2A` (via `l ∈ A`).
  have hAsub : A ⊆ S2 := fun a ha => by
    have h : a = 0 + a := by ring
    rw [h]; exact Finset.mem_image₂_of_mem h0 ha
  have hlA : A.image (l + ·) ⊆ S2 := by
    intro y hy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hy
    exact Finset.mem_image₂_of_mem hl ha
  -- `A ∩ (l + A) = {l}`.
  have hinter : A ∩ A.image (l + ·) = {l} := by
    ext y
    simp only [Finset.mem_inter, Finset.mem_image, Finset.mem_singleton]
    constructor
    · rintro ⟨hyA, a, ha, rfl⟩
      have ha0 := hmin a ha
      have hay : l + a ≤ l := hmax _ hyA
      have ha0' : a = 0 := by omega
      rw [ha0']; ring
    · rintro rfl
      exact ⟨hl, ⟨0, h0, by ring⟩⟩
  -- `|A ∪ (l + A)| = 2|A| − 1`.
  have hunion_card : (A ∪ A.image (l + ·)).card = 2 * A.card - 1 := by
    have himg : (A.image (l + ·)).card = A.card :=
      Finset.card_image_of_injective _ (add_right_injective l)
    have hpos : 0 < A.card := Finset.card_pos.2 ⟨0, h0⟩
    have := Finset.card_union_add_card_inter A (A.image (l + ·))
    rw [hinter, Finset.card_singleton, himg] at this
    omega
  -- Every hole `x ∈ [0, l] \ A` is covered: `x ∈ 2A` or `x + l ∈ 2A`.
  set holes := (Finset.Icc 0 l).filter (· ∉ A)
  have hhole : ∀ x ∈ holes, x ∈ S2 ∨ x + l ∈ S2 := by
    intro x hx
    have hxI := Finset.mem_Icc.1 (Finset.mem_filter.1 hx).1
    by_contra h
    push Not at h
    have := two_mul_card_le_of_uncovered hmin hmax hxI.1 hxI.2 h.1 h.2
    omega
  -- The map `x ↦ if x ∈ 2A then x else x + l` sends holes injectively into
  -- `2A \ (A ∪ l + A)`.
  have hf_mem : ∀ x ∈ holes,
      (if x ∈ S2 then x else x + l) ∈ S2 \ (A ∪ A.image (l + ·)) := by
    intro x hx
    have hxI := Finset.mem_Icc.1 (Finset.mem_filter.1 hx).1
    have hxA := (Finset.mem_filter.1 hx).2
    by_cases hxs : x ∈ S2
    · rw [ite_eq_left hxs]
      simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_image, not_or,
        not_exists]
      refine ⟨hxs, hxA, fun a ha => ?_⟩
      have ha0 := hmin a ha.1
      have haeq := ha.2
      have : x = l := by omega
      exact hxA (this ▸ hl)
    · rw [ite_eq_right hxs]
      have hxl2 : x + l ∈ S2 := (hhole x hx).resolve_left hxs
      simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_image, not_or,
        not_exists]
      refine ⟨hxl2, fun hA' => ?_, fun a ha => ?_⟩
      · have hxl' := hmax _ hA'
        have hxpos : x ≠ 0 := fun e => hxA (e ▸ h0)
        omega
      · have haeq := ha.2
        have : x = a := by omega
        exact hxA (this ▸ ha.1)
  have hf_inj : ∀ x ∈ holes, ∀ y ∈ holes,
      (if x ∈ S2 then x else x + l) = (if y ∈ S2 then y else y + l) → x = y := by
    intro x hx y hy hxy
    have hxI := Finset.mem_Icc.1 (Finset.mem_filter.1 hx).1
    have hyI := Finset.mem_Icc.1 (Finset.mem_filter.1 hy).1
    have hxA := (Finset.mem_filter.1 hx).2
    have hyA := (Finset.mem_filter.1 hy).2
    have hx0 : x ≠ 0 := fun e => hxA (e ▸ h0)
    have hxl : x ≠ l := fun e => hxA (e ▸ hl)
    have hy0 : y ≠ 0 := fun e => hyA (e ▸ h0)
    have hyl : y ≠ l := fun e => hyA (e ▸ hl)
    by_cases hxs : x ∈ S2 <;> by_cases hys : y ∈ S2 <;>
      simp only [hxs, hys, ite_true, ite_false] at hxy <;> omega
  -- `|2A| ≥ |A ∪ lA| + |holes|`.
  have hsub : (A ∪ A.image (l + ·)) ∪
      holes.image (fun x => if x ∈ S2 then x else x + l) ⊆ S2 := by
    intro y hy
    rcases Finset.mem_union.1 hy with h | h
    · rcases Finset.mem_union.1 h with h | h
      · exact hAsub h
      · exact hlA h
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 h
      exact (Finset.mem_sdiff.1 (hf_mem x hx)).1
  have hdisj : Disjoint (A ∪ A.image (l + ·))
      (holes.image (fun x => if x ∈ S2 then x else x + l)) := by
    rw [Finset.disjoint_left]
    intro y hy1 hy2
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy2
    exact (Finset.mem_sdiff.1 (hf_mem x hx)).2 hy1
  have himg_card : (holes.image (fun x => if x ∈ S2 then x else x + l)).card =
      holes.card := by
    apply Finset.card_image_iff.2
    intro x hx y hy hxy
    exact hf_inj x (Finset.mem_coe.1 hx) y (Finset.mem_coe.1 hy) hxy
  have hcard : (A ∪ A.image (l + ·)).card + holes.card ≤ S2.card := by
    have := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdisj, himg_card] at this
    exact this
  -- `|holes| = l + 1 − |A|`.
  have hIcc : ((Finset.Icc (0 : ℤ) l).card : ℤ) = l + 1 := by
    have h := Int.card_Icc_of_le (a := (0 : ℤ)) (b := l) (by omega)
    omega
  have hAsub' : A ⊆ Finset.Icc 0 l :=
    fun a ha => Finset.mem_Icc.2 ⟨hmin a ha, hmax a ha⟩
  have hholes_eq : holes = Finset.Icc 0 l \ A := by
    ext x
    simp [holes, Finset.mem_sdiff, and_comm]
  have hholes : (holes.card : ℤ) = l + 1 - A.card := by
    rw [hholes_eq]
    have hsd := Finset.card_sdiff_of_subset hAsub'
    rw [hsd, Nat.cast_sub (Finset.card_le_card hAsub'), hIcc]
  omega

end SmallDiameter

/-! ### The modular fiber bound

For `A ⊆ [0, l]` containing `0` and `l` (with `l > 0`), write `Ā` for the image
of `A ∖ {l}` in `ZMod l`.  Then `|A + A| ≥ |A| + |Ā + Ā|`.

The reason: `A ∪ (l + A) ⊆ 2A` contributes `2|A| − 1`, and every residue
class `r ∈ (Ā + Ā) ∖ Ā` is represented by an element of `2A` whose residue is
outside `Ā`, hence outside `A ∪ (l + A)`.  These elements are distinct modulo
`l`, so each contributes at least one further element. -/

section ModularBound

variable {A : Finset ℤ} {l : ℤ}

/-- Reduction mod `l` is injective on `A ∖ {l}` (all elements lie in
`[0, l)`). -/
lemma card_zmod_image_eq_card_erase {A : Finset ℤ} {l : ℤ}
    (hl : l ∈ A) (hl0 : 0 < l)
    (hmin : ∀ a ∈ A, 0 ≤ a) (hmax : ∀ a ∈ A, a ≤ l) :
    ((A.erase l).image (fun x : ℤ => (x : ZMod l.toNat))).card = A.card - 1 := by
  have h1 : (A.erase l).card = A.card - 1 := Finset.card_erase_of_mem hl
  have hinj : Set.InjOn (fun x : ℤ => (x : ZMod l.toNat)) (A.erase l) := by
    intro x hx y hy hxy
    have hxA := (Finset.mem_erase.1 hx).2
    have hyA := (Finset.mem_erase.1 hy).2
    have hx0 := hmin x hxA
    have hxl : x < l := lt_of_le_of_ne (hmax x hxA) (Finset.mem_erase.1 hx).1
    have hy0 := hmin y hyA
    have hyl : y < l := lt_of_le_of_ne (hmax y hyA) (Finset.mem_erase.1 hy).1
    have hkey : (x : ZMod l.toNat) = (y : ZMod l.toNat) := hxy
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at hkey
    obtain ⟨k, hk⟩ := hkey
    have hlt : (l.toNat : ℤ) = l := Int.toNat_of_nonneg (le_of_lt hl0)
    rw [hlt] at hk
    have hk0 : k = 0 := by
      rcases lt_trichotomy k 0 with hkc | hkc | hkc
      · have : l * k ≤ -l := by nlinarith
        omega
      · exact hkc
      · have : l * k ≥ l := by nlinarith
        omega
    rw [hk0] at hk
    omega
  rw [Finset.card_image_of_injOn hinj, h1]

/-- The residue classes attained by `A + A` outside `Ā` supply at least
`|Ā + Ā| − |Ā|` additional sumset elements. -/
theorem card_add_self_ge_card_add_zmod
    (h0 : 0 ∈ A) (hl : l ∈ A) (hl0 : 0 < l)
    (hmin : ∀ a ∈ A, 0 ≤ a) (hmax : ∀ a ∈ A, a ≤ l) :
    A.card + (((A.erase l).image (fun x : ℤ => (x : ZMod l.toNat))) +
      ((A.erase l).image (fun x : ℤ => (x : ZMod l.toNat)))).card
      ≤ (A.image₂ (· + ·) A).card := by
  classical
  set S2 := A.image₂ (· + ·) A
  set Ā := (A.erase l).image (fun x : ℤ => (x : ZMod l.toNat))
  have h0e : 0 ∈ A.erase l := Finset.mem_erase.2 ⟨ne_of_lt hl0, h0⟩
  have h0Ā : (0 : ZMod l.toNat) ∈ Ā :=
    Finset.mem_image.2 ⟨0, h0e, by simp⟩
  -- `A ∪ (l + A) ⊆ 2A`, `|A ∪ (l + A)| = 2|A| − 1`.
  have hAsub : A ⊆ S2 := fun a ha => by
    have h : a = 0 + a := by ring
    rw [h]; exact Finset.mem_image₂_of_mem h0 ha
  have hlA : A.image (l + ·) ⊆ S2 := by
    intro y hy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hy
    exact Finset.mem_image₂_of_mem hl ha
  have hinter : A ∩ A.image (l + ·) = {l} := by
    ext y
    simp only [Finset.mem_inter, Finset.mem_image, Finset.mem_singleton]
    constructor
    · rintro ⟨hyA, a, ha, rfl⟩
      have ha0 := hmin a ha
      have hay : l + a ≤ l := hmax _ hyA
      have ha0' : a = 0 := by omega
      rw [ha0']; ring
    · rintro rfl
      exact ⟨hl, ⟨0, h0, by ring⟩⟩
  have hunion_card : (A ∪ A.image (l + ·)).card = 2 * A.card - 1 := by
    have himg : (A.image (l + ·)).card = A.card :=
      Finset.card_image_of_injective _ (add_right_injective l)
    have hpos : 0 < A.card := Finset.card_pos.2 ⟨0, h0⟩
    have := Finset.card_union_add_card_inter A (A.image (l + ·))
    rw [hinter, Finset.card_singleton, himg] at this
    omega
  -- `T` = elements of `2A` whose residue class avoids `Ā`.
  set T := S2.filter (fun x : ℤ => (x : ZMod l.toNat) ∉ Ā)
  -- `T` is disjoint from `A ∪ (l + A)`.
  have hTdisj : Disjoint (A ∪ A.image (l + ·)) T := by
    rw [Finset.disjoint_right]
    intro y hyT
    have hyres : (y : ZMod l.toNat) ∉ Ā := (Finset.mem_filter.1 hyT).2
    intro hy
    rcases Finset.mem_union.1 hy with h | h
    · by_cases hyl : y = l
      · rw [hyl] at hyres
        have hle : (l : ZMod l.toNat) = 0 := by
          have e : ((l.toNat : ℤ) : ZMod l.toNat) = 0 := by
            rw [Int.cast_natCast]
            exact ZMod.natCast_self _
          rwa [Int.toNat_of_nonneg (le_of_lt hl0)] at e
        rw [hle] at hyres
        exact hyres h0Ā
      · apply hyres
        exact Finset.mem_image.2 ⟨y, Finset.mem_erase.2 ⟨hyl, h⟩, rfl⟩
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 h
      apply hyres
      have hle : (l : ZMod l.toNat) = 0 := by
        have e : ((l.toNat : ℤ) : ZMod l.toNat) = 0 := by
          rw [Int.cast_natCast]
          exact ZMod.natCast_self _
        rwa [Int.toNat_of_nonneg (le_of_lt hl0)] at e
      have hcast : ((l + a : ℤ) : ZMod l.toNat) = (a : ZMod l.toNat) := by
        rw [Int.cast_add, hle, zero_add]
      rw [hcast]
      by_cases hal : a = l
      · rwa [hal, hle]
      · exact Finset.mem_image.2 ⟨a, Finset.mem_erase.2 ⟨hal, ha⟩, rfl⟩
  -- Every residue `r ∈ Ā + Ā` outside `Ā` is hit by `T`.
  have hTcov : (Ā + Ā) \ Ā ⊆ T.image (fun x : ℤ => (x : ZMod l.toNat)) := by
    intro r hr
    obtain ⟨hrS, hrĀ⟩ := Finset.mem_sdiff.1 hr
    obtain ⟨a, haĀ, b, hbĀ, hab⟩ := Finset.mem_add.1 hrS
    obtain ⟨a', ha'e, rfl⟩ := Finset.mem_image.1 haĀ
    obtain ⟨b', hb'e, rfl⟩ := Finset.mem_image.1 hbĀ
    have hsum : (a' + b' : ℤ) ∈ T := by
      refine Finset.mem_filter.2 ⟨?_, ?_⟩
      · exact Finset.mem_image₂_of_mem
          (Finset.mem_erase.1 ha'e).2 (Finset.mem_erase.1 hb'e).2
      · rw [Int.cast_add]; rwa [hab]
    exact Finset.mem_image.2 ⟨a' + b', hsum, by rw [Int.cast_add, hab]⟩
  -- `Ā ⊆ Ā + Ā` via `0 ∈ Ā`.
  have hĀsub : Ā ⊆ Ā + Ā := by
    intro r hr
    have h : r = r + 0 := by ring
    rw [h]
    exact Finset.mem_add.2 ⟨r, hr, 0, h0Ā, rfl⟩
  -- Assemble.
  have hsub : (A ∪ A.image (l + ·)) ∪ T ⊆ S2 := by
    intro y hy
    rcases Finset.mem_union.1 hy with h | h
    · rcases Finset.mem_union.1 h with h | h
      · exact hAsub h
      · exact hlA h
    · exact (Finset.mem_filter.1 h).1
  have hcard : (A ∪ A.image (l + ·)).card + T.card ≤ S2.card := by
    have := Finset.card_le_card hsub
    rwa [Finset.card_union_of_disjoint hTdisj] at this
  have hTimage : (T.image (fun x : ℤ => (x : ZMod l.toNat))).card ≥ ((Ā + Ā) \ Ā).card :=
    Finset.card_le_card hTcov
  have hTle : T.card ≥ (T.image (fun x : ℤ => (x : ZMod l.toNat))).card :=
    Finset.card_image_le
  have hĀcard : Ā.card = A.card - 1 :=
    card_zmod_image_eq_card_erase hl hl0 hmin hmax
  have hdiff : ((Ā + Ā) \ Ā).card = (Ā + Ā).card - Ā.card :=
    Finset.card_sdiff_of_subset hĀsub
  omega

/-- **Large-diameter doubling when `l` has no small prime factor.**

If `minFac l ≥ 2|A| − 3` (in particular whenever `l` is prime), then
`|A + A| ≥ 3|A| − 3`. This follows from `card_add_self_ge_card_add_zmod`
and the Cauchy–Davenport bound `|Ā + Ā| ≥ min (minOrder) (2|Ā| − 1)` in
`ZMod l`, where `minOrder (ZMod l) = minFac l`. -/
theorem card_add_self_ge_three_mul_sub_three_of_minFac
    (h0 : 0 ∈ A) (hl : l ∈ A) (hl0 : 0 < l)
    (hmin : ∀ a ∈ A, 0 ≤ a) (hmax : ∀ a ∈ A, a ≤ l)
    (hmf : 2 * A.card - 3 ≤ l.toNat.minFac) :
    3 * A.card - 3 ≤ (A.image₂ (· + ·) A).card := by
  classical
  have hbound := card_add_self_ge_card_add_zmod h0 hl hl0 hmin hmax
  set Ā := (A.erase l).image (fun x : ℤ => (x : ZMod l.toNat))
  have hĀcard : Ā.card = A.card - 1 :=
    card_zmod_image_eq_card_erase hl hl0 hmin hmax
  have hĀne : Ā.Nonempty := by
    refine ⟨(0 : ZMod l.toNat), ?_⟩
    rw [Finset.mem_image]
    exact ⟨0, Finset.mem_erase.2 ⟨ne_of_lt hl0, h0⟩, by simp⟩
  by_cases hl1 : l = 1
  · -- `A ⊆ {0, 1}` with `0, 1 ∈ A`, so `A = {0,1}` and `2A = {0,1,2}`.
    have hA : A = {0, 1} := by
      apply Finset.eq_of_subset_of_card_le
      · intro a ha
        have h1 := hmin a ha; have h2 := hmax a ha
        simp only [Finset.mem_insert, Finset.mem_singleton]
        omega
      · have hsub : ({0, 1} : Finset ℤ) ⊆ A := by
          intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact h0
          · exact hl1 ▸ hl
        exact Finset.card_le_card hsub
    rw [hA]
    native_decide
  · have hl2 : (2 : ℤ) ≤ l := by omega
    have hn0 : l.toNat ≠ 0 := by
      have := Int.toNat_of_nonneg (le_of_lt hl0); omega
    have hn1 : l.toNat ≠ 1 := by
      have := Int.toNat_of_nonneg (le_of_lt hl0); omega
    have hcd := cauchy_davenport_minOrder_add hĀne hĀne
    -- `min (minOrder (ZMod l)) ↑(#Ā + #Ā - 1) ≤ #(Ā + Ā)`
    have hmo : AddMonoid.minOrder (ZMod l.toNat) = (l.toNat.minFac : ℕ∞) :=
      ZMod.minOrder hn0 hn1
    rw [hmo] at hcd
    have hĀpos : 0 < Ā.card := hĀne.card_pos
    have hN : (Ā.card + Ā.card - 1 : ℕ) = 2 * A.card - 3 := by omega
    rw [hN] at hcd
    -- `min ↑minFac ↑(2k-3) = ↑(2k-3)` since `2k-3 ≤ minFac`
    have hcast : ((2 * A.card - 3 : ℕ) : ℕ∞) ≤ (l.toNat.minFac : ℕ∞) := by
      exact_mod_cast hmf
    have hmin_eq : min (l.toNat.minFac : ℕ∞) ((2 * A.card - 3 : ℕ) : ℕ∞)
        = ((2 * A.card - 3 : ℕ) : ℕ∞) := min_eq_right hcast
    rw [hmin_eq] at hcd
    have hcd' : 2 * A.card - 3 ≤ (Ā + Ā).card := by exact_mod_cast hcd
    omega

end ModularBound

/-! ### Gcd normalization -/

section GcdNormalization

variable {A : Finset ℤ}

/-- **Gcd normalization.** If `A` contains a nonzero element, `A` is a
dilation `d • A'` of a set `A'` whose elements have gcd `1`, and both the
cardinality and the sumset cardinality are preserved.  This is the
normalisation step of Freiman's theorem: after translating `min A` to `0`
one divides by `gcd A`. -/
theorem exists_gcd_normalize (hne : ∃ a ∈ A, a ≠ 0) :
    ∃ d : ℤ, ∃ A' : Finset ℤ, 0 < d ∧
      A = A'.image (d * ·) ∧ A'.gcd id = 1 ∧
      A'.card = A.card ∧
      (A'.image₂ (· + ·) A').card = (A.image₂ (· + ·) A).card := by
  classical
  obtain ⟨a₀, ha₀, ha₀'⟩ := hne
  set d := A.gcd id with hd_def
  have hdvd : ∀ a ∈ A, d ∣ a := fun a ha => Finset.gcd_dvd ha
  have hd0 : d ≠ 0 := Finset.gcd_ne_zero_iff.2 ⟨a₀, ha₀, ha₀'⟩
  have hd_nonneg : 0 ≤ d := by
    rw [hd_def]
    refine Finset.induction_on A (by simp) ?_
    intro b s _ ih
    rw [Finset.gcd_insert]
    exact Int.gcd_nonneg _ _
  have hdpos : 0 < d := lt_of_le_of_ne hd_nonneg (Ne.symm hd0)
  have hdiv : ∀ a ∈ A, a = d * (a / d) := fun a ha =>
    (Int.mul_ediv_cancel' (hdvd a ha)).symm
  have hinj : Set.InjOn (· / d) A := by
    intro a ha b hb hab
    have hab' : a / d = b / d := hab
    rw [hdiv a ha, hdiv b hb, hab']
  have hAeq : A = (A.image (· / d)).image (d * ·) := by
    rw [Finset.image_image]
    calc A = A.image id := (Finset.image_id).symm
      _ = A.image (fun a => d * (a / d)) :=
          Finset.image_congr (fun a ha => hdiv a ha)
  have hgcd : (A.image (· / d)).gcd id = 1 := by
    rw [← Finset.gcd_eq_gcd_image]
    exact Finset.gcd_div_id_eq_one ha₀ ha₀'
  have hcard : (A.image (· / d)).card = A.card :=
    Finset.card_image_of_injOn hinj
  have hsum : ((A.image (· / d)).image₂ (· + ·) (A.image (· / d))).card =
      (A.image₂ (· + ·) A).card := by
    have hmap : (A.image (· / d)).image₂ (· + ·) (A.image (· / d)) =
        (A.image₂ (· + ·) A).image (· / d) := by
      ext x
      simp only [Finset.mem_image₂, Finset.mem_image]
      constructor
      · rintro ⟨a, ⟨a', ha', rfl⟩, b, ⟨b', hb', rfl⟩, rfl⟩
        refine ⟨a' + b', ⟨a', ha', b', hb', rfl⟩, ?_⟩
        obtain ⟨a'', rfl⟩ := hdvd a' ha'
        obtain ⟨b'', rfl⟩ := hdvd b' hb'
        rw [Int.mul_ediv_cancel_left _ hd0, Int.mul_ediv_cancel_left _ hd0,
          ← mul_add, Int.mul_ediv_cancel_left _ hd0]
      · rintro ⟨x', ⟨a', ha', b', hb', rfl⟩, rfl⟩
        refine ⟨a' / d, ⟨a', ha', rfl⟩, b' / d, ⟨b', hb', rfl⟩, ?_⟩
        obtain ⟨a'', rfl⟩ := hdvd a' ha'
        obtain ⟨b'', rfl⟩ := hdvd b' hb'
        rw [Int.mul_ediv_cancel_left _ hd0, Int.mul_ediv_cancel_left _ hd0,
          ← mul_add, Int.mul_ediv_cancel_left _ hd0]
    rw [hmap]
    apply Finset.card_image_of_injOn
    intro x hx y hy hxy
    obtain ⟨a₁, ha₁, b₁, hb₁, rfl⟩ := Finset.mem_image₂.1 hx
    obtain ⟨a₂, ha₂, b₂, hb₂, rfl⟩ := Finset.mem_image₂.1 hy
    have e1 : a₁ + b₁ = d * ((a₁ + b₁) / d) :=
      (Int.mul_ediv_cancel' ((hdvd a₁ ha₁).add (hdvd b₁ hb₁))).symm
    have e2 : a₂ + b₂ = d * ((a₂ + b₂) / d) :=
      (Int.mul_ediv_cancel' ((hdvd a₂ ha₂).add (hdvd b₂ hb₂))).symm
    have hxy' : (a₁ + b₁) / d = (a₂ + b₂) / d := hxy
    rw [e1, e2, hxy']
  exact ⟨d, A.image (· / d), hdpos, hAeq, hgcd, hcard, hsum⟩

end GcdNormalization

/-! ### Freiman's `3k − 4` theorem: proved cases -/

/-- **Freiman's `3k − 4` theorem** in the cases currently covered by this
file's doubling bounds.

If `|A + A| ≤ 3|A| − 4` and the diameter `l = max A − min A` satisfies either

* `l + 3 ≤ 2|A|` (the **small-diameter** case), or
* `minFac l ≥ 2|A| − 3` (e.g. `l` prime, or `l ≤ 1`),

then `A` is contained in an arithmetic progression of length at most
`|A + A| − |A| + 1`.

The remaining case `l ≥ 2|A| − 2` with `minFac l ≤ 2|A| − 4` is genuine
Freiman territory: after dividing by `gcd A` one needs the periodic-boundary
analysis of `Ā = A ∖ {l} ⊆ ZMod l` (equivalently, Kneser's theorem for the
cyclic group), which is not currently formalised here. -/
theorem freiman_3k4_of_diam_or_minFac {A : Finset ℤ} (hA : A.Nonempty)
    (h : (A.image₂ (· + ·) A).card ≤ 3 * A.card - 4)
    (hdisj : (A.max' hA - A.min' hA) + 3 ≤ 2 * A.card ∨
      2 * A.card - 3 ≤ (A.max' hA - A.min' hA).toNat.minFac) :
    ∃ d : ℤ, ∃ a : ℤ, A ⊆ Finset.image (fun i : ℕ => a + d * (i : ℤ))
      (Finset.range ((A.image₂ (· + ·) A).card - A.card + 1)) := by
  classical
  set m := A.min' hA with hm_def
  set l := A.max' hA - m with hl_def
  set A₀ := A.image (· + (-m)) with hA₀_def
  set n := (A.image₂ (· + ·) A).card - A.card + 1 with hn_def
  have hm_mem : m ∈ A := A.min'_mem hA
  have hmax_mem : A.max' hA ∈ A := A.max'_mem hA
  have hmin_le : ∀ a ∈ A, m ≤ a := fun a ha => A.min'_le a ha
  have hle_max : ∀ a ∈ A, a ≤ A.max' hA := fun a ha => A.le_max' a ha
  have hl0 : 0 ≤ l := sub_nonneg.2 (hmin_le _ hmax_mem)
  have h0 : (0 : ℤ) ∈ A₀ := by
    exact Finset.mem_image.2 ⟨m, hm_mem, by ring⟩
  have hl_mem : l ∈ A₀ := by
    exact Finset.mem_image.2 ⟨A.max' hA, hmax_mem, by ring⟩
  have hmin0 : ∀ a ∈ A₀, 0 ≤ a := by
    intro a ha
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 ha
    have := hmin_le x hx; omega
  have hmaxl : ∀ a ∈ A₀, a ≤ l := by
    intro a ha
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 ha
    have := hle_max x hx; omega
  have hcard : A₀.card = A.card := card_image_add_const A (-m)
  have hsum : (A₀.image₂ (· + ·) A₀).card = (A.image₂ (· + ·) A).card :=
    card_image₂_add_const A (-m)
  rcases hdisj with hsmall | hmf
  · -- **Small-diameter case**: `|2A₀| ≥ l + |A|`, so `l + 1 ≤ n`.
    have hdiam := card_add_self_ge_diam_add_card h0 hl_mem hmin0 hmaxl
      (hcard.symm ▸ hsmall)
    have hln : l.toNat + 1 ≤ n := by
      have hlt : (l.toNat : ℤ) = l := Int.toNat_of_nonneg hl0
      omega
    refine ⟨1, m, ?_⟩
    intro x hx
    -- `x - m ∈ A₀ ⊆ image (fun i : ℕ => (i : ℤ)) (range (l.toNat+1))`
    have hxA₀ : x + (-m) ∈ A₀ := Finset.mem_image.2 ⟨x, hx, rfl⟩
    have hxr := subset_image_progression hmin0 hmaxl hxA₀
    obtain ⟨i, hi, hieq⟩ := Finset.mem_image.1 hxr
    refine Finset.mem_image.2 ⟨i, ?_, ?_⟩
    · exact Finset.mem_range.2
        (lt_of_lt_of_le (Finset.mem_range.1 hi)
          (by exact_mod_cast hln))
    · -- `x = m + 1 * i`
      have : (i : ℤ) = x + (-m) := hieq
      have : x = m + i := by
        have h' : (i : ℤ) = x + (-m) := this
        omega
      rw [this]; ring
  · -- **Large-`minFac` case**: `|2A₀| ≥ 3|A| − 3`, contradicting the bound.
    by_cases hl_eq : l = 0
    · -- `A = {m}`: a singleton is contained in a length-1 progression.
      have hA1 : A = {m} := by
        apply Finset.eq_of_subset_of_card_le
        · intro a ha
          have h1 := hmin_le a ha; have h2 := hle_max a ha
          simp only [Finset.mem_singleton]; omega
        · have hsub : ({m} : Finset ℤ) ⊆ A := by
            intro x hx; simp only [Finset.mem_singleton] at hx
            rw [hx]; exact hm_mem
          exact Finset.card_le_card hsub
      refine ⟨1, m, ?_⟩
      intro x hx
      rw [hA1] at hx
      simp only [Finset.mem_singleton] at hx
      rw [hx]
      have hn_pos : 1 ≤ n := by
        have hne : (A.image₂ (· + ·) A).Nonempty :=
          ⟨m + m, Finset.mem_image₂_of_mem hm_mem hm_mem⟩
        have := Finset.Nonempty.card_pos hne
        have := hA.card_pos
        omega
      exact Finset.mem_image.2 ⟨0, Finset.mem_range.2 hn_pos, by ring⟩
    · have hl_pos : 0 < l := lt_of_le_of_ne hl0 (Ne.symm hl_eq)
      have hbig := card_add_self_ge_three_mul_sub_three_of_minFac
        h0 hl_mem hl_pos hmin0 hmaxl (hcard.symm ▸ hmf)
      exfalso
      have h1 := hA.card_pos
      have hne : (A.image₂ (· + ·) A).Nonempty :=
        ⟨m + m, Finset.mem_image₂_of_mem hm_mem hm_mem⟩
      have h2 := Finset.Nonempty.card_pos hne
      omega

/-! ### The difference set `A − A`

`Freiman3k4` bounds `|A − A|` rather than `|A + A|`.  Writing
`D = l − A`, we have `A + D = l + (A − A)`; the two-set version of the
hole-counting argument therefore gives `|A − A| ≥ l + |A|` whenever
`l ≤ 2|A| − 3`.  In the large-diameter regime we use the modular bound
`|A − A| ≥ |B − B| + |B ∪ (−B)| + 1` for `B = (A ∖ {l}) ⊆ ZMod l`,
which via Cauchy–Davenport suffices whenever `minFac l ≥ 2|A| − 3`.
The remaining case `l ≥ 2|A| − 2` and `minFac l ≤ 2|A| − 4` is the
periodic-boundary part of Freiman's theorem, isolated below as
`Freiman3k4Residual`. -/

section DifferenceSet

/-- If `x ∉ A + B`, then `A ∩ (−∞, x]` and `x − (B ∩ (−∞, x])` are
disjoint. -/
lemma disjoint_filter_le_image_add {A B : Finset ℤ} {x : ℤ}
    (hx : x ∉ A.image₂ (· + ·) B) :
    Disjoint (A.filter (· ≤ x)) ((B.filter (· ≤ x)).image (x - ·)) := by
  rw [Finset.disjoint_left]
  intro a ha hb
  obtain ⟨b, hblo, hab⟩ := Finset.mem_image.1 hb
  have haA := (Finset.mem_filter.1 ha).1
  have hbB := (Finset.mem_filter.1 hblo).1
  apply hx
  have h : x = a + b := by omega
  rw [h]
  exact Finset.mem_image₂_of_mem haA hbB

/-- If `x + l ∉ A + B`, then `A ∩ [x, ∞)` and `x + l − (B ∩ [x, ∞))` are
disjoint. -/
lemma disjoint_filter_ge_image_add {A B : Finset ℤ} {x l : ℤ}
    (hx : x + l ∉ A.image₂ (· + ·) B) :
    Disjoint (A.filter (x ≤ ·)) ((B.filter (x ≤ ·)).image (x + l - ·)) := by
  rw [Finset.disjoint_left]
  intro a ha hb
  obtain ⟨b, hbhi, hab⟩ := Finset.mem_image.1 hb
  have haA := (Finset.mem_filter.1 ha).1
  have hbB := (Finset.mem_filter.1 hbhi).1
  apply hx
  have h : x + l = a + b := by omega
  rw [h]
  exact Finset.mem_image₂_of_mem haA hbB

/-- Low-side doubling: `|A ∩ (−∞, x]| + |B ∩ (−∞, x]| ≤ |[0, x]|` when
`x ∉ A + B`. -/
lemma card_filter_le_add_card_filter_le {A B : Finset ℤ} {x : ℤ}
    (hminA : ∀ a ∈ A, 0 ≤ a) (hminB : ∀ b ∈ B, 0 ≤ b)
    (hx : x ∉ A.image₂ (· + ·) B) :
    (A.filter (· ≤ x)).card + (B.filter (· ≤ x)).card ≤
      (Finset.Icc 0 x).card := by
  classical
  set loA := A.filter (· ≤ x)
  set loB := B.filter (· ≤ x)
  have hsub : loA ∪ loB.image (x - ·) ⊆ Finset.Icc 0 x := by
    intro y hy
    rcases Finset.mem_union.1 hy with h | h
    · have hAy := (Finset.mem_filter.1 h).1
      have hyx := (Finset.mem_filter.1 h).2
      exact Finset.mem_Icc.2 ⟨hminA y hAy, hyx⟩
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 h
      have haB := (Finset.mem_filter.1 ha).1
      have hax := (Finset.mem_filter.1 ha).2
      have ha0 := hminB a haB
      exact Finset.mem_Icc.2 ⟨by omega, by omega⟩
  have hcard : (loB.image (x - ·)).card = loB.card :=
    Finset.card_image_of_injective _ (fun a b h => by omega)
  have hunion : (loA ∪ loB.image (x - ·)).card = loA.card + loB.card := by
    rw [Finset.card_union_of_disjoint (disjoint_filter_le_image_add hx), hcard]
  calc loA.card + loB.card = (loA ∪ loB.image (x - ·)).card := hunion.symm
    _ ≤ (Finset.Icc 0 x).card := Finset.card_le_card hsub

/-- High-side doubling: `|A ∩ [x, ∞)| + |B ∩ [x, ∞)| ≤ |[x, l]|` when
`x + l ∉ A + B`. -/
lemma card_filter_ge_add_card_filter_ge {A B : Finset ℤ} {x l : ℤ}
    (hmaxA : ∀ a ∈ A, a ≤ l) (hmaxB : ∀ b ∈ B, b ≤ l)
    (hx : x + l ∉ A.image₂ (· + ·) B) :
    (A.filter (x ≤ ·)).card + (B.filter (x ≤ ·)).card ≤
      (Finset.Icc x l).card := by
  classical
  set hiA := A.filter (x ≤ ·)
  set hiB := B.filter (x ≤ ·)
  have hsub : hiA ∪ hiB.image (x + l - ·) ⊆ Finset.Icc x l := by
    intro y hy
    rcases Finset.mem_union.1 hy with h | h
    · have hAy := (Finset.mem_filter.1 h).1
      have hxy := (Finset.mem_filter.1 h).2
      exact Finset.mem_Icc.2 ⟨hxy, hmaxA y hAy⟩
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 h
      have haB := (Finset.mem_filter.1 ha).1
      have hxa := (Finset.mem_filter.1 ha).2
      have hal := hmaxB a haB
      exact Finset.mem_Icc.2 ⟨by omega, by omega⟩
  have hcard : (hiB.image (x + l - ·)).card = hiB.card :=
    Finset.card_image_of_injective _ (fun a b h => by omega)
  have hunion : (hiA ∪ hiB.image (x + l - ·)).card = hiA.card + hiB.card := by
    rw [Finset.card_union_of_disjoint (disjoint_filter_ge_image_add hx), hcard]
  calc hiA.card + hiB.card = (hiA ∪ hiB.image (x + l - ·)).card := hunion.symm
    _ ≤ (Finset.Icc x l).card := Finset.card_le_card hsub

/-- **Uncovered holes force `|A| + |B| ≤ l + 2`.**  If `x ∈ [0, l]` satisfies
`x ∉ A + B` and `x + l ∉ A + B`, then `|A| + |B| ≤ l + 2`. -/
lemma card_add_card_le_of_uncovered {A B : Finset ℤ} {x l : ℤ}
    (hminA : ∀ a ∈ A, 0 ≤ a) (hmaxA : ∀ a ∈ A, a ≤ l)
    (hminB : ∀ b ∈ B, 0 ≤ b) (hmaxB : ∀ b ∈ B, b ≤ l)
    (hx0 : 0 ≤ x) (hxl : x ≤ l)
    (hx : x ∉ A.image₂ (· + ·) B) (hxl' : x + l ∉ A.image₂ (· + ·) B) :
    A.card + B.card ≤ l + 2 := by
  classical
  have hlo := card_filter_le_add_card_filter_le hminA hminB hx
  have hhi := card_filter_ge_add_card_filter_ge hmaxA hmaxB hxl'
  have hcoverA : A ⊆ A.filter (· ≤ x) ∪ A.filter (x ≤ ·) := by
    intro a ha
    rcases le_total a x with h | h
    · exact Finset.mem_union.2 (Or.inl (Finset.mem_filter.2 ⟨ha, h⟩))
    · exact Finset.mem_union.2 (Or.inr (Finset.mem_filter.2 ⟨ha, h⟩))
  have hcoverB : B ⊆ B.filter (· ≤ x) ∪ B.filter (x ≤ ·) := by
    intro b hb
    rcases le_total b x with h | h
    · exact Finset.mem_union.2 (Or.inl (Finset.mem_filter.2 ⟨hb, h⟩))
    · exact Finset.mem_union.2 (Or.inr (Finset.mem_filter.2 ⟨hb, h⟩))
  have hAc : A.card ≤ (A.filter (· ≤ x)).card + (A.filter (x ≤ ·)).card :=
    (Finset.card_le_card hcoverA).trans (Finset.card_union_le _ _)
  have hBc : B.card ≤ (B.filter (· ≤ x)).card + (B.filter (x ≤ ·)).card :=
    (Finset.card_le_card hcoverB).trans (Finset.card_union_le _ _)
  have hIcc0 : ((Finset.Icc (0 : ℤ) x).card : ℤ) = x + 1 := by
    have h := Int.card_Icc_of_le (a := (0 : ℤ)) (b := x) (by omega)
    omega
  have hIccx : ((Finset.Icc x l).card : ℤ) = l - x + 1 := by
    have h := Int.card_Icc_of_le (a := x) (b := l) (by omega)
    omega
  have hlo' : ((A.filter (· ≤ x)).card + (B.filter (· ≤ x)).card : ℤ) ≤
      x + 1 := by
    calc ((A.filter (· ≤ x)).card + (B.filter (· ≤ x)).card : ℤ)
        ≤ ((Finset.Icc 0 x).card : ℤ) := by exact_mod_cast hlo
      _ = x + 1 := hIcc0
  have hhi' : ((A.filter (x ≤ ·)).card + (B.filter (x ≤ ·)).card : ℤ) ≤
      l - x + 1 := by
    calc ((A.filter (x ≤ ·)).card + (B.filter (x ≤ ·)).card : ℤ)
        ≤ ((Finset.Icc x l).card : ℤ) := by exact_mod_cast hhi
      _ = l - x + 1 := hIccx
  have hAc' : (A.card : ℤ) ≤
      (A.filter (· ≤ x)).card + (A.filter (x ≤ ·)).card := by
    exact_mod_cast hAc
  have hBc' : (B.card : ℤ) ≤
      (B.filter (· ≤ x)).card + (B.filter (x ≤ ·)).card := by
    exact_mod_cast hBc
  omega

/-- **Small-diameter two-set bound.**  For `A, B ⊆ [0, l]` with `0 ∈ A`,
`0 ∈ B`, `l ∈ A` and `l + 3 ≤ |A| + |B|`, one has `|A + B| ≥ l + |B|`. -/
theorem card_add_ge_diam_add_card {A B : Finset ℤ} {l : ℤ}
    (h0A : 0 ∈ A) (hlA : l ∈ A) (h0B : 0 ∈ B)
    (hminA : ∀ a ∈ A, 0 ≤ a) (hmaxA : ∀ a ∈ A, a ≤ l)
    (hminB : ∀ b ∈ B, 0 ≤ b) (hmaxB : ∀ b ∈ B, b ≤ l)
    (hk : l + 3 ≤ A.card + B.card) :
    l + B.card ≤ (A.image₂ (· + ·) B).card := by
  classical
  set S := A.image₂ (· + ·) B with hSdef
  have hl0 : 0 ≤ l := hminA l hlA
  have hAsub : A ⊆ S := fun a ha => by
    have h : a = a + 0 := by ring
    rw [h]; exact Finset.mem_image₂_of_mem ha h0B
  have hBsub : B ⊆ S := fun b hb => by
    have h : b = 0 + b := by ring
    rw [h]; exact Finset.mem_image₂_of_mem h0A hb
  have hlB : B.image (l + ·) ⊆ S := by
    intro y hy
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hy
    exact Finset.mem_image₂_of_mem hlA hb
  -- `A ∩ (l + B) = {l}`.
  have hinter : A ∩ B.image (l + ·) = {l} := by
    ext y
    simp only [Finset.mem_inter, Finset.mem_image, Finset.mem_singleton]
    constructor
    · rintro ⟨hyA, b, hb, rfl⟩
      have hb0 := hminB b hb
      have hay : l + b ≤ l := hmaxA _ hyA
      have hb0' : b = 0 := by omega
      rw [hb0']; ring
    · rintro rfl
      exact ⟨hlA, ⟨0, h0B, by ring⟩⟩
  -- `|A ∪ (l + B)| = |A| + |B| − 1`.
  have hunion_card : (A ∪ B.image (l + ·)).card = A.card + B.card - 1 := by
    have himg : (B.image (l + ·)).card = B.card :=
      Finset.card_image_of_injective _ (add_right_injective l)
    have hpos : 0 < B.card := Finset.card_pos.2 ⟨0, h0B⟩
    have := Finset.card_union_add_card_inter A (B.image (l + ·))
    rw [hinter, Finset.card_singleton, himg] at this
    omega
  -- Every hole `x ∈ [0, l] \ A` is covered: `x ∈ A + B` or `x + l ∈ A + B`.
  set holes := (Finset.Icc 0 l).filter (· ∉ A) with holesdef
  have hhole : ∀ x ∈ holes, x ∈ S ∨ x + l ∈ S := by
    intro x hx
    have hxI := Finset.mem_Icc.1 (Finset.mem_filter.1 hx).1
    by_contra h
    push Not at h
    have := card_add_card_le_of_uncovered hminA hmaxA hminB hmaxB
      hxI.1 hxI.2 h.1 h.2
    omega
  -- The map `x ↦ if x ∈ A + B then x else x + l` sends holes injectively
  -- into `(A + B) \ (A ∪ l + B)`.
  have hf_mem : ∀ x ∈ holes,
      (if x ∈ S then x else x + l) ∈ S \ (A ∪ B.image (l + ·)) := by
    intro x hx
    have hxI := Finset.mem_Icc.1 (Finset.mem_filter.1 hx).1
    have hxA := (Finset.mem_filter.1 hx).2
    by_cases hxs : x ∈ S
    · rw [ite_eq_left hxs]
      simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_image, not_or,
        not_exists]
      refine ⟨hxs, hxA, fun b hb => ?_⟩
      have hb0 := hminB b hb.1
      have hbeq := hb.2
      have hxl : x = l := by omega
      exact hxA (hxl ▸ hlA)
    · rw [ite_eq_right hxs]
      have hxl2 : x + l ∈ S := (hhole x hx).resolve_left hxs
      simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_image, not_or,
        not_exists]
      refine ⟨hxl2, fun hA' => ?_, fun b hb => ?_⟩
      · have hxl' := hmaxA _ hA'
        have hxpos : x ≠ 0 := fun e => hxA (e ▸ h0A)
        omega
      · have hbeq := hb.2
        have hxb : b = x := by omega
        exact hxs (hxb ▸ hBsub hb.1)
  have hf_inj : ∀ x ∈ holes, ∀ y ∈ holes,
      (if x ∈ S then x else x + l) = (if y ∈ S then y else y + l) → x = y := by
    intro x hx y hy hxy
    have hxI := Finset.mem_Icc.1 (Finset.mem_filter.1 hx).1
    have hyI := Finset.mem_Icc.1 (Finset.mem_filter.1 hy).1
    have hxA := (Finset.mem_filter.1 hx).2
    have hyA := (Finset.mem_filter.1 hy).2
    have hx0 : x ≠ 0 := fun e => hxA (e ▸ h0A)
    have hxl : x ≠ l := fun e => hxA (e ▸ hlA)
    have hy0 : y ≠ 0 := fun e => hyA (e ▸ h0A)
    have hyl : y ≠ l := fun e => hyA (e ▸ hlA)
    by_cases hxs : x ∈ S <;> by_cases hys : y ∈ S <;>
      simp only [hxs, hys, ite_true, ite_false] at hxy <;> omega
  -- `|A + B| ≥ |A ∪ (l + B)| + |holes|`.
  have hsub : (A ∪ B.image (l + ·)) ∪
      holes.image (fun x => if x ∈ S then x else x + l) ⊆ S := by
    intro y hy
    rcases Finset.mem_union.1 hy with h | h
    · rcases Finset.mem_union.1 h with h | h
      · exact hAsub h
      · exact hlB h
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 h
      exact (Finset.mem_sdiff.1 (hf_mem x hx)).1
  have hdisj : Disjoint (A ∪ B.image (l + ·))
      (holes.image (fun x => if x ∈ S then x else x + l)) := by
    rw [Finset.disjoint_left]
    intro y hy1 hy2
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy2
    exact (Finset.mem_sdiff.1 (hf_mem x hx)).2 hy1
  have himg_card : (holes.image (fun x => if x ∈ S then x else x + l)).card =
      holes.card :=
    Finset.card_image_of_injOn
      (fun x hx y hy hxy =>
        hf_inj x (Finset.mem_coe.1 hx) y (Finset.mem_coe.1 hy) hxy)
  have hcard : (A ∪ B.image (l + ·)).card + holes.card ≤ S.card := by
    have := Finset.card_le_card hsub
    rwa [Finset.card_union_of_disjoint hdisj, himg_card] at this
  -- `|holes| = l + 1 − |A|`.
  have hIcc : ((Finset.Icc (0 : ℤ) l).card : ℤ) = l + 1 := by
    have h := Int.card_Icc_of_le (a := (0 : ℤ)) (b := l) (by omega)
    omega
  have hAsub' : A ⊆ Finset.Icc 0 l :=
    fun a ha => Finset.mem_Icc.2 ⟨hminA a ha, hmaxA a ha⟩
  have hholes : (holes.card : ℤ) = l + 1 - A.card := by
    have hsd : holes = Finset.Icc 0 l \ A := by
      rw [holesdef]
      ext x
      simp [Finset.mem_sdiff, Finset.mem_filter]
    rw [hsd, Finset.card_sdiff_of_subset hAsub',
      Nat.cast_sub (Finset.card_le_card hAsub'), hIcc]
  omega

/-- **Small-diameter bound for the difference set.**  For `A ⊆ [0, l]`
containing `0` and `l` with `l + 3 ≤ 2|A|`, one has `|A − A| ≥ l + |A|`.

Applied to `B = l − A`: `A + B = l + (A − A)`. -/
theorem card_sub_self_ge_diam_add_card {A : Finset ℤ} {l : ℤ}
    (h0 : 0 ∈ A) (hl : l ∈ A)
    (hmin : ∀ a ∈ A, 0 ≤ a) (hmax : ∀ a ∈ A, a ≤ l)
    (hk : l + 3 ≤ 2 * A.card) :
    l + A.card ≤ (A.image₂ (· - ·) A).card := by
  classical
  set B := A.image (l - ·) with hBdef
  have hBcard : B.card = A.card :=
    Finset.card_image_of_injective _ (fun a b h => by omega)
  have h0B : (0 : ℤ) ∈ B := Finset.mem_image.2 ⟨l, hl, by ring⟩
  have hminB : ∀ b ∈ B, 0 ≤ b := by
    intro b hb
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hb
    have := hmax a ha; omega
  have hmaxB : ∀ b ∈ B, b ≤ l := by
    intro b hb
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hb
    have := hmin a ha; omega
  have hsum : A.image₂ (· + ·) B = (A.image₂ (· - ·) A).image (l + ·) := by
    ext x
    simp only [hBdef, Finset.mem_image₂, Finset.mem_image]
    constructor
    · rintro ⟨a, ha, b, ⟨a', ha', rfl⟩, rfl⟩
      exact ⟨a - a', ⟨a, ha, a', ha', rfl⟩, by ring⟩
    · rintro ⟨x', ⟨a, ha, a', ha', rfl⟩, rfl⟩
      exact ⟨a, ha, l - a', ⟨a', ha', rfl⟩, by ring⟩
  have hcard : (A.image₂ (· + ·) B).card = (A.image₂ (· - ·) A).card := by
    rw [hsum]
    exact Finset.card_image_of_injective _ (add_right_injective l)
  have hbig := card_add_ge_diam_add_card h0 hl h0B hmin hmax hminB hmaxB
    (by rw [hBcard]; omega)
  rwa [hcard, hBcard] at hbig

/-- The trivial bound `2|A| − 1 ≤ |A − A|` (ordered Cauchy–Davenport applied
to `A` and `−A`). -/
theorem card_sub_self_ge {A : Finset ℤ} (hA : A.Nonempty) :
    2 * A.card - 1 ≤ (A.image₂ (· - ·) A).card := by
  classical
  set B := A.image (fun a : ℤ => -a) with hBdef
  have hBne : B.Nonempty := hA.image _
  have hBcard : B.card = A.card :=
    Finset.card_image_of_injective _ (fun a b h => by omega)
  have hsum : A.image₂ (· + ·) B = A.image₂ (· - ·) A := by
    ext x
    simp only [hBdef, Finset.mem_image₂, Finset.mem_image]
    constructor
    · rintro ⟨a, ha, b, ⟨a', ha', rfl⟩, rfl⟩
      exact ⟨a, ha, a', ha', by ring⟩
    · rintro ⟨a, ha, a', ha', rfl⟩
      exact ⟨a, ha, -a', ⟨a', ha', rfl⟩, by ring⟩
  have h := cauchy_davenport_add_of_linearOrder_isCancelAdd hA hBne
  have h2 : A + B = A.image₂ (· + ·) B := rfl
  rw [h2, hsum, hBcard] at h
  omega

/-- The image of `A ∖ {l}` in `ZMod l` (`l > 0`): the "modular shadow" of `A`
in which the two elements `0` and `l` collapse to a single residue. -/
def modIm (A : Finset ℤ) (l : ℤ) : Finset (ZMod l.toNat) :=
  (A.erase l).image (fun x : ℤ => (x : ZMod l.toNat))

/-- **Modular fiber bound for the difference set.**  For `A ⊆ [0, l]`
containing `0` and `l` with `l > 0`, writing `B` for the image of `A ∖ {l}`
in `ZMod l`, one has

  `|A − A| ≥ |B − B| + |B ∪ (−B)| + 1`.

Indeed `A − A ⊆ [−l, l]`, and the fibre of `A − A` above a nonzero class
`c` of `B − B` has size `1` or `2` according to whether the difference `c`
is realised in only one direction (`a − a' ≡ c` or `≡ c − l`) or in both.
The class `0` has the three realisations `−l, 0, l`.  Every class of `B`
(resp. `−B`) is realised in both directions, since `a` and `l + a`
(resp. `l − a` and `2l − a`) both lie in `A + (l − A)`. -/
theorem card_sub_self_ge_zmod {A : Finset ℤ} {l : ℤ}
    (h0 : 0 ∈ A) (hl : l ∈ A) (hl0 : 0 < l)
    (hmin : ∀ a ∈ A, 0 ≤ a) (hmax : ∀ a ∈ A, a ≤ l) :
    ((modIm A l).image₂ (· - ·) (modIm A l)).card +
      (modIm A l ∪ (modIm A l).image (fun x => -x)).card + 1 ≤
      (A.image₂ (· - ·) A).card := by
  classical
  set B := modIm A l with hBdef
  set π : ℤ → ZMod l.toNat := fun x : ℤ => (x : ZMod l.toNat) with hπdef
  set D := A.image (l - ·) with hDdef
  set S := A.image₂ (· + ·) D with hSdef
  set L := S.filter (· ≤ l) with hLdef
  set H := S.filter (l < ·) with hHdef
  set U := L.image π with hUdef
  set V := H.image π with hVdef
  have hcastl : ((l : ℤ) : ZMod l.toNat) = 0 := by
    have e : ((l.toNat : ℤ) : ZMod l.toNat) = 0 := by
      rw [Int.cast_natCast]; exact ZMod.natCast_self _
    rwa [Int.toNat_of_nonneg (le_of_lt hl0)] at e
  have h0D : (0 : ℤ) ∈ D := Finset.mem_image.2 ⟨l, hl, by ring⟩
  have hlD : l ∈ D := Finset.mem_image.2 ⟨0, h0, by ring⟩
  have hminD : ∀ d ∈ D, 0 ≤ d := by
    intro d hd
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hd
    have := hmax a ha; omega
  have hmaxD : ∀ d ∈ D, d ≤ l := by
    intro d hd
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hd
    have := hmin a ha; omega
  have hSbound : ∀ x ∈ S, 0 ≤ x ∧ x ≤ 2 * l := by
    intro x hx
    rw [hSdef] at hx
    obtain ⟨a, ha, d, hd, rfl⟩ := Finset.mem_image₂.1 hx
    constructor
    · have h1 := hmin a ha; have h2 := hminD d hd; omega
    · have h1 := hmax a ha; have h2 := hmaxD d hd; omega
  -- `S = l + (A − A)`.
  have hSeq : S = (A.image₂ (· - ·) A).image (l + ·) := by
    rw [hSdef]
    ext x
    simp only [hDdef, Finset.mem_image₂, Finset.mem_image]
    constructor
    · rintro ⟨a, ha, b, ⟨a', ha', rfl⟩, rfl⟩
      exact ⟨a - a', ⟨a, ha, a', ha', rfl⟩, by ring⟩
    · rintro ⟨x', ⟨a, ha, a', ha', rfl⟩, rfl⟩
      exact ⟨a, ha, l - a', ⟨a', ha', rfl⟩, by ring⟩
  have hScard : S.card = (A.image₂ (· - ·) A).card := by
    rw [hSeq]
    exact Finset.card_image_of_injective _ (add_right_injective l)
  -- `0, l ∈ L` and `2l ∈ H`.
  have h0S : (0 : ℤ) ∈ S := by
    have h : (0 : ℤ) + 0 ∈ S := Finset.mem_image₂_of_mem h0 h0D
    rwa [add_zero] at h
  have hlS : l ∈ S := by
    have h : l + 0 ∈ S := Finset.mem_image₂_of_mem hl h0D
    rwa [add_zero] at h
  have h0L : (0 : ℤ) ∈ L := Finset.mem_filter.2 ⟨h0S, le_of_lt hl0⟩
  have hlL : l ∈ L := Finset.mem_filter.2 ⟨hlS, le_rfl⟩
  have h2lS : 2 * l ∈ S := by
    have h : l + l ∈ S := Finset.mem_image₂_of_mem hl hlD
    rwa [← two_mul] at h
  have h2lH : 2 * l ∈ H := Finset.mem_filter.2 ⟨h2lS, by omega⟩
  -- `π` is injective on `L.erase l ⊆ [0, l)`.
  have hinj : Set.InjOn π (L.erase l) := by
    intro x hx y hy hxy
    rw [hLdef] at hx hy
    have hxL := (Finset.mem_erase.1 hx).2
    have hyL := (Finset.mem_erase.1 hy).2
    have hxS := (Finset.mem_filter.1 hxL).1
    have hyS := (Finset.mem_filter.1 hyL).1
    obtain ⟨hx0, hx2⟩ := hSbound x hxS
    obtain ⟨hy0, hy2⟩ := hSbound y hyS
    have hxlt : x < l := lt_of_le_of_ne
      ((Finset.mem_filter.1 hxL).2) (Finset.mem_erase.1 hx).1
    have hylt : y < l := lt_of_le_of_ne
      ((Finset.mem_filter.1 hyL).2) (Finset.mem_erase.1 hy).1
    have hkey : (x : ZMod l.toNat) = (y : ZMod l.toNat) := hxy
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at hkey
    obtain ⟨k, hk⟩ := hkey
    rw [Int.toNat_of_nonneg (le_of_lt hl0)] at hk
    have hk0 : k = 0 := by
      rcases lt_trichotomy k 0 with hkc | hkc | hkc
      · have : l * k ≤ -l := by nlinarith
        omega
      · exact hkc
      · have : l * k ≥ l := by nlinarith
        omega
    rw [hk0] at hk
    omega
  -- `π(L) = π(L.erase l)`, since `π(l) = 0 = π(0)` and `0 ∈ L.erase l`.
  have hLπ : L.image π = (L.erase l).image π := by
    ext r
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨x, hx, rfl⟩
      by_cases hxl : x = l
      · refine ⟨0, Finset.mem_erase.2 ⟨ne_of_lt hl0, h0L⟩, ?_⟩
        rw [hxl]
        show ((0 : ℤ) : ZMod l.toNat) = ((l : ℤ) : ZMod l.toNat)
        rw [hcastl]
        simp
      · exact ⟨x, Finset.mem_erase.2 ⟨hxl, hx⟩, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, (Finset.mem_erase.1 hx).2, rfl⟩
  have hUcard : U.card = L.card - 1 := by
    rw [hUdef, hLπ, Finset.card_image_of_injOn hinj,
      Finset.card_erase_of_mem hlL]
  -- Residues of `A` modulo `l` lie in `B`.
  have hcastB : ∀ a ∈ A, (a : ZMod l.toNat) ∈ B := by
    intro a ha
    by_cases hal : a = l
    · subst hal
      rw [hcastl]
      refine Finset.mem_image.2 ⟨0, ?_, by simp⟩
      exact Finset.mem_erase.2 ⟨ne_of_lt hl0, h0⟩
    · exact Finset.mem_image.2 ⟨a, Finset.mem_erase.2 ⟨hal, ha⟩, rfl⟩
  -- The covering `U ∪ V = B − B`.
  have hUS : U ∪ V = B.image₂ (· - ·) B := by
    rw [hUdef, hVdef]
    ext r
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_image₂]
    constructor
    · rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩)
      · -- `x ∈ L ⊆ S`: `x = a + (l − a')`, `π x = ↑a − ↑a'`.
        rw [hLdef] at hx
        have hxS := (Finset.mem_filter.1 hx).1
        rw [hSdef] at hxS
        obtain ⟨a, ha, d, hd, rfl⟩ := Finset.mem_image₂.1 hxS
        obtain ⟨a', ha', rfl⟩ := Finset.mem_image.1 hd
        refine ⟨(a : ZMod l.toNat), hcastB a ha,
          (a' : ZMod l.toNat), hcastB a' ha', ?_⟩
        show (a : ZMod l.toNat) - (a' : ZMod l.toNat) =
          ((a + (l - a') : ℤ) : ZMod l.toNat)
        rw [Int.cast_add, Int.cast_sub, hcastl]
        ring
      · rw [hHdef] at hx
        have hxS := (Finset.mem_filter.1 hx).1
        rw [hSdef] at hxS
        obtain ⟨a, ha, d, hd, rfl⟩ := Finset.mem_image₂.1 hxS
        obtain ⟨a', ha', rfl⟩ := Finset.mem_image.1 hd
        refine ⟨(a : ZMod l.toNat), hcastB a ha,
          (a' : ZMod l.toNat), hcastB a' ha', ?_⟩
        show (a : ZMod l.toNat) - (a' : ZMod l.toNat) =
          ((a + (l - a') : ℤ) : ZMod l.toNat)
        rw [Int.cast_add, Int.cast_sub, hcastl]
        ring
    · rintro ⟨b₁, hb₁, b₂, hb₂, rfl⟩
      rw [hBdef] at hb₁ hb₂
      obtain ⟨a₁, ha₁, rfl⟩ := Finset.mem_image.1 hb₁
      obtain ⟨a₂, ha₂, rfl⟩ := Finset.mem_image.1 hb₂
      have ha₁A := (Finset.mem_erase.1 ha₁).2
      have ha₂A := (Finset.mem_erase.1 ha₂).2
      -- `x = a₁ + (l − a₂) ∈ S` has residue `↑a₁ − ↑a₂`.
      have hxS : a₁ + (l - a₂) ∈ S := by
        rw [hSdef]
        exact Finset.mem_image₂_of_mem ha₁A
          (Finset.mem_image.2 ⟨a₂, ha₂A, rfl⟩)
      have hres : π (a₁ + (l - a₂)) =
          (a₁ : ZMod l.toNat) - (a₂ : ZMod l.toNat) := by
        show ((a₁ + (l - a₂) : ℤ) : ZMod l.toNat) = _
        rw [Int.cast_add, Int.cast_sub, hcastl]
        ring
      rcases le_or_gt (a₁ + (l - a₂)) l with hle | hlt
      · exact Or.inl ⟨a₁ + (l - a₂),
          Finset.mem_filter.2 ⟨hxS, hle⟩, hres⟩
      · exact Or.inr ⟨a₁ + (l - a₂),
          Finset.mem_filter.2 ⟨hxS, hlt⟩, hres⟩
  -- `B ∪ (−B) ⊆ U ∩ V`.
  have hBUV : B ∪ B.image (fun x => -x) ⊆ U ∩ V := by
    intro r hr
    rcases Finset.mem_union.1 hr with hrb | hrb
    · -- `r = ↑a`, `a ∈ A.erase l`: realised by `a ∈ L` and `a + l ∈ H`.
      rw [hBdef] at hrb
      obtain ⟨a, hae, rfl⟩ := Finset.mem_image.1 hrb
      have haA := (Finset.mem_erase.1 hae).2
      have hane := (Finset.mem_erase.1 hae).1
      have ha0 := hmin a haA
      have hal := hmax a haA
      have halt : a < l := lt_of_le_of_ne hal hane
      refine Finset.mem_inter.2 ⟨?_, ?_⟩
      · rw [hUdef]
        have haS : a ∈ S := by
          have h : a + 0 ∈ S := Finset.mem_image₂_of_mem haA h0D
          rwa [add_zero] at h
        exact Finset.mem_image.2 ⟨a, Finset.mem_filter.2 ⟨haS, hal⟩, rfl⟩
      · rw [hVdef]
        rcases eq_or_ne a 0 with ha0eq | ha0eq
        · subst ha0eq
          refine Finset.mem_image.2 ⟨2 * l, h2lH, ?_⟩
          show ((2 * l : ℤ) : ZMod l.toNat) = ((0 : ℤ) : ZMod l.toNat)
          rw [show (2 * l : ℤ) = l + l by ring, Int.cast_add, hcastl,
            add_zero]
          simp
        · refine Finset.mem_image.2 ⟨a + l, ?_, ?_⟩
          · exact Finset.mem_filter.2 ⟨
              Finset.mem_image₂_of_mem haA hlD, by omega⟩
          · show ((a + l : ℤ) : ZMod l.toNat) = ((a : ℤ) : ZMod l.toNat)
            rw [Int.cast_add, hcastl, add_zero]
    · -- `r ∈ −B`: `r = −↑a` realised by `l − a ∈ L` and `2l − a ∈ H`.
      obtain ⟨c, hcB, rfl⟩ := Finset.mem_image.1 hrb
      rw [hBdef] at hcB
      obtain ⟨a, hae, rfl⟩ := Finset.mem_image.1 hcB
      have haA := (Finset.mem_erase.1 hae).2
      have hane := (Finset.mem_erase.1 hae).1
      have ha0 := hmin a haA
      have hal := hmax a haA
      have halt : a < l := lt_of_le_of_ne hal hane
      have hdS : l - a ∈ S := by
        have h : 0 + (l - a) ∈ S := Finset.mem_image₂_of_mem h0
          (Finset.mem_image.2 ⟨a, haA, rfl⟩ : l - a ∈ D)
        rwa [zero_add] at h
      have hdL : l - a ∈ L := Finset.mem_filter.2 ⟨hdS, by omega⟩
      refine Finset.mem_inter.2 ⟨?_, ?_⟩
      · rw [hUdef]
        refine Finset.mem_image.2 ⟨l - a, hdL, ?_⟩
        show ((l - a : ℤ) : ZMod l.toNat) = -((a : ℤ) : ZMod l.toNat)
        rw [Int.cast_sub, hcastl, zero_sub]
      · rw [hVdef]
        refine Finset.mem_image.2 ⟨2 * l - a, ?_, ?_⟩
        · refine Finset.mem_filter.2 ⟨?_, ?_⟩
          · have h : l + (l - a) ∈ S := Finset.mem_image₂_of_mem hl
              (Finset.mem_image.2 ⟨a, haA, rfl⟩ : l - a ∈ D)
            rwa [show l + (l - a) = 2 * l - a by ring] at h
          · omega
        · show ((2 * l - a : ℤ) : ZMod l.toNat) =
            -((a : ℤ) : ZMod l.toNat)
          rw [show (2 * l - a : ℤ) = l + (l - a) by ring, Int.cast_add,
            hcastl, zero_add, Int.cast_sub, hcastl, zero_sub]
  -- Assemble: `|S| = |L| + |H| ≥ (|U| + 1) + |V| ≥ |U ∪ V| + |U ∩ V| + 1`.
  have hcardLH : L.card + H.card = S.card := by
    have hunion : L ∪ H = S := by
      rw [hLdef, hHdef]
      ext x
      simp only [Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
      · intro hx
        rcases le_or_gt x l with h | h
        · exact Or.inl ⟨hx, h⟩
        · exact Or.inr ⟨hx, h⟩
    have hdisj : Disjoint L H := by
      rw [hLdef, hHdef, Finset.disjoint_left]
      intro x hx hy
      exact absurd ((Finset.mem_filter.1 hx).2)
        (not_le.2 (Finset.mem_filter.1 hy).2)
    rw [← hunion]
    exact (Finset.card_union_of_disjoint hdisj).symm
  have hVle : V.card ≤ H.card := Finset.card_image_le
  have hUVcard : (U ∪ V).card + (U ∩ V).card = U.card + V.card :=
    Finset.card_union_add_card_inter U V
  have hUV' : (U ∪ V).card = (B.image₂ (· - ·) B).card := by rw [hUS]
  have hUV'' : (B ∪ B.image (fun x => -x)).card ≤ (U ∩ V).card :=
    Finset.card_le_card hBUV
  have hLpos : 0 < L.card := Finset.card_pos.2 ⟨0, h0L⟩
  omega

/-- **Large-diameter bound when `l` has no small prime factor**, difference
version.  If `minFac l ≥ 2|A| − 3` then `|A − A| ≥ 3|A| − 3`: the
Cauchy–Davenport bound gives `|B − B| ≥ 2|A| − 3` for the modular shadow
`B`, while `|B ∪ (−B)| ≥ |B| = |A| − 1`, and `card_sub_self_ge_zmod`
assembles. -/
theorem card_sub_self_ge_three_mul_sub_three_of_minFac
    {A : Finset ℤ} {l : ℤ}
    (h0 : 0 ∈ A) (hl : l ∈ A) (hl0 : 0 < l)
    (hmin : ∀ a ∈ A, 0 ≤ a) (hmax : ∀ a ∈ A, a ≤ l)
    (hmf : 2 * A.card - 3 ≤ l.toNat.minFac) :
    3 * A.card - 3 ≤ (A.image₂ (· - ·) A).card := by
  classical
  set B := modIm A l with hBdef
  have hbound : (B.image₂ (· - ·) B).card +
      (B ∪ B.image (fun x => -x)).card + 1 ≤
      (A.image₂ (· - ·) A).card :=
    card_sub_self_ge_zmod h0 hl hl0 hmin hmax
  have hBcard : B.card = A.card - 1 :=
    card_zmod_image_eq_card_erase hl hl0 hmin hmax
  have hBne : B.Nonempty := by
    refine ⟨(0 : ZMod l.toNat), ?_⟩
    refine Finset.mem_image.2 ⟨0, ?_, by simp⟩
    exact Finset.mem_erase.2 ⟨ne_of_lt hl0, h0⟩
  have hBpos : 0 < B.card := hBne.card_pos
  set nB := B.image (fun x => -x) with hnBdef
  have hnBcard : nB.card = B.card :=
    Finset.card_image_of_injective _ (fun a b h => by rwa [neg_inj] at h)
  have hnBne : nB.Nonempty := hBne.image _
  have hBB : B.image₂ (· - ·) B = B + nB := by
    ext x
    simp only [Finset.mem_image₂, Finset.mem_add, hnBdef, Finset.mem_image]
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact ⟨a, ha, -b, ⟨b, hb, rfl⟩, by ring⟩
    · rintro ⟨a, ha, b, ⟨b', hb', rfl⟩, rfl⟩
      exact ⟨a, ha, b', hb', by ring⟩
  have hU1 : B.card ≤ (B ∪ nB).card :=
    Finset.card_le_card Finset.subset_union_left
  by_cases hl1 : l = 1
  · -- `A ⊆ {0, 1}` with `0, 1 ∈ A`, so `A = {0, 1}` and `A − A = {−1, 0, 1}`.
    have hA : A = {0, 1} := by
      apply Finset.eq_of_subset_of_card_le
      · intro a ha
        have h1 := hmin a ha; have h2 := hmax a ha
        simp only [Finset.mem_insert, Finset.mem_singleton]
        omega
      · have hsub : ({0, 1} : Finset ℤ) ⊆ A := by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact h0
          · exact hl1 ▸ hl
        exact Finset.card_le_card hsub
    rw [hA]
    native_decide
  · have hl2 : (2 : ℤ) ≤ l := by omega
    have hn0 : l.toNat ≠ 0 := by
      have := Int.toNat_of_nonneg (le_of_lt hl0); omega
    have hn1 : l.toNat ≠ 1 := by
      have := Int.toNat_of_nonneg (le_of_lt hl0); omega
    have hcd := cauchy_davenport_minOrder_add hBne hnBne
    have hmo : AddMonoid.minOrder (ZMod l.toNat) = (l.toNat.minFac : ℕ∞) :=
      ZMod.minOrder hn0 hn1
    rw [hmo] at hcd
    have hN : (B.card + nB.card - 1 : ℕ) = 2 * A.card - 3 := by omega
    rw [hN] at hcd
    have hcast : ((2 * A.card - 3 : ℕ) : ℕ∞) ≤ (l.toNat.minFac : ℕ∞) := by
      exact_mod_cast hmf
    have hmin_eq : min (l.toNat.minFac : ℕ∞) ((2 * A.card - 3 : ℕ) : ℕ∞)
        = ((2 * A.card - 3 : ℕ) : ℕ∞) := min_eq_right hcast
    rw [hmin_eq] at hcd
    rw [← hBB] at hcd
    have hcd' : 2 * A.card - 3 ≤ (B.image₂ (· - ·) B).card := by
      exact_mod_cast hcd
    omega

end DifferenceSet

/-- **The residual case of Freiman's `3k − 4` difference bound.**
This is the periodic-boundary case of the theorem: large diameter
(`2|A| − 2 ≤ l`) together with a small prime factor of `l`
(`minFac l ≤ 2|A| − 4`).  `freiman3k4` below shows that
`Freiman3k4Residual → Freiman3k4`, i.e. this is the *only* remaining
hypothesis needed to make `dfst_of_freiman3k4` unconditional. -/
def Freiman3k4Residual : Prop :=
  ∀ A : Finset ℤ, ∀ l : ℤ,
    0 ∈ A → l ∈ A → (∀ x ∈ A, 0 ≤ x ∧ x ≤ l) →
    (∀ d : ℤ, 2 ≤ d → ∃ x ∈ A, ∃ y ∈ A, ¬ d ∣ x - y) →
    2 * (A.card : ℤ) - 2 ≤ l → (l.toNat.minFac : ℤ) ≤ 2 * (A.card : ℤ) - 4 →
      3 * (A.card : ℤ) - 3 ≤ ((A.image₂ (· - ·) A).card : ℤ)

/-- **Freiman's `3k − 4` bound for `A − A`, modulo the residual
periodic-boundary hypothesis.** -/
theorem freiman3k4 (hres : Freiman3k4Residual) : Freiman3k4 := by
  classical
  intro A l h0 hl hmem hgcd
  have hmin : ∀ x ∈ A, 0 ≤ x := fun x hx => (hmem x hx).1
  have hmax : ∀ x ∈ A, x ≤ l := fun x hx => (hmem x hx).2
  have hne : A.Nonempty := ⟨0, h0⟩
  have htriv : 2 * (A.card : ℤ) - 1 ≤ ((A.image₂ (· - ·) A).card : ℤ) := by
    have h := card_sub_self_ge hne
    have hk : 1 ≤ A.card := Finset.card_pos.2 hne
    omega
  by_cases hk2 : A.card ≤ 2
  · calc min (l + A.card) (3 * A.card - 3) ≤ 3 * A.card - 3 :=
        min_le_right _ _
      _ ≤ 2 * A.card - 1 := by omega
      _ ≤ (A.image₂ (· - ·) A).card := htriv
  · push Not at hk2
    by_cases hdiam : l + 3 ≤ 2 * A.card
    · calc min (l + A.card) (3 * A.card - 3) ≤ l + A.card :=
          min_le_left _ _
        _ ≤ (A.image₂ (· - ·) A).card :=
          card_sub_self_ge_diam_add_card h0 hl hmin hmax hdiam
    · push Not at hdiam
      have hl0 : 0 < l := by
        have h00 := hmin 0 h0
        omega
      rw [min_eq_right (show 3 * (A.card : ℤ) - 3 ≤ l + A.card by omega)]
      by_cases hmf : 2 * A.card - 3 ≤ l.toNat.minFac
      · have h := card_sub_self_ge_three_mul_sub_three_of_minFac
          h0 hl hl0 hmin hmax hmf
        omega
      · push Not at hmf
        exact hres A l h0 hl hmem hgcd (by omega) (by omega)

end JSP000728
