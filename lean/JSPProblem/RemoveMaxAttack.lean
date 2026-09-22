/-
# Attack on `RemoveMaxResidual`

This file develops two independent routes towards `JSP000728.RemoveMaxResidual`
(`JSPProblem/FreimanResidualB.lean`), the residual inverse statement of the
elementary remove-max proof of Freiman's `3k − 3` difference-set bound.

Recall the setup: `A ⊆ [0, l]`, `0, l ∈ A`, `2|A| − 2 ≤ l`, `A` has coprime
differences, `A' = A ∖ {l}`, `l' = max A'`, `A'` coprime,
`r = #{a' ∈ A' : l − a' ∉ A' − A'}`, and either `r = 1` or `l' + 2r < 2|A| − 2`.
The goal is `3|A| − 3 ≤ |A − A|`.

## Route 1: the modular fibre bound (proved)

`card_sub_self_ge_zmod` gives, for `B := modIm A l ⊆ ZMod l` (the residues of
`A'`),

  `|A − A| ≥ |B − B| + |B ∪ (−B)| + 1`.

Since `0 ∈ B` one has `B ∪ (−B) ⊆ B − B`, hence

  `|A − A| ≥ 2|B ∪ (−B)| + 1 = 4|B| − 2|B ∩ (−B)| + 1`.

Two sufficient conditions follow immediately:

* `card_sub_self_ge_of_small_symm_part` — if `2|B ∩ (−B)| ≤ |B| + 1` (i.e. the
  symmetric part `{a' ∈ A' : l − a' ∈ A'}` has at most `(|A'| + 1)/2` elements)
  then `|A − A| ≥ 3|A| − 3`.  No residual hypothesis needed.
* `card_sub_self_ge_of_addStab_zero` — if `B − B` is *aperiodic* in `ZMod l`
  (trivial stabilizer), Kneser's theorem (`ZMod.kneser_sub_aperiodic`) gives
  `|B − B| ≥ 2|B| − 1` and again `|A − A| ≥ 3|A| − 3`.

The same fibre bound applied to `A'` at `l'` (the set `B' = modIm A' l'`) gives
`|A' − A'| ≥ 3(|A'| − 1)` whenever `B' − B'` is aperiodic, hence
`|A − A| ≥ 3|A| − 6 + 2r`, which closes the target unless `r = 1` and `B'` is
symmetric (`A'` symmetric about `l'/2`).

## Route 2: the integer near-symmetric analysis (reduction proved)

When `r = 1`, every `a' ∈ A' ∖ {0}` has `l − a' ∈ A' − A'`, which forces
`A' ∖ {0} ⊆ [l − l', l']` and `l − (A' ∖ {0}) ⊆ posDiff A'`.  Writing
`I = A' ∖ {0}` one has `posDiff A' = I ∪ posDiff I` and

  `|A − A| = 2|I ∪ posDiff I| + 3`,

so the `r = 1` disjunct is *exactly* the following combinatorial statement
(`posDiff_union_card_ge`, proved as a reduction):

  for `I ⊆ [c, l − c]` (`c = l − l' ≥ 1`) with `σ(I) ⊆ I ∪ posDiff I`,
  `σ x = l − x`, and `2|I| + 2 ≤ l`, one has `2|I ∪ posDiff I| ≥ 3|I|`.

## Remaining gap

The unproven residue is the *super-symmetric periodic* corner.  Concretely,
after the lemmas below the target remains open only when **all** of the
following hold simultaneously:

* `B = modIm A l` satisfies `2|B ∩ (−B)| ≥ |B| + 2` — more than half of `A'`
  reflects into `A'` under `a' ↦ l − a'`;
* `B − B` has nontrivial stabilizer in `ZMod l` (Kneser periodic case);
* the same alternative fails at `l'`: `B' − B'` periodic in `ZMod l'`, or `r = 1`
  with `B'` symmetric.

In the `r = 1` case what remains is exactly `posDiff_union_card_ge` above; the
natural strategy (count `I ∪ σI` and the small differences of `I` below `c`)
requires `|posDiff I ∩ [1, c)| ≥ |I ∩ σI| − |I|/2`, which in turn needs the
cluster analysis of `I ∩ σI` symmetric about `l/2`.  In the second disjunct
(`l' + 2r < 2|A| − 2`, i.e. `l' + 2r < 2|A'|`) the needed slack is
`δ = (2|A'| − l' − 2r) ≥ 1` beyond the small-diameter bound
`|A' − A'| ≥ l' + |A'|` (`card_sub_self_ge_diam_add_card`).
-/

import JSPProblem.FreimanResidualB
import JSPProblem.KneserZMod

namespace JSP000728

open Finset
open scoped Pointwise

/-! ### The modular shadow: cardinality and symmetry counts -/

section ModShadow

variable {A : Finset ℤ} {l : ℤ}

/-- The cast `ℤ → ZMod l.toNat` is injective on `A ∖ {l} ⊆ [0, l)`, so the
modular shadow `modIm A l` has `|A| − 1` elements. -/
lemma card_modIm (hmin : ∀ x ∈ A, 0 ≤ x) (hmax : ∀ x ∈ A, x ≤ l)
    (hl0 : 0 < l) :
    (modIm A l).card = (A.erase l).card := by
  unfold modIm
  rw [Finset.card_image_of_injOn]
  intro x hx y hy hxy
  have hxA := (Finset.mem_erase.1 hx).2
  have hyA := (Finset.mem_erase.1 hy).2
  have hxlt : x < l := lt_of_le_of_ne (hmax x hxA) (Finset.mem_erase.1 hx).1
  have hylt : y < l := lt_of_le_of_ne (hmax y hyA) (Finset.mem_erase.1 hy).1
  have hx0 := hmin x hxA
  have hy0 := hmin y hyA
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at hxy
  obtain ⟨k, hk⟩ := hxy
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

/-- `0 ∈ B` for the modular shadow `B = modIm A l`. -/
lemma zero_mem_modIm (h0 : 0 ∈ A) (hl0 : 0 < l) :
    (0 : ZMod l.toNat) ∈ modIm A l := by
  refine Finset.mem_image.2 ⟨0, Finset.mem_erase.2 ⟨ne_of_lt hl0, h0⟩, ?_⟩
  simp

/-- For `0 ∈ B`, the symmetric hull `B ∪ (−B)` is contained in `B − B`. -/
lemma union_image_neg_subset_image₂_sub {N : ℕ} {B : Finset (ZMod N)}
    (hB0 : 0 ∈ B) :
    B ∪ B.image (fun x => -x) ⊆ B.image₂ (· - ·) B := by
  intro x hx
  rcases Finset.mem_union.1 hx with h | h
  · exact Finset.mem_image₂.2 ⟨x, h, 0, hB0, sub_zero x⟩
  · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 h
    exact Finset.mem_image₂.2 ⟨0, hB0, b, hb, zero_sub b⟩

/-- `|B ∪ (−B)| = 2|B| − |B ∩ (−B)|`. -/
lemma card_union_image_neg {N : ℕ} (B : Finset (ZMod N)) :
    ((B ∪ B.image (fun x => -x)).card : ℤ) =
      2 * B.card - (B ∩ B.image (fun x => -x)).card := by
  have hneg : (B.image (fun x => -x)).card = B.card :=
    Finset.card_image_of_injective _ (fun a b h => by simpa using h)
  have h := Finset.card_union B (B.image (fun x => -x))
  rw [hneg] at h
  have h1 : ((B ∪ B.image (fun x => -x)).card +
      (B ∩ B.image (fun x => -x)).card : ℕ) = 2 * B.card := by omega
  have h2 : (((B ∪ B.image (fun x => -x)).card +
      (B ∩ B.image (fun x => -x)).card : ℕ) : ℤ) = 2 * (B.card : ℤ) := by
    exact_mod_cast h1
  push_cast at h2
  omega

/-- **First sufficient condition**: if the symmetric part
`B ∩ (−B)` (the elements `a' ∈ A'` with `l − a' ∈ A'`) has at most
`(|A'| + 1)/2` elements, then `|A − A| ≥ 3|A| − 3`.

This needs none of the residual hypotheses: it already settles the whole
problem unless `A'` is majority-symmetric about `l/2`. -/
theorem card_sub_self_ge_of_small_symm_part
    (h0 : 0 ∈ A) (hl : l ∈ A)
    (hmin : ∀ x ∈ A, 0 ≤ x) (hmax : ∀ x ∈ A, x ≤ l) (hl0 : 0 < l)
    (hsymm : 2 * ((modIm A l) ∩ (modIm A l).image (fun x => -x)).card ≤
      (modIm A l).card + 1) :
    3 * (A.card : ℤ) - 3 ≤ ((A.image₂ (· - ·) A).card : ℤ) := by
  classical
  set B := modIm A l with hBdef
  have hB0 : (0 : ZMod l.toNat) ∈ B := zero_mem_modIm h0 hl0
  have hsub : B ∪ B.image (fun x => -x) ⊆ B.image₂ (· - ·) B :=
    union_image_neg_subset_image₂_sub hB0
  have hzmod := card_sub_self_ge_zmod h0 hl hl0 hmin hmax
  have hle1 : (B ∪ B.image (fun x => -x)).card ≤ (B.image₂ (· - ·) B).card :=
    Finset.card_le_card hsub
  have hunion := card_union_image_neg B
  have hcardB : B.card = (A.erase l).card := card_modIm hmin hmax hl0
  have hcardA' : ((A.erase l).card : ℤ) = (A.card : ℤ) - 1 := by
    have h := Finset.card_erase_of_mem hl
    have h1 : 1 ≤ A.card := Finset.card_pos.2 ⟨l, hl⟩
    omega
  -- `|A − A| ≥ 2|B ∪ (−B)| + 1 ≥ 3|B| = 3|A| − 3`.
  have hcast : ((B.image₂ (· - ·) B).card +
      (B ∪ B.image (fun x => -x)).card + 1 : ℕ) ≤
      (A.image₂ (· - ·) A).card := hzmod
  have hz : (((B.image₂ (· - ·) B).card +
      (B ∪ B.image (fun x => -x)).card + 1 : ℕ) : ℤ) ≤
      ((A.image₂ (· - ·) A).card : ℤ) := by exact_mod_cast hcast
  push_cast at hz
  omega

/-- **Second sufficient condition**: if `B − B` is aperiodic in `ZMod l`
(trivial pointwise stabilizer), Kneser's theorem gives `|B − B| ≥ 2|B| − 1`
and hence `|A − A| ≥ 3|A| − 3`. -/
theorem card_sub_self_ge_of_addStab_zero
    (h0 : 0 ∈ A) (hl : l ∈ A)
    (hmin : ∀ x ∈ A, 0 ≤ x) (hmax : ∀ x ∈ A, x ≤ l) (hl0 : 0 < l)
    (hstab : ((modIm A l) - (modIm A l)).addStab = 0) :
    3 * (A.card : ℤ) - 3 ≤ ((A.image₂ (· - ·) A).card : ℤ) := by
  classical
  set B := modIm A l with hBdef
  have hB0 : (0 : ZMod l.toNat) ∈ B := zero_mem_modIm h0 hl0
  have hBne : B.Nonempty := ⟨0, hB0⟩
  have hsub : B ∪ B.image (fun x => -x) ⊆ B.image₂ (· - ·) B :=
    union_image_neg_subset_image₂_sub hB0
  have hzmod := card_sub_self_ge_zmod h0 hl hl0 hmin hmax
  have hkn : 2 * B.card - 1 ≤ (B - B).card :=
    ZMod.kneser_sub_aperiodic hBne hstab
  have hBB : B - B = B.image₂ (· - ·) B := rfl
  rw [hBB] at hkn
  have hle1 : B.card ≤ (B ∪ B.image (fun x => -x)).card :=
    Finset.card_le_card Finset.subset_union_left
  have hcardB : B.card = (A.erase l).card := card_modIm hmin hmax hl0
  have hcardA' : ((A.erase l).card : ℤ) = (A.card : ℤ) - 1 := by
    have h := Finset.card_erase_of_mem hl
    have h1 : 1 ≤ A.card := Finset.card_pos.2 ⟨l, hl⟩
    omega
  have hz : (((B.image₂ (· - ·) B).card +
      (B ∪ B.image (fun x => -x)).card + 1 : ℕ) : ℤ) ≤
      ((A.image₂ (· - ·) A).card : ℤ) := by exact_mod_cast hzmod
  push_cast at hz
  omega

end ModShadow

/-! ### The `r = 1` reduction to the combinatorial core -/

section ROne

variable {A : Finset ℤ} {l l' : ℤ}

/-- When `r = 1`, the `removeMaxR` filter is exactly `{0}`: `0` always belongs
to it (`l` is never an `A'`-difference), and it has a single element. -/
lemma removeMaxR_filter_eq_singleton
    (h0 : 0 ∈ A) (hl : l ∈ A)
    (hmin : ∀ x ∈ A, 0 ≤ x) (hmax : ∀ x ∈ A, x ≤ l) (hl0 : 0 < l)
    (hr : ((A.erase l).filter (fun a' => l - a' ∉
        (A.erase l).image₂ (· - ·) (A.erase l))).card = 1) :
    (A.erase l).filter (fun a' => l - a' ∉
        (A.erase l).image₂ (· - ·) (A.erase l)) = {0} := by
  have h0mem : (0 : ℤ) ∈ (A.erase l).filter
      (fun a' => l - a' ∉ (A.erase l).image₂ (· - ·) (A.erase l)) := by
    refine Finset.mem_filter.2 ⟨Finset.mem_erase.2 ⟨ne_of_lt hl0, h0⟩, ?_⟩
    intro hmem
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.mem_image₂.1 hmem
    have hxl : x < l :=
      lt_of_le_of_ne (hmax x (Finset.mem_erase.1 hx).2)
        (Finset.mem_erase.1 hx).1
    have hy0 := hmin y (Finset.mem_erase.1 hy).2
    omega
  rw [Finset.card_eq_one] at hr
  obtain ⟨a, ha⟩ := hr
  rw [ha] at h0mem
  rw [Finset.mem_singleton] at h0mem
  rw [h0mem] at ha
  exact ha

/-- When `r = 1`, every nonzero `a' ∈ A'` has `l − a' ∈ A' − A'`. -/
lemma sub_mem_image₂_of_r_eq_one
    (hr : (A.erase l).filter (fun a' => l - a' ∉
        (A.erase l).image₂ (· - ·) (A.erase l)) = {0})
    {a' : ℤ} (ha' : a' ∈ A.erase l) (ha0 : a' ≠ 0) :
    l - a' ∈ (A.erase l).image₂ (· - ·) (A.erase l) := by
  by_contra h
  have hmem : a' ∈ (A.erase l).filter
      (fun a' => l - a' ∉ (A.erase l).image₂ (· - ·) (A.erase l)) :=
    Finset.mem_filter.2 ⟨ha', h⟩
  rw [hr, Finset.mem_singleton] at hmem
  exact ha0 hmem

/-- For `I = A' ∖ {0}`, the positive differences of `A'` split as
`posDiff A' = I ∪ posDiff I`: a positive difference `x − y` either has
`y = 0` (and equals `x ∈ I`) or is a difference inside `I`. -/
lemma posDiff_erase_eq_union (h0' : 0 ∈ A.erase l)
    (hmin' : ∀ x ∈ A.erase l, 0 ≤ x) :
    posDiff (A.erase l) =
      (A.erase l).erase 0 ∪ posDiff ((A.erase l).erase 0) := by
  ext d
  simp only [mem_posDiff, Finset.mem_union, Finset.mem_erase, ne_eq]
  constructor
  · rintro ⟨⟨x, hx, y, hy, rfl⟩, hdpos⟩
    by_cases hy0 : y = 0
    · subst hy0
      left
      exact ⟨by omega, by rwa [sub_zero]⟩
    · right
      have hx0 : x ≠ 0 := by
        have hy0' := hmin' y hy
        omega
      exact ⟨⟨x, ⟨hx0, hx⟩, y, ⟨hy0, hy⟩, rfl⟩, hdpos⟩
  · intro h
    rcases h with ⟨hd0, hd⟩ | ⟨⟨x, hx, y, hy, rfl⟩, hdpos⟩
    · exact ⟨⟨d, hd, 0, h0', sub_zero d⟩, by
        have := hmin' d hd; omega⟩
    · exact ⟨⟨x, (Finset.mem_erase.1 hx).2, y, (Finset.mem_erase.1 hy).2, rfl⟩,
        hdpos⟩

/-- When `r = 1`, the reflected elements `l − i`, `i ∈ I`, are positive
differences of `A'`, i.e. `σ(I) ⊆ posDiff A' = I ∪ posDiff I`. -/
lemma refl_mem_posDiff_of_r_eq_one
    (h0 : 0 ∈ A) (hl : l ∈ A)
    (hmin : ∀ x ∈ A, 0 ≤ x) (hmax : ∀ x ∈ A, x ≤ l) (hl0 : 0 < l)
    {l' : ℤ} (hl'max : ∀ a' ∈ A.erase l, a' ≤ l')
    (hr : (A.erase l).filter (fun a' => l - a' ∉
        (A.erase l).image₂ (· - ·) (A.erase l)) = {0})
    {i : ℤ} (hi : i ∈ (A.erase l).erase 0) :
    l - i ∈ posDiff (A.erase l) := by
  have hiA : i ∈ A.erase l := (Finset.mem_erase.1 hi).2
  have hi0 : i ≠ 0 := (Finset.mem_erase.1 hi).1
  have hsub : l - i ∈ (A.erase l).image₂ (· - ·) (A.erase l) :=
    sub_mem_image₂_of_r_eq_one hr hiA hi0
  have hpos : 0 < l - i := by
    have h1 := hl'max i hiA
    have h2 := (Finset.mem_erase.1 hiA).1
    omega
  exact mem_posDiff.2 ⟨Finset.mem_image₂.1 hsub, hpos⟩

/-- When `r = 1`, `I = A' ∖ {0} ⊆ [l − l', l']`: the reflected element
`l − a'` is an `A'`-difference, hence `≤ l'`. -/
lemma erase_zero_subset_Icc_of_r_eq_one
    (hmin' : ∀ x ∈ A.erase l, 0 ≤ x)
    {l' : ℤ} (hl'max : ∀ a' ∈ A.erase l, a' ≤ l')
    (hr : (A.erase l).filter (fun a' => l - a' ∉
        (A.erase l).image₂ (· - ·) (A.erase l)) = {0}) :
    (A.erase l).erase 0 ⊆ Finset.Icc (l - l') l' := by
  intro i hi
  have hiA : i ∈ A.erase l := (Finset.mem_erase.1 hi).2
  have hi0 : i ≠ 0 := (Finset.mem_erase.1 hi).1
  have hsub := sub_mem_image₂_of_r_eq_one hr hiA hi0
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.mem_image₂.1 hsub
  have hx' := hl'max x hx
  have hy0 := hmin' y hy
  have hi' := hl'max i hiA
  rw [Finset.mem_Icc]
  omega

/-- **The `r = 1` reduction.**  The first disjunct of `RemoveMaxResidual`
reduces to the combinatorial statement `2|I ∪ posDiff I| ≥ 3|I|` for
`I = A' ∖ {0}` (which satisfies `I ⊆ [l − l', l']` and
`l − I ⊆ I ∪ posDiff I` by the lemmas above). -/
theorem card_sub_self_ge_of_r_eq_one
    (h0 : 0 ∈ A) (hl : l ∈ A)
    (hmin : ∀ x ∈ A, 0 ≤ x) (hmax : ∀ x ∈ A, x ≤ l) (hl0 : 0 < l)
    (hr : ((A.erase l).filter (fun a' => l - a' ∉
        (A.erase l).image₂ (· - ·) (A.erase l))).card = 1)
    (hcomb : 3 * (((A.erase l).erase 0).card : ℤ) ≤
      2 * ((((A.erase l).erase 0) ∪ posDiff ((A.erase l).erase 0)).card : ℤ)) :
    3 * (A.card : ℤ) - 3 ≤ ((A.image₂ (· - ·) A).card : ℤ) := by
  classical
  have h0' : (0 : ℤ) ∈ A.erase l := Finset.mem_erase.2 ⟨ne_of_lt hl0, h0⟩
  have hne : (A.erase l).Nonempty := ⟨0, h0'⟩
  have hident := card_sub_self_eq_erase_add_two_mul_r h0 hl hmin hmax hl0
  have hmin' : ∀ x ∈ A.erase l, 0 ≤ x := fun x hx =>
    hmin x (Finset.mem_erase.1 hx).2
  have hsplit := posDiff_erase_eq_union h0' hmin'
  have hcard : ((A.erase l).image₂ (· - ·) (A.erase l)).card =
      2 * (posDiff (A.erase l)).card + 1 := card_image_sub_self hne
  have hcardA' : ((A.erase l).card : ℤ) = (A.card : ℤ) - 1 := by
    have h := Finset.card_erase_of_mem hl
    have h1 : 1 ≤ A.card := Finset.card_pos.2 ⟨l, hl⟩
    omega
  have hunfold : removeMaxR A l = 1 := hr
  have hIcard : (((A.erase l).erase 0).card : ℤ) = (A.card : ℤ) - 2 := by
    have h := Finset.card_erase_of_mem h0'
    omega
  have hpos : (posDiff (A.erase l)).card =
      (((A.erase l).erase 0) ∪ posDiff ((A.erase l).erase 0)).card := by
    rw [hsplit]
  rw [hunfold] at hident
  push_cast at hident hcard
  omega

end ROne

/-! ### The unified `posDiff` reduction -/

section PosDiffReduction

variable {A : Finset ℤ} {l : ℤ}

/-- **Unified reduction of `RemoveMaxResidual`.**  For `I = A' ∖ {0}` one has
`|A − A| = 2|I ∪ posDiff I| + 1 + 2r`, so the conclusion `3|A| − 3 ≤ |A − A|`
is equivalent to

  `2|I ∪ posDiff I| ≥ 3|I| + 2 − 2r`.

For `r = 1` this is the `2|I ∪ posDiff I| ≥ 3|I|` of
`card_sub_self_ge_of_r_eq_one`; for the second disjunct the slack `2r` makes
the required bound progressively weaker. -/
theorem card_sub_self_ge_of_posDiff_union_bound
    (h0 : 0 ∈ A) (hl : l ∈ A)
    (hmin : ∀ x ∈ A, 0 ≤ x) (hmax : ∀ x ∈ A, x ≤ l) (hl0 : 0 < l)
    (hcomb : 3 * (((A.erase l).erase 0).card : ℤ) + 2 -
        2 * (removeMaxR A l : ℤ) ≤
      2 * ((((A.erase l).erase 0) ∪ posDiff ((A.erase l).erase 0)).card : ℤ)) :
    3 * (A.card : ℤ) - 3 ≤ ((A.image₂ (· - ·) A).card : ℤ) := by
  classical
  have h0' : (0 : ℤ) ∈ A.erase l := Finset.mem_erase.2 ⟨ne_of_lt hl0, h0⟩
  have hne : (A.erase l).Nonempty := ⟨0, h0'⟩
  have hident := card_sub_self_eq_erase_add_two_mul_r h0 hl hmin hmax hl0
  have hmin' : ∀ x ∈ A.erase l, 0 ≤ x := fun x hx =>
    hmin x (Finset.mem_erase.1 hx).2
  have hsplit := posDiff_erase_eq_union h0' hmin'
  have hcard : ((A.erase l).image₂ (· - ·) (A.erase l)).card =
      2 * (posDiff (A.erase l)).card + 1 := card_image_sub_self hne
  have hIcard : (((A.erase l).erase 0).card : ℤ) = (A.card : ℤ) - 2 := by
    have h := Finset.card_erase_of_mem h0'
    have h1 := Finset.card_erase_of_mem hl
    omega
  have hpos : (posDiff (A.erase l)).card =
      (((A.erase l).erase 0) ∪ posDiff ((A.erase l).erase 0)).card := by
    rw [hsplit]
  push_cast at hident hcard
  omega

end PosDiffReduction

/-! ### The second disjunct: reductions -/

section RSmall

variable {A : Finset ℤ} {l l' : ℤ}

/-- In the second disjunct (`l' + 2r < 2|A| − 2`), the diameter `l'` of `A'`
satisfies `l' ≤ 2|A'| − 3` (the small-diameter regime): indeed `r ≥ 1` and
`2|A| − 2 = 2|A'|`. -/
lemma erase_le_two_mul_card_sub_three
    (h0 : 0 ∈ A) (hl : l ∈ A)
    (hmin : ∀ x ∈ A, 0 ≤ x) (hmax : ∀ x ∈ A, x ≤ l) (hl0 : 0 < l)
    (hgap : l' + 2 * (((A.erase l).filter (fun a' => l - a' ∉
        (A.erase l).image₂ (· - ·) (A.erase l))).card : ℤ)
        < 2 * (A.card : ℤ) - 2) :
    l' + 3 ≤ 2 * ((A.erase l).card : ℤ) := by
  have hcardA' : ((A.erase l).card : ℤ) = (A.card : ℤ) - 1 := by
    have h := Finset.card_erase_of_mem hl
    have h1 : 1 ≤ A.card := Finset.card_pos.2 ⟨l, hl⟩
    omega
  have hr1 : (1 : ℤ) ≤ (((A.erase l).filter (fun a' => l - a' ∉
      (A.erase l).image₂ (· - ·) (A.erase l))).card : ℤ) := by
    have h := one_le_removeMaxR h0 hl hmin hmax hl0
    exact_mod_cast h
  omega

/-- In the second disjunct, `2l' ≥ l` (i.e. `c = l − l' ≤ l'`): otherwise every
`a' ∈ A'` is below `c` and lies in `R`, giving `r = |A'|` and
`l' + 2r ≥ 2|A| − 2`, a contradiction. -/
lemma two_mul_le_sub_of_gap
    (h0 : 0 ∈ A) (hl : l ∈ A)
    (hmin : ∀ x ∈ A, 0 ≤ x) (hmax : ∀ x ∈ A, x ≤ l) (hl0 : 0 < l)
    (hl'max : ∀ a' ∈ A.erase l, a' ≤ l')
    (hgap : l' + 2 * (((A.erase l).filter (fun a' => l - a' ∉
        (A.erase l).image₂ (· - ·) (A.erase l))).card : ℤ)
        < 2 * (A.card : ℤ) - 2) :
    2 * l' ≥ l := by
  classical
  by_contra hcon
  push Not at hcon
  -- `c = l − l' > l'`, so every `a' ≤ l' < c` lies in `R`.
  have hc : l' < l - l' := by omega
  have hR : (A.erase l).filter (fun a' => l - a' ∉
      (A.erase l).image₂ (· - ·) (A.erase l)) = A.erase l := by
    apply Finset.filter_true_of_mem
    intro a' ha' hmem
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.mem_image₂.1 hmem
    have hx' := hl'max x hx
    have hy0 := hmin y (Finset.mem_erase.1 hy).2
    have ha'' := hl'max a' ha'
    omega
  have hcardA' : ((A.erase l).card : ℤ) = (A.card : ℤ) - 1 := by
    have h := Finset.card_erase_of_mem hl
    have h1 : 1 ≤ A.card := Finset.card_pos.2 ⟨l, hl⟩
    omega
  have hr : (((A.erase l).filter (fun a' => l - a' ∉
      (A.erase l).image₂ (· - ·) (A.erase l))).card : ℤ) =
      (A.card : ℤ) - 1 := by
    rw [hR, hcardA']
  rw [hr] at hgap
  have h0' : (0 : ℤ) ∈ A.erase l := Finset.mem_erase.2 ⟨ne_of_lt hl0, h0⟩
  have hl'0 : 0 ≤ l' := le_trans (hmin 0 ((Finset.mem_erase.1 h0').2))
    (hl'max 0 h0')
  omega

/-- The fibre bound applied to `A'` at `l'`: `|A' − A|` ≥ `|B' − B'| +
|B' ∪ (−B')| + 1` for `B' = modIm A' l'`.  Together with the remove-max
identity this gives the *third sufficient condition*: if `B' − B'` is
aperiodic in `ZMod l'`, then `|A − A| ≥ 3|A| − 6 + 2r + δ`, which proves the
target whenever `r ≥ 2` or `r = 1` and `B'` is not symmetric. -/
theorem card_sub_self_ge_of_erase_addStab_zero
    (h0 : 0 ∈ A) (hl : l ∈ A)
    (hmin : ∀ x ∈ A, 0 ≤ x) (hmax : ∀ x ∈ A, x ≤ l) (hl0 : 0 < l)
    {l' : ℤ} (hl'mem : l' ∈ A.erase l)
    (hl'max : ∀ a' ∈ A.erase l, a' ≤ l')
    (hstab : ((modIm (A.erase l) l') - (modIm (A.erase l) l')).addStab = 0) :
    3 * (A.card : ℤ) - 6 + 2 * (removeMaxR A l : ℤ) ≤
      ((A.image₂ (· - ·) A).card : ℤ) := by
  classical
  set A' := A.erase l with hA'def
  have h0' : (0 : ℤ) ∈ A' := Finset.mem_erase.2 ⟨ne_of_lt hl0, h0⟩
  have hmin' : ∀ x ∈ A', 0 ≤ x := fun x hx => hmin x (Finset.mem_erase.1 hx).2
  have hl'0 : 0 < l' := by
    have h1 := hmin' l' hl'mem
    have h2 := (Finset.mem_erase.1 hl'mem).1
    omega
  have hzmod := card_sub_self_ge_zmod h0' hl'mem hl'0 hmin' hl'max
  set B' := modIm A' l' with hB'def
  have hB'0 : (0 : ZMod l'.toNat) ∈ B' := zero_mem_modIm h0' hl'0
  have hB'ne : B'.Nonempty := ⟨0, hB'0⟩
  have hsub : B' ∪ B'.image (fun x => -x) ⊆ B'.image₂ (· - ·) B' :=
    union_image_neg_subset_image₂_sub hB'0
  have hkn : 2 * B'.card - 1 ≤ (B' - B').card :=
    ZMod.kneser_sub_aperiodic hB'ne hstab
  have hBB : B' - B' = B'.image₂ (· - ·) B' := rfl
  rw [hBB] at hkn
  have hle1 : B'.card ≤ (B' ∪ B'.image (fun x => -x)).card :=
    Finset.card_le_card Finset.subset_union_left
  have hcardB' : B'.card = (A'.erase l').card :=
    card_modIm hmin' hl'max hl'0
  have hcardB'2 : ((A'.erase l').card : ℤ) = (A.card : ℤ) - 2 := by
    have h1 := Finset.card_erase_of_mem hl
    have h2 := Finset.card_erase_of_mem hl'mem
    omega
  have hident := card_sub_self_eq_erase_add_two_mul_r h0 hl hmin hmax hl0
  have hz : (((B'.image₂ (· - ·) B').card +
      (B' ∪ B'.image (fun x => -x)).card + 1 : ℕ) : ℤ) ≤
      ((A'.image₂ (· - ·) A').card : ℤ) := by exact_mod_cast hzmod
  push_cast at hz hident
  omega

end RSmall

end JSP000728
