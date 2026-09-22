/-
Reduction of `Freiman3k4Residual` to a cyclic Kneser-type bound.

## Mathematical content

For `A ⊆ [0, l]` containing `0` and `l` with `0 < l`, the difference set
`A − A ⊆ [−l, l]` is symmetric and contains `0, ±l`, hence

  `|A − A| = 2·|P_A| + 3`,   `P_A := (A − A) ∩ (0, l)`.

Writing `A₀ = A ∖ {l} ⊆ [0, l)`, the positive differences below `l` split as

  `P_A = posDiff(A₀) ∪ (l − (A₀ ∖ {0}))`
       = (A₀ − A₀) ∩ (0, l)  ∪  {l − a : a ∈ A₀, a ≠ 0}

(`posDiff_eq_erase_union_image` below).  The `modIm`-fiber bound
`card_sub_self_ge_zmod` of `Freiman3k4.lean` is a weakening of this exact
count: the residues of `P_A` are the classes of `B − B` realised in the
"positive" direction, `l − P_A` gives the negative-direction realisations,
and `P_A ∩ (l − P_A)` are the classes realised in *both* directions (of which
`B ∪ (−B)` is the obvious part).

The residual estimate needed for Freiman's `3k − 4` theorem is

  `3(|A₀| − 1) ≤ 2·|posDiff(A₀) ∪ (l − A₀')|`

whenever `2|A₀| ≤ l` and the differences of `A₀` generate `ZMod l` (i.e. no
`d ≥ 2` dividing `l` divides all differences).  This is precisely the
conclusion of Kneser's theorem applied to the modular shadow
`B = A₀ ⊆ ZMod l`, combined with the both-direction fiber refinement: with
`H = stabilizer(B − B)`, `|B − B| ≥ 2|B + H| − |H|` is sufficient unless `H`
is a proper nontrivial subgroup and `B` is (nearly) `H`-saturated, in which
case the partial/full `H`-cosets supply the missing `|H| − 1` both-direction
fibres via the grid descent `A₀ = φ⁻¹(B̄)`, `B̄ ⊆ ZMod (l/|H|)`.  We package
that conclusion as the hypothesis `ZModKneserBound` (the "rectified" output
of the cyclic Kneser analysis) and prove

  `ZModKneserBound → Freiman3k4Residual`

in `freiman3k4Residual`.

## Main declarations

* `ZModKneserBound` — the packaged periodic-boundary bound.
* `posDiff_filter_lt_eq` — the decomposition `P_A = posDiff(A₀) ∪ (l − A₀')`.
* `card_image2_sub_self_eq` — `|A − A| = 2·|P_A| + 3`.
* `modIm_sub_self_eq` — `B − B` is `{0}` plus the residues of `P ∪ (l − P)`.
* `card_sub_self_eq_zmod_fiber` — the exact fiber identity
  `|A − A| = |B − B| + |P_A ∩ (l − P_A)| + 2`, sharpening
  `card_sub_self_ge_zmod` and locating precisely where additional fibers can
  come from.
* `exists_not_dvd_sub_of_erase` — the generation hypothesis descends to
  `A₀ = A ∖ {l}` for divisors of `l`.
* `freiman3k4Residual` — `ZModKneserBound → Freiman3k4Residual`.
-/

import JSPProblem.Freiman3k4

namespace JSP000728

open Finset
open scoped Pointwise

/-- **The periodic-boundary bound** (cyclic Kneser + fiber refinement, in
rectified form): for `A₀ ⊆ [0, l)` containing `0`, with `2|A₀| ≤ l` and whose
differences generate `ZMod l` (no `d ≥ 2` with `d ∣ l` divides all
differences), the positive differences of `A₀` together with the reflected
set `l − (A₀ ∖ {0})` occupy at least `3(|A₀| − 1)/2` points of `(0, l)`.

This is the conclusion of Kneser's theorem for `ZMod l` applied to
`B = A₀`, lifted through the fiber count `|A − A| = 2·|P_A| + 3`; it is the
genuine mathematical content of the periodic case of Freiman's `3k − 4`
theorem for `A − A`. -/
def ZModKneserBound : Prop :=
  ∀ (l : ℤ) (A₀ : Finset ℤ),
    0 < l → 0 ∈ A₀ → (∀ x ∈ A₀, 0 ≤ x ∧ x < l) →
    2 * (A₀.card : ℤ) ≤ l →
    (∀ d : ℤ, 2 ≤ d → d ∣ l → ∃ x ∈ A₀, ∃ y ∈ A₀, ¬ d ∣ x - y) →
    3 * ((A₀.card : ℤ) - 1) ≤
      2 * (posDiff A₀ ∪ (A₀.erase 0).image (l - ·)).card

/-- The positive differences of `A` below `l` are exactly the positive
differences of `A₀ = A ∖ {l}` together with the reflected elements
`l − a`, `a ∈ A₀ ∖ {0}` (the differences `l − a`). -/
theorem posDiff_filter_lt_eq {A : Finset ℤ} {l : ℤ}
    (hl : l ∈ A) (hmin : ∀ a ∈ A, 0 ≤ a) (hmax : ∀ a ∈ A, a ≤ l) :
    (posDiff A).filter (· < l) =
      posDiff (A.erase l) ∪ ((A.erase l).erase 0).image (l - ·) := by
  ext d
  simp only [mem_posDiff, Finset.mem_filter, Finset.mem_union, Finset.mem_image,
    Finset.mem_erase]
  constructor
  · rintro ⟨⟨⟨a, ha, b, hb, rfl⟩, hd0⟩, hdl⟩
    have ha0 := hmin a ha
    have hal := hmax a ha
    have hb0 := hmin b hb
    have hbl := hmax b hb
    by_cases haeq : a = l
    · -- `a = l`: `d = l − b` with `b ∈ (0, l)`.
      right
      refine ⟨b, ⟨?_, ?_, hb⟩, ?_⟩
      · omega
      · omega
      · rw [haeq]
    · -- `a < l`: both `a, b ∈ A₀`, `d` a positive difference of `A₀`.
      left
      have halt : a < l := lt_of_le_of_ne hal haeq
      refine ⟨⟨a, ⟨haeq, ha⟩, b, ⟨?_, hb⟩, rfl⟩, hd0⟩
      omega
  · rintro (⟨⟨a, ⟨hane, ha⟩, b, ⟨-, hb⟩, rfl⟩, hd0⟩ | ⟨b, ⟨hb0, hbl, hb⟩, rfl⟩)
    · -- A positive difference of `A₀`: automatically `< l`.
      have ha0 := hmin a ha
      have hal := hmax a ha
      have hb0 := hmin b hb
      have halt : a < l := lt_of_le_of_ne hal hane
      exact ⟨⟨⟨a, ha, b, hb, rfl⟩, hd0⟩, by omega⟩
    · -- A reflected element `l − b`, `b ∈ A₀ ∖ {0}`: `l − b = l − b ∈ A − A`.
      have hb0m := hmin b hb
      have hblm := hmax b hb
      exact ⟨⟨⟨l, hl, b, hb, rfl⟩, by omega⟩, by omega⟩

/-- The difference set cardinality: `|A − A| = 2·|P_A| + 3` where
`P_A = (A − A) ∩ (0, l)`. -/
theorem card_image2_sub_self_eq {A : Finset ℤ} {l : ℤ}
    (h0 : 0 ∈ A) (hl : l ∈ A) (hl0 : 0 < l)
    (hmin : ∀ a ∈ A, 0 ≤ a) (hmax : ∀ a ∈ A, a ≤ l) :
    (A.image₂ (· - ·) A).card =
      2 * ((posDiff A).filter (· < l)).card + 3 := by
  have hne : A.Nonempty := ⟨0, h0⟩
  rw [card_image_sub_self hne]
  -- `posDiff A ⊆ [1, l]` and `l ∈ posDiff A`.
  have hsub : posDiff A ⊆ Finset.Icc 1 l := by
    have h := posDiff_subset_Icc hmin hmax
    rwa [sub_zero] at h
  have hlpos : l ∈ posDiff A :=
    mem_posDiff.2 ⟨⟨l, hl, 0, h0, by ring⟩, hl0⟩
  -- `posDiff A = (posDiff A ∩ (0,l)) ∪ {l}`.
  have heq : (posDiff A).erase l = (posDiff A).filter (· < l) := by
    ext d
    simp only [Finset.mem_erase, Finset.mem_filter]
    constructor
    · rintro ⟨hd, hpos⟩
      have hdI := Finset.mem_Icc.1 (hsub hpos)
      exact ⟨hpos, lt_of_le_of_ne hdI.2 hd⟩
    · rintro ⟨hpos, hd⟩
      exact ⟨ne_of_lt hd, hpos⟩
  have hcard : (posDiff A).card = ((posDiff A).filter (· < l)).card + 1 := by
    rw [← heq]
    exact (Finset.card_erase_add_one hlpos).symm
  omega

/-- Every residue of an element of `A` lies in the modular shadow
`B = modIm A l`. -/
theorem intCast_mem_modIm {A : Finset ℤ} {l : ℤ} (h0 : 0 ∈ A) (hl0 : 0 < l) :
    ∀ a ∈ A, ((a : ℤ) : ZMod l.toNat) ∈ modIm A l := by
  intro a ha
  by_cases hal : a = l
  · have hcastl : ((a : ℤ) : ZMod l.toNat) = 0 := by
      rw [hal]
      have e : ((l.toNat : ℤ) : ZMod l.toNat) = 0 := by
        rw [Int.cast_natCast]; exact ZMod.natCast_self _
      rwa [Int.toNat_of_nonneg (le_of_lt hl0)] at e
    rw [hcastl]
    exact Finset.mem_image.2 ⟨0, Finset.mem_erase.2 ⟨ne_of_lt hl0, h0⟩, by simp⟩
  · exact Finset.mem_image.2 ⟨a, Finset.mem_erase.2 ⟨hal, ha⟩, rfl⟩

/-- Reduction mod `l` is injective on the open interval `(0, l)`. -/
theorem intCast_injOn_Ioo {l : ℤ} (hl0 : 0 < l) :
    Set.InjOn (fun x : ℤ => (x : ZMod l.toNat)) {x : ℤ | 0 < x ∧ x < l} := by
  intro x hx y hy hxy
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at hxy
  obtain ⟨k, hk⟩ := hxy
  rw [Int.toNat_of_nonneg (le_of_lt hl0)] at hk
  have hx0 := hx.1
  have hxl := hx.2
  have hy0 := hy.1
  have hyl := hy.2
  have hk0 : k = 0 := by
    rcases lt_trichotomy k 0 with hkc | hkc | hkc
    · have : l * k ≤ l * (-1) := mul_le_mul_of_nonneg_left (by omega) (by omega)
      omega
    · exact hkc
    · have : l * 1 ≤ l * k := mul_le_mul_of_nonneg_left (by omega) (by omega)
      omega
  rw [hk0] at hk
  omega

/-- **The modular difference set explicitly.**  `B − B ⊆ ZMod l` is `0`
together with the residues of the positive differences of `A₀ = A ∖ {l}` and
their reflections `l − P`. -/
theorem modIm_sub_self_eq {A : Finset ℤ} {l : ℤ}
    (h0 : 0 ∈ A) (hl0 : 0 < l)
    (hmin : ∀ a ∈ A, 0 ≤ a) (hmax : ∀ a ∈ A, a ≤ l) :
    ((modIm A l).image₂ (· - ·) (modIm A l)) =
      insert 0 ((posDiff (A.erase l) ∪
        (posDiff (A.erase l)).image (l - ·)).image
          (fun x : ℤ => (x : ZMod l.toNat))) := by
  classical
  have hcastl : ((l : ℤ) : ZMod l.toNat) = 0 := by
    have e : ((l.toNat : ℤ) : ZMod l.toNat) = 0 := by
      rw [Int.cast_natCast]; exact ZMod.natCast_self _
    rwa [Int.toNat_of_nonneg (le_of_lt hl0)] at e
  ext r
  simp only [modIm, Finset.mem_image₂, Finset.mem_image, Finset.mem_insert,
    Finset.mem_union, mem_posDiff, Finset.mem_erase]
  constructor
  · rintro ⟨b₁, ⟨a₁, ⟨ha₁l, ha₁⟩, rfl⟩, b₂, ⟨a₂, ⟨ha₂l, ha₂⟩, rfl⟩, rfl⟩
    have ha₁0 := hmin a₁ ha₁
    have ha₁lt : a₁ < l := lt_of_le_of_ne (hmax a₁ ha₁) ha₁l
    have ha₂0 := hmin a₂ ha₂
    have ha₂lt : a₂ < l := lt_of_le_of_ne (hmax a₂ ha₂) ha₂l
    rcases lt_trichotomy a₁ a₂ with h | h | h
    · -- `a₁ < a₂`: the residue is that of `l − (a₂ − a₁) ∈ l − P`.
      right
      refine ⟨l - (a₂ - a₁), Or.inr
        ⟨a₂ - a₁, ⟨⟨a₂, ⟨ha₂l, ha₂⟩, a₁, ⟨ha₁l, ha₁⟩, rfl⟩, by omega⟩,
          by ring⟩, ?_⟩
      rw [Int.cast_sub, Int.cast_sub, hcastl]
      ring
    · -- `a₁ = a₂`: the residue is `0`.
      subst h
      left
      simp
    · -- `a₂ < a₁`: the residue is that of `a₁ − a₂ ∈ P`.
      right
      exact ⟨a₁ - a₂, Or.inl
        ⟨⟨a₁, ⟨ha₁l, ha₁⟩, a₂, ⟨ha₂l, ha₂⟩, rfl⟩, by omega⟩,
        Int.cast_sub _ _⟩
  · rintro (rfl | ⟨x, hx, rfl⟩)
    · -- `0 = 0 − 0`.
      refine ⟨_, ⟨0, ⟨ne_of_lt hl0, h0⟩, rfl⟩, _, ⟨0, ⟨ne_of_lt hl0, h0⟩, rfl⟩, ?_⟩
      simp
    · rcases hx with hxP | hxP
      · -- `x = a₁ − a₂ ∈ P` has residue `↑a₁ − ↑a₂`.
        obtain ⟨⟨a₁, ⟨ha₁l, ha₁⟩, a₂, ⟨ha₂l, ha₂⟩, rfl⟩, -⟩ := hxP
        exact ⟨(a₁ : ZMod l.toNat), ⟨a₁, ⟨ha₁l, ha₁⟩, rfl⟩,
          (a₂ : ZMod l.toNat), ⟨a₂, ⟨ha₂l, ha₂⟩, rfl⟩, (Int.cast_sub _ _).symm⟩
      · -- `x = l − (a₁ − a₂)` has residue `↑a₂ − ↑a₁`.
        obtain ⟨d, ⟨⟨a₁, ⟨ha₁l, ha₁⟩, a₂, ⟨ha₂l, ha₂⟩, rfl⟩, -⟩, rfl⟩ := hxP
        refine ⟨(a₂ : ZMod l.toNat), ⟨a₂, ⟨ha₂l, ha₂⟩, rfl⟩,
          (a₁ : ZMod l.toNat), ⟨a₁, ⟨ha₁l, ha₁⟩, rfl⟩, ?_⟩
        have : ((l - (a₁ - a₂) : ℤ) : ZMod l.toNat) = -((a₁ : ZMod l.toNat) - a₂) := by
          rw [Int.cast_sub, Int.cast_sub, hcastl, zero_sub]
        rw [this]
        ring

/-- **Exact fiber identity for the difference set**, sharpening
`card_sub_self_ge_zmod`.  For `A ⊆ [0, l]` containing `0` and `l`, writing
`B = modIm A l` and `P_A = (A − A) ∩ (0, l)`,

  `|A − A| = |B − B| + |P_A ∩ (l − P_A)| + 2`.

Here `P_A ∩ (l − P_A)` is (the `(0, l)`-lift of) the set of nonzero classes
of `B − B` realised by integer differences in *both* directions; it contains
the lift `A₀' ∪ (l − A₀')` of `(B ∪ −B) ∖ {0}`, whence
`card_sub_self_ge_zmod` as a corollary.  Any sharpening of the residual
bound lives exactly in the extra both-direction classes
`P_A ∩ (l − P_A) ∖ (A₀' ∪ (l − A₀'))`. -/
theorem card_sub_self_eq_zmod_fiber {A : Finset ℤ} {l : ℤ}
    (h0 : 0 ∈ A) (hl : l ∈ A) (hl0 : 0 < l)
    (hmin : ∀ a ∈ A, 0 ≤ a) (hmax : ∀ a ∈ A, a ≤ l) :
    (A.image₂ (· - ·) A).card =
      ((modIm A l).image₂ (· - ·) (modIm A l)).card +
        (((posDiff A).filter (· < l)) ∩
          ((posDiff A).filter (· < l)).image (l - ·)).card + 2 := by
  classical
  set PA := (posDiff A).filter (· < l) with hPAdef
  set P := posDiff (A.erase l) with hPdef
  set Q := ((A.erase l).erase 0).image (l - ·) with hQdef
  have hAA := card_image2_sub_self_eq h0 hl hl0 hmin hmax
  have hPA : PA = P ∪ Q := posDiff_filter_lt_eq hl hmin hmax
  -- `A₀' ⊆ P`: every nonzero `a ∈ A₀` is the difference `a − 0`.
  have hA₀'P : (A.erase l).erase 0 ⊆ P := by
    intro a ha
    obtain ⟨ha0, ha'⟩ := Finset.mem_erase.1 ha
    obtain ⟨hal, haA⟩ := Finset.mem_erase.1 ha'
    refine mem_posDiff.2 ⟨⟨a, Finset.mem_erase.2 ⟨hal, haA⟩, 0,
      Finset.mem_erase.2 ⟨ne_of_lt hl0, h0⟩, by ring⟩, ?_⟩
    have := hmin a haA
    omega
  -- `Q ⊆ l − P` since `A₀' ⊆ P`.
  have hQsub : Q ⊆ P.image (l - ·) := Finset.image_subset_image hA₀'P
  -- `l − Q = A₀'` (reflection is an involution).
  have hQQ : Q.image (l - ·) = (A.erase l).erase 0 := by
    rw [hQdef]
    ext y
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨x, ⟨z, hz, rfl⟩, rfl⟩
      have hz' : l - (l - z) = z := by ring
      rwa [hz']
    · intro hy
      exact ⟨l - y, ⟨y, hy, rfl⟩, by ring⟩
  -- `Z := PA ∪ (l − PA) = P ∪ (l − P)`.
  have hZ : PA ∪ PA.image (l - ·) = P ∪ P.image (l - ·) := by
    rw [hPA, Finset.image_union, hQQ]
    ext x
    simp only [Finset.mem_union]
    constructor
    · rintro ((h | h) | (h | h))
      · exact Or.inl h
      · exact Or.inr (hQsub h)
      · exact Or.inr h
      · exact Or.inl (hA₀'P h)
    · rintro (h | h)
      · exact Or.inl (Or.inl h)
      · exact Or.inr (Or.inl h)
  -- `Z ⊆ (0, l)`.
  have hZsub : ∀ x ∈ P ∪ P.image (l - ·), 0 < x ∧ x < l := by
    intro x hx
    rcases Finset.mem_union.1 hx with hx | hx
    · obtain ⟨⟨a, ha, b, hb, rfl⟩, hpos⟩ := mem_posDiff.1 hx
      obtain ⟨hal, haA⟩ := Finset.mem_erase.1 ha
      have hb0 := hmin b (Finset.mem_erase.1 hb).2
      have halt := lt_of_le_of_ne (hmax a haA) hal
      exact ⟨hpos, by omega⟩
    · obtain ⟨d, hd, rfl⟩ := Finset.mem_image.1 hx
      obtain ⟨⟨a, ha, b, hb, rfl⟩, hpos⟩ := mem_posDiff.1 hd
      obtain ⟨hal, haA⟩ := Finset.mem_erase.1 ha
      obtain ⟨hbl, hbA⟩ := Finset.mem_erase.1 hb
      have hb0 := hmin b hbA
      have halt := lt_of_le_of_ne (hmax a haA) hal
      have hblt := lt_of_le_of_ne (hmax b hbA) hbl
      exact ⟨by omega, by omega⟩
  -- `0 ∉ π Z` since `Z ⊆ (0, l)`.
  have h0not : (0 : ZMod l.toNat) ∉
      (P ∪ P.image (l - ·)).image (fun x : ℤ => (x : ZMod l.toNat)) := by
    intro h
    obtain ⟨x, hx, hx0⟩ := Finset.mem_image.1 h
    obtain ⟨hx0', hxl'⟩ := hZsub x hx
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hx0
    rw [Int.toNat_of_nonneg (le_of_lt hl0)] at hx0
    obtain ⟨k, hk⟩ := hx0
    rcases lt_trichotomy k 0 with hkc | hkc | hkc
    · have : l * k ≤ l * (-1) := mul_le_mul_of_nonneg_left (by omega) (by omega)
      omega
    · subst hkc
      omega
    · have : l * 1 ≤ l * k := mul_le_mul_of_nonneg_left (by omega) (by omega)
      omega
  -- `|B − B| = |Z| + 1`.
  have hBBcard : ((modIm A l).image₂ (· - ·) (modIm A l)).card =
      (P ∪ P.image (l - ·)).card + 1 := by
    rw [modIm_sub_self_eq h0 hl0 hmin hmax,
      Finset.card_insert_of_notMem h0not,
      Finset.card_image_of_injOn
        ((intCast_injOn_Ioo hl0).mono (fun x hx => hZsub x hx))]
  -- `|PA| + |l − PA| = |Z| + |PA ∩ (l − PA)|`.
  have hfin : PA.card + (PA.image (l - ·)).card =
      (P ∪ P.image (l - ·)).card + (PA ∩ PA.image (l - ·)).card := by
    have h := Finset.card_union_add_card_inter PA (PA.image (l - ·))
    rw [hZ] at h
    omega
  have himg : (PA.image (l - ·)).card = PA.card :=
    Finset.card_image_of_injective _ (fun a b h => by omega)
  rw [← hPAdef] at hAA
  omega

/-- **Generation descends to `A₀`.** If the differences of `A` are not all
divisible by `d`, and `d ∣ l`, then already `A₀ = A ∖ {l}` has a pair of
elements with difference not divisible by `d`. -/
theorem exists_not_dvd_sub_of_erase {A : Finset ℤ} {l : ℤ}
    (h0 : 0 ∈ A) (hl0 : 0 < l)
    (hgcd : ∀ d : ℤ, 2 ≤ d → ∃ x ∈ A, ∃ y ∈ A, ¬ d ∣ x - y)
    {d : ℤ} (hd2 : 2 ≤ d) (hdl : d ∣ l) :
    ∃ x ∈ A.erase l, ∃ y ∈ A.erase l, ¬ d ∣ x - y := by
  have h0e : (0 : ℤ) ∈ A.erase l := Finset.mem_erase.2 ⟨ne_of_lt hl0, h0⟩
  by_contra h
  push Not at h
  -- All elements of `A.erase l` are divisible by `d`, hence so are all of `A`.
  have hdA : ∀ a ∈ A, d ∣ a := by
    intro a ha
    by_cases hal : a = l
    · rwa [hal]
    · have h' := h a (Finset.mem_erase.2 ⟨hal, ha⟩) 0 h0e
      rwa [sub_zero] at h'
  obtain ⟨x, hx, y, hy, hxy⟩ := hgcd d hd2
  exact hxy ((hdA x hx).sub (hdA y hy))

/-- **The residual case of Freiman's `3k − 4` difference bound**, assuming
the cyclic Kneser consequence `ZModKneserBound`. -/
theorem freiman3k4Residual (hK : ZModKneserBound) : Freiman3k4Residual := by
  classical
  intro A l h0 hl hmem hgcd hk hmf
  have hmin : ∀ x ∈ A, 0 ≤ x := fun x hx => (hmem x hx).1
  have hmax : ∀ x ∈ A, x ≤ l := fun x hx => (hmem x hx).2
  have hne : A.Nonempty := ⟨0, h0⟩
  -- `0 < l`: otherwise `A = {0}` and the `minFac` hypothesis is `2 ≤ −2`.
  have hl0 : 0 < l := by
    have hll := hmin l hl
    rcases lt_or_eq_of_le hll with hlt | heq
    · exact hlt
    · -- `l = 0`: `A ⊆ {0}` so `|A| = 1` and `minFac 0 = 2 ≤ −2`, absurd.
      have hlz : l = 0 := heq.symm
      have hA : A = {0} := by
        apply Finset.eq_of_subset_of_card_le
        · intro a ha
          have h1 := hmin a ha
          have h2 := hmax a ha
          simp only [Finset.mem_singleton]
          omega
        · exact Finset.card_le_card (Finset.singleton_subset_iff.2 h0)
      rw [hA, hlz] at hmf
      simp only [Finset.card_singleton, Nat.cast_one, Int.toNat_zero,
        Nat.minFac_zero, Nat.cast_ofNat] at hmf
      omega
  have h0A₀ : (0 : ℤ) ∈ A.erase l := Finset.mem_erase.2 ⟨ne_of_lt hl0, h0⟩
  have hmemA₀ : ∀ x ∈ A.erase l, 0 ≤ x ∧ x < l := by
    intro x hx
    obtain ⟨hxl, hxA⟩ := Finset.mem_erase.1 hx
    exact ⟨hmin x hxA, lt_of_le_of_ne (hmax x hxA) hxl⟩
  have hcardA₀ : ((A.erase l).card : ℤ) = (A.card : ℤ) - 1 := by
    have h1 : (A.erase l).card = A.card - 1 := Finset.card_erase_of_mem hl
    have h2 : 1 ≤ A.card := Finset.card_pos.2 hne
    omega
  have h2A₀ : 2 * ((A.erase l).card : ℤ) ≤ l := by omega
  have hgen : ∀ d : ℤ, 2 ≤ d → d ∣ l →
      ∃ x ∈ A.erase l, ∃ y ∈ A.erase l, ¬ d ∣ x - y :=
    fun d hd2 hdl => exists_not_dvd_sub_of_erase h0 hl0 hgcd hd2 hdl
  -- The Kneser bound at `A₀` gives `3(|A₀| − 1) ≤ 2|P_A|`.
  have hbound := hK l (A.erase l) hl0 h0A₀ hmemA₀ h2A₀ hgen
  have hPA := posDiff_filter_lt_eq hl hmin hmax
  rw [← hPA] at hbound
  -- `|A − A| = 2|P_A| + 3 ≥ 3(|A₀| − 1) + 3 = 3|A| − 3`.
  have hAA : ((A.image₂ (· - ·) A).card : ℤ) =
      2 * (((posDiff A).filter (· < l)).card : ℤ) + 3 := by
    exact_mod_cast card_image2_sub_self_eq h0 hl hl0 hmin hmax
  omega

end JSP000728
