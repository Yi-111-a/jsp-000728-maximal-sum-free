/-
# A second proof of the cyclic Kneser bound `ZModKneserBound`

For `A₀ ⊆ [0, l)` containing `0` with `2|A₀| ≤ l` and generating difference
set, the goal is

  `3(|A₀| − 1) ≤ 2·|posDiff(A₀) ∪ (l − A₀')|`.

Writing `A = A₀ ∪ {l}` and `P = (A − A) ∩ (0, l) = posDiff(A₀) ∪ (l − A₀')`,
the exact fiber identity `card_sub_self_eq_zmod_fiber` gives
`|A − A| = |B − B| + |P ∩ (l − P)| + 2`, so the goal is equivalent to

  `|B − B| + |P ∩ (l − P)| ≥ 3|B| − 2`,

where `B = modIm A l ⊆ ZMod l` has `|B| = |A₀|`.  The both-direction set
`P ∩ (l − P)` contains the lift `A₀' ∪ (l − A₀')` of `(B ∪ −B) ∖ {0}`, of
size `|B ∪ −B| − 1 ≥ |B| − 1` (`card_fiber_ge_card_union_neg`).  Hence:

* if `B − B` is aperiodic, Kneser gives `|B − B| ≥ 2|B| − 1` and the two
  bounds sum to `≥ 3|B| − 2`;
* if `B − B = univ`, then `|B − B| = l ≥ 2|B|`, again sufficient.

The remaining *periodic* case (`B − B` proper with nontrivial stabilizer) is
isolated as the hypothesis `PeriodicMarginal`, and
`zmodKneserBound' : PeriodicMarginal → ZModKneserBound`.
-/

import JSPProblem.FreimanResidual
import JSPProblem.KneserZMod

namespace JSP000728

open Finset
open scoped Pointwise

section Setup

variable {l : ℤ} {A₀ : Finset ℤ}

/-- The reflected-image set `U = A₀' ∪ (l − A₀')` is contained in the
both-direction fiber set `P ∩ (l − P)`. -/
lemma erase_union_image_sub_subset_inter (_hl : 0 < l) (h0 : 0 ∈ A₀)
    (hmem : ∀ x ∈ A₀, 0 ≤ x ∧ x < l) :
    (A₀.erase 0) ∪ ((A₀.erase 0).image (l - ·)) ⊆
      (posDiff A₀ ∪ (A₀.erase 0).image (l - ·)) ∩
        ((posDiff A₀ ∪ (A₀.erase 0).image (l - ·)).image (l - ·)) := by
  intro d hd
  rw [Finset.mem_union] at hd
  refine Finset.mem_inter.2 ⟨?_, ?_⟩
  · rcases hd with hd | hd
    · obtain ⟨hd0, hdA⟩ := Finset.mem_erase.1 hd
      have hpos : 0 < d := by
        have := (hmem d hdA).1
        omega
      exact Finset.mem_union.2 (Or.inl
        (mem_posDiff.2 ⟨⟨d, hdA, 0, h0, by ring⟩, hpos⟩))
    · obtain ⟨a', ha', rfl⟩ := Finset.mem_image.1 hd
      exact Finset.mem_union.2 (Or.inr (Finset.mem_image.2 ⟨a', ha', rfl⟩))
  · rw [Finset.mem_image]
    rcases hd with hd | hd
    · obtain ⟨hd0, hdA⟩ := Finset.mem_erase.1 hd
      exact ⟨l - d, Finset.mem_union.2
        (Or.inr (Finset.mem_image.2 ⟨d, hd, rfl⟩)), by ring⟩
    · obtain ⟨a', ha', rfl⟩ := Finset.mem_image.1 hd
      obtain ⟨ha'0, ha'A⟩ := Finset.mem_erase.1 ha'
      have hpos : 0 < a' := by
        have := (hmem a' ha'A).1
        omega
      exact ⟨a', Finset.mem_union.2 (Or.inl
        (mem_posDiff.2 ⟨⟨a', ha'A, 0, h0, by ring⟩, hpos⟩)), by ring⟩

/-- The modular image of `U = A₀' ∪ (l − A₀')` in `ZMod l` is exactly
`(B ∪ −B) ∖ {0}` for `B = A₀` cast into `ZMod l`. -/
lemma image_cast_erase_union_eq (hl : 0 < l)
    (hmem : ∀ x ∈ A₀, 0 ≤ x ∧ x < l) :
    ((A₀.erase 0) ∪ ((A₀.erase 0).image (l - ·))).image
        (fun x : ℤ => (x : ZMod l.toNat)) =
      ((A₀.image (fun x : ℤ => (x : ZMod l.toNat))) ∪
        -(A₀.image (fun x : ℤ => (x : ZMod l.toNat)))).erase 0 := by
  classical
  have hcastl : ((l : ℤ) : ZMod l.toNat) = 0 := by
    have e : ((l.toNat : ℤ) : ZMod l.toNat) = 0 := by
      rw [Int.cast_natCast]; exact ZMod.natCast_self _
    rwa [Int.toNat_of_nonneg (le_of_lt hl)] at e
  have hne0 : ∀ x ∈ A₀, ((x : ℤ) : ZMod l.toNat) ≠ 0 → x ≠ 0 := by
    intro x hx h hx0
    rw [hx0] at h
    simp at h
  have hcast_ne0 : ∀ x ∈ A₀, x ≠ 0 → ((x : ℤ) : ZMod l.toNat) ≠ 0 := by
    intro x hxA hx0 h
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h
    rw [Int.toNat_of_nonneg (le_of_lt hl)] at h
    obtain ⟨c, hc⟩ := h
    have hx0' := (hmem x hxA).1
    have hxl' := (hmem x hxA).2
    rcases lt_trichotomy c 0 with hc' | hc' | hc'
    · have : l * c ≤ l * (-1) := mul_le_mul_of_nonneg_left (by omega) (by omega)
      omega
    · subst hc'; omega
    · have : l * 1 ≤ l * c := mul_le_mul_of_nonneg_left (by omega) (by omega)
      omega
  ext r
  simp only [Finset.mem_image, Finset.mem_union, Finset.mem_erase, Finset.mem_neg]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases hx with ⟨hx0, hxA⟩ | ⟨a', ⟨ha'0, ha'A⟩, rfl⟩
    · -- `x = a' ∈ A₀'`: image is `a' ∈ B`, nonzero.
      exact ⟨hcast_ne0 x hxA hx0, Or.inl ⟨x, hxA, rfl⟩⟩
    · -- `x = l − a'`: image is `−a' ∈ −B`, nonzero.
      have hne : ((l - a' : ℤ) : ZMod l.toNat) = -(a' : ZMod l.toNat) := by
        rw [Int.cast_sub, hcastl, zero_sub]
      have hz : ((l - a' : ℤ) : ZMod l.toNat) ≠ 0 := by
        rw [hne, neg_ne_zero]
        exact hcast_ne0 a' ha'A ha'0
      exact ⟨hz, Or.inr ⟨(a' : ZMod l.toNat), ⟨a', ha'A, rfl⟩, hne.symm⟩⟩
  · rintro ⟨hr0, hr | ⟨b, ⟨a, ha, rfl⟩, rfl⟩⟩
    · -- `r = a' ∈ B ∖ {0}`: lift to `a' ∈ A₀'`.
      obtain ⟨a, haA, rfl⟩ := hr
      exact ⟨a, Or.inl ⟨hne0 a haA hr0, haA⟩, rfl⟩
    · -- `r = −a'`: lift to `l − a'`.
      refine ⟨l - a, Or.inr ⟨a, ⟨hne0 a ha ?_, ha⟩, rfl⟩, ?_⟩
      · intro hz
        rw [hz] at hr0
        simp at hr0
      · rw [Int.cast_sub, hcastl, zero_sub]

/-- The both-direction fiber count: `|P ∩ (l − P)| ≥ |B ∪ −B| − 1` where
`B = A₀ ⊆ ZMod l` and `P = posDiff(A₀) ∪ (l − A₀')`. -/
lemma card_fiber_ge_card_union_neg (hl : 0 < l) (h0 : 0 ∈ A₀)
    (hmem : ∀ x ∈ A₀, 0 ≤ x ∧ x < l) :
    (((A₀.image (fun x : ℤ => (x : ZMod l.toNat))) ∪
        -(A₀.image (fun x : ℤ => (x : ZMod l.toNat)))).card : ℤ) - 1 ≤
      ((posDiff A₀ ∪ (A₀.erase 0).image (l - ·)) ∩
        ((posDiff A₀ ∪ (A₀.erase 0).image (l - ·)).image (l - ·))).card := by
  classical
  set U := (A₀.erase 0) ∪ ((A₀.erase 0).image (l - ·)) with hUdef
  set B := A₀.image (fun x : ℤ => (x : ZMod l.toNat)) with hBdef
  -- `U ⊆ (0, l)`, where the cast is injective.
  have hUsub : ∀ x ∈ U, 0 < x ∧ x < l := by
    intro x hx
    rw [hUdef, Finset.mem_union] at hx
    rcases hx with hx | hx
    · obtain ⟨hx0, hxA⟩ := Finset.mem_erase.1 hx
      have h1 := (hmem x hxA).1
      have h2 := (hmem x hxA).2
      exact ⟨by omega, h2⟩
    · obtain ⟨a', ha', rfl⟩ := Finset.mem_image.1 hx
      obtain ⟨ha'0, ha'A⟩ := Finset.mem_erase.1 ha'
      have h1 := (hmem a' ha'A).1
      have h2 := (hmem a' ha'A).2
      exact ⟨by omega, by omega⟩
  have hinj : Set.InjOn (fun x : ℤ => (x : ZMod l.toNat)) U :=
    (intCast_injOn_Ioo hl).mono (fun x hx => hUsub x hx)
  have hcardU : (U.image (fun x : ℤ => (x : ZMod l.toNat))).card = U.card :=
    Finset.card_image_of_injOn hinj
  have himg : U.image (fun x : ℤ => (x : ZMod l.toNat)) = (B ∪ -B).erase 0 := by
    rw [hUdef, hBdef]
    exact image_cast_erase_union_eq hl hmem
  have h0mem : (0 : ZMod l.toNat) ∈ B ∪ -B := by
    exact Finset.mem_union.2 (Or.inl (Finset.mem_image.2 ⟨0, h0, by simp⟩))
  have hcard : U.card = (B ∪ -B).card - 1 := by
    rw [← hcardU, himg, Finset.card_erase_of_mem h0mem]
  have hle := Finset.card_le_card (erase_union_image_sub_subset_inter hl h0 hmem)
  have hcardpos : 1 ≤ (B ∪ -B).card := Finset.card_pos.2 ⟨0, h0mem⟩
  rw [hcard] at hle
  calc (((B ∪ -B).card : ℤ) - 1)
      = (((B ∪ -B).card - 1 : ℕ) : ℤ) := by
        rw [Nat.cast_sub hcardpos]; push_cast; ring
    _ ≤ ((posDiff A₀ ∪ (A₀.erase 0).image (l - ·)) ∩
        ((posDiff A₀ ∪ (A₀.erase 0).image (l - ·)).image (l - ·))).card := by
        exact_mod_cast hle

end Setup

/-! ### The periodic residual case and the main reduction -/

/-- **The periodic marginal case.**  `ZModKneserBound` restricted to the
configurations where the modular difference set `B − B` (for
`B = A₀ ⊆ ZMod l`) is genuinely periodic: its stabilizer `addStab` is
nontrivial and `B − B ≠ ZMod l`.  The clean cases are proved outright in
`zmodKneserBound'`; this Prop packages the inverse-theoretic content of the
periodic case. -/
def PeriodicMarginal : Prop :=
  ∀ (l : ℤ) (A₀ : Finset ℤ),
    0 < l → 0 ∈ A₀ → (∀ x ∈ A₀, 0 ≤ x ∧ x < l) →
    2 * (A₀.card : ℤ) ≤ l →
    (∀ d : ℤ, 2 ≤ d → d ∣ l → ∃ x ∈ A₀, ∃ y ∈ A₀, ¬ d ∣ x - y) →
    ((A₀.image (fun x : ℤ => (x : ZMod l.toNat))).image₂ (· - ·)
        (A₀.image (fun x : ℤ => (x : ZMod l.toNat)))).addStab ≠ 0 →
    ((A₀.image (fun x : ℤ => (x : ZMod l.toNat))).image₂ (· - ·)
        (A₀.image (fun x : ℤ => (x : ZMod l.toNat)))).card < l.toNat →
    3 * ((A₀.card : ℤ) - 1) ≤
      2 * (posDiff A₀ ∪ (A₀.erase 0).image (l - ·)).card

/-- **Reduction of `ZModKneserBound` to the periodic marginal case.**

Let `A = A₀ ∪ {l}` and `B = A₀ ⊆ ZMod l` (the cast is injective on `A₀`).
With `P = posDiff(A₀) ∪ (l − A₀')` and `T = P ∩ (l − P)`:

* `|A − A| = 2·|P| + 3` and `|A − A| = |B − B| + |T| + 2`
  (`card_image2_sub_self_eq`, `card_sub_self_eq_zmod_fiber`), so the goal is
  `|B − B| + |T| ≥ 3|B| − 2`.
* `|T| ≥ |B ∪ −B| − 1 ≥ |B| − 1` (`card_fiber_ge_card_union_neg`).
* If `(B − B).addStab = 0`, Kneser gives `|B − B| ≥ 2|B| − 1`, done.
* If `|B − B| = l`, then `|B − B| + |T| ≥ l + |B| − 1 ≥ 3|B| − 1`, done.
* Otherwise `B − B` is periodic and proper — the `PeriodicMarginal`
  hypothesis. -/
theorem zmodKneserBound' (hpm : PeriodicMarginal) : ZModKneserBound := by
  classical
  intro l A₀ hl h0 hmem h2 hgen
  -- The ambient set `A = insert l A₀`.
  set A : Finset ℤ := insert l A₀ with hAdef
  have hlnA : l ∉ A₀ := by
    intro h
    have := (hmem l h).2
    omega
  have hAerase : A.erase l = A₀ := by
    rw [hAdef]
    exact Finset.erase_insert hlnA
  have h0A : (0 : ℤ) ∈ A := Finset.mem_insert.2 (Or.inr h0)
  have hlA : l ∈ A := Finset.mem_insert_self _ _
  have hminA : ∀ x ∈ A, 0 ≤ x := by
    intro x hx
    rcases Finset.mem_insert.1 hx with rfl | hx
    · omega
    · exact (hmem x hx).1
  have hmaxA : ∀ x ∈ A, x ≤ l := by
    intro x hx
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact le_refl _
    · exact le_of_lt (hmem x hx).2
  -- The positive-difference set `P` and the two cardinality identities.
  set P := (posDiff A).filter (· < l) with hPdef
  have hPA : P = posDiff A₀ ∪ (A₀.erase 0).image (l - ·) := by
    rw [hPdef, posDiff_filter_lt_eq hlA hminA hmaxA, hAerase]
  have hAA : ((A.image₂ (· - ·) A).card : ℤ) = 2 * (P.card : ℤ) + 3 := by
    exact_mod_cast card_image2_sub_self_eq h0A hlA hl hminA hmaxA
  have hAAz : ((A.image₂ (· - ·) A).card : ℤ) =
      ((modIm A l).image₂ (· - ·) (modIm A l)).card +
        (P ∩ P.image (l - ·)).card + 2 := by
    have h := card_sub_self_eq_zmod_fiber h0A hlA hl hminA hmaxA
    rw [← hPdef] at h
    exact_mod_cast h
  -- `B = A₀` in `ZMod l`, `|B| = k`.
  set B := A₀.image (fun x : ℤ => (x : ZMod l.toNat)) with hBdef
  have hBeq : modIm A l = B := by
    rw [modIm, hAerase, hBdef]
  have hBcard : (B.card : ℤ) = A₀.card := by
    have h := card_zmod_image_eq_card_erase hlA hl hminA hmaxA
    rw [hAerase] at h
    have hcardA : A.card = A₀.card + 1 := by
      rw [hAdef, Finset.card_insert_of_notMem hlnA]
    rw [hcardA] at h
    have : (A₀.card + 1 - 1 : ℕ) = A₀.card := Nat.add_sub_cancel _ _
    rw [this] at h
    rw [hBdef]
    exact_mod_cast h
  -- `modIm A l` is literally `B`, so `B − B` is the `image₂` in `hAAz`.
  rw [hBeq] at hAAz
  -- The sufficient inequality: `|B − B| + |T| ≥ 3k − 2`.
  have hTge : (B.card : ℤ) - 1 ≤ (P ∩ P.image (l - ·)).card := by
    have h := card_fiber_ge_card_union_neg hl h0 hmem
    rw [← hPA] at h
    have hle : B ⊆ B ∪ -B := Finset.subset_union_left
    have hcardle : B.card ≤ (B ∪ -B).card := Finset.card_le_card hle
    calc ((B.card : ℤ) - 1)
        ≤ (((B ∪ -B).card : ℤ) - 1) := by omega
      _ ≤ (P ∩ P.image (l - ·)).card := h
  -- It suffices to show `|B − B| + |T| ≥ 3k − 2`.
  suffices hkey : 3 * (A₀.card : ℤ) - 2 ≤
      (B.image₂ (· - ·) B).card + (P ∩ P.image (l - ·)).card by
    have hk : (A₀.card : ℤ) = B.card := hBcard.symm
    rw [← hPA]
    omega
  -- Case split on the stabilizer / size of `B − B`.
  by_cases hstab : (B.image₂ (· - ·) B).addStab = 0
  · -- Aperiodic case: `|B − B| ≥ 2|B| − 1` and `|T| ≥ |B| − 1`.
    have hBne : B.Nonempty := ⟨0, Finset.mem_image.2 ⟨0, h0, by simp⟩⟩
    have hBB : 2 * B.card - 1 ≤ (B.image₂ (· - ·) B).card :=
      Finset.two_mul_card_sub_one_le_card_sub_of_addStab_eq_zero hBne hstab
    omega
  · by_cases hfull : (B.image₂ (· - ·) B).card = l.toNat
    · -- `B − B = univ`: `|B − B| = l ≥ 2|B|`.
      have hlcard : (l.toNat : ℤ) = l := Int.toNat_of_nonneg (le_of_lt hl)
      omega
    · -- The periodic marginal case.
      have hnz : NeZero l.toNat := ⟨by omega⟩
      have hle : (B.image₂ (· - ·) B).card ≤ l.toNat := by
        have hle' := Finset.card_le_card (Finset.subset_univ (B.image₂ (· - ·) B))
        rwa [Finset.card_univ, ZMod.card] at hle'
      have hlt : (B.image₂ (· - ·) B).card < l.toNat :=
        lt_of_le_of_ne hle hfull
      have hmarg := hpm l A₀ hl h0 hmem h2 hgen hstab hlt
      rw [← hPA] at hmarg
      omega

end JSP000728
