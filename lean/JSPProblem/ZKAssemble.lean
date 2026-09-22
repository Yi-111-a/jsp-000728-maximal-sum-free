/-
# Assembly of `ZKTightCount`: the tight periodic fibre count

This file closes `ZKTightCount` — the residual inequality
`|S| + |T| ≥ 3|A₀| − 2` for the tight Kneser periodic case — using the
coset-charge machinery of `ZKTightAttack` and the missing-coset existence of
`ZKMissing`.

## The argument

Write `B = A₀ ⊆ ZMod l`, `S = B − B`, `H = S.addStab`, `h = |H|` and
`|B + H| = ht`.  Tightness gives `|S| = h(2t − 1)`.  With `η = ht − k` the
number of *holes* in the occupied `H`-cosets, the goal is equivalent to

  `|T| ≥ (k − 1) + (h − 1 − η)`.

* The free fibres `A₀ ∖ {0} ⊆ T` supply `k − 1`.
* Since `t ≥ 2` (the missing-coset lemma `zk_exists_missing_coset`),
  `|B̄ − B̄| = 2t − 1 > t = |B̄|` in the quotient by `H`, so some difference
  coset `(b − c) + H` is *unoccupied*: `b − c ∉ B + H`
  (`zk_exists_unoccupied_diff_coset`).
* The charge lemma `zk_cosDiff_charge_fiber` gives at least
  `f_b + f_c − h − 1` both-direction fibres in the integer lift `K` of that
  coset; all of them are *new* (their residues lie outside `B`, hence they
  are not in `A₀`).
* Since `f_b + f_c − h − 1 = h − 1 − (η_b + η_c) ≥ h − 1 − η`
  (the holes of two distinct cosets sum to at most the total `η`), the
  fibres combine to `|T| ≥ k − 1 + h − 1 − η`, and

  `|S| + |T| ≥ h(2t − 1) + k + h − 2 − η = 3k − 2 + η ≥ 3k − 2`.

No case split is needed: when `η ≥ h − 1` the charge bound is nonpositive
and the free fibres alone already suffice.

## Main declarations

* `intCast_emod_self` — `↑(x % l) = ↑x` in `ZMod l`.
* `modTranslate_subset_valImage` — an `H`-coset lift lands in the `val`-image
  of `B + H`.
* `zk_exists_unoccupied_diff_coset` — existence of a difference coset
  disjoint from `B + H`.
* `zkTightCount` — the theorem.
-/

import JSPProblem.ZKMissing
import JSPProblem.ZKTightAttack

namespace JSP000728

open Finset
open scoped Pointwise

section Assemble

variable {l : ℤ} {A₀ : Finset ℤ}

/-- `(x % l)` and `x` coincide in `ZMod l`. -/
theorem intCast_emod_self (hl : 0 < l) (x : ℤ) :
    ((x % l : ℤ) : ZMod l.toNat) = (x : ZMod l.toNat) := by
  have hcastl : ((l : ℤ) : ZMod l.toNat) = 0 := by
    have e : ((l.toNat : ℤ) : ZMod l.toNat) = 0 := by
      rw [Int.cast_natCast]
      exact ZMod.natCast_self _
    rwa [Int.toNat_of_nonneg (le_of_lt hl)] at e
  conv_rhs => rw [← Int.emod_add_ediv_mul x l]
  rw [Int.cast_add, Int.cast_mul, hcastl, zero_mul, add_zero]

/-- `x ∈ [0, l)` equals `val` of its cast to `ZMod l`. -/
theorem val_intCast_of_mem_Ico (hl : 0 < l) {x : ℤ} (hx0 : 0 ≤ x) (hxl : x < l) :
    (((x : ℤ) : ZMod l.toNat).val : ℤ) = x := by
  have hlN : NeZero l.toNat := by
    have hcastl : (l.toNat : ℤ) = l := Int.toNat_of_nonneg (le_of_lt hl)
    exact ⟨fun h => by rw [h, Nat.cast_zero] at hcastl; omega⟩
  have hv := ZMod.val_intCast (n := l.toNat) x
  rwa [Int.toNat_of_nonneg (le_of_lt hl), Int.emod_eq_of_lt hx0 hxl] at hv

/-- An `H`-coset lift `modTranslate l b Hint` is contained in the `val`-image
of `B + H` whenever `b` itself lies in `B`.  Here `Hint` is the integer lift
of `H` in `[0, l)`. -/
theorem modTranslate_subset_valImage (hl : 0 < l)
    {b : ℤ} (hbB : ((b : ℤ) : ZMod l.toNat) ∈ zkB l A₀) :
    modTranslate l b (hintRes l A₀) ⊆
      (zkB l A₀ + (zkS l A₀).addStab).image
        (fun x : ZMod l.toNat => (x.val : ℤ)) := by
  intro x hx
  obtain ⟨hh, hhHint, rfl⟩ := mem_modTranslate.1 hx
  have hhH := cast_mem_zkStab_of_mem_hintRes hhHint
  have hxD : ((b : ℤ) : ZMod l.toNat) + ((hh : ℤ) : ZMod l.toNat) ∈
      zkB l A₀ + (zkS l A₀).addStab :=
    Finset.mem_add.2 ⟨_, hbB, _, hhH, rfl⟩
  have hxb : 0 ≤ (b + hh) % l ∧ (b + hh) % l < l :=
    ⟨Int.emod_nonneg _ (ne_of_gt hl), Int.emod_lt_of_pos _ hl⟩
  refine Finset.mem_image.2 ⟨_, hxD, ?_⟩
  have heq : (((b + hh) % l : ℤ) : ZMod l.toNat) =
      ((b : ℤ) : ZMod l.toNat) + ((hh : ℤ) : ZMod l.toNat) := by
    rw [intCast_emod_self hl, Int.cast_add]
  have hv := val_intCast_of_mem_Ico hl hxb.1 hxb.2
  rwa [heq] at hv

/-- **The unoccupied difference coset.**  Since `t ≥ 2`, the `2t − 1`
difference cosets of `B̄` cannot all be occupied by the `t` elements of `B̄`:
some `b, c ∈ A₀` have `(b − c) ∉ B + H`.  All charged fibres in that coset
are then automatically new (not in `A₀`). -/
theorem zk_exists_unoccupied_diff_coset
    (hl : 0 < l) (h0 : 0 ∈ A₀) (hmem : ∀ x ∈ A₀, 0 ≤ x ∧ x < l)
    (hgen : ∀ d : ℤ, 2 ≤ d → d ∣ l → ∃ x ∈ A₀, ∃ y ∈ A₀, ¬ d ∣ x - y)
    (hlt : (zkS l A₀).card < l.toNat)
    (htight : (zkS l A₀).card + (zkS l A₀).addStab.card =
      2 * (zkB l A₀ + (zkS l A₀).addStab).card) :
    ∃ b ∈ A₀, ∃ c ∈ A₀,
      ((b - c : ℤ) : ZMod l.toNat) ∉ zkB l A₀ + (zkS l A₀).addStab := by
  classical
  have h0B : (0 : ZMod l.toNat) ∈ zkB l A₀ := Finset.mem_image.2 ⟨0, h0, by simp⟩
  have h0S : (0 : ZMod l.toNat) ∈ zkS l A₀ :=
    Finset.mem_image₂.2 ⟨0, h0B, 0, h0B, sub_self 0⟩
  have hSne : (zkS l A₀).Nonempty := ⟨0, h0S⟩
  have h0H : (0 : ZMod l.toNat) ∈ (zkS l A₀).addStab := zero_mem_addStab.2 hSne
  have hHpos : 0 < (zkS l A₀).addStab.card := (⟨0, h0H⟩ : _).card_pos
  obtain ⟨s, t, hsS, htB, hst, ht1⟩ := zkTight_st htight hSne
  by_contra hcon
  push_neg at hcon
  -- Every difference of `B` lands in `B + H`: then `S ⊆ B + H`.
  have hSD : zkS l A₀ ⊆ zkB l A₀ + (zkS l A₀).addStab := by
    intro x hx
    obtain ⟨u, hu, v, hv, huv⟩ := Finset.mem_image₂.1 hx
    obtain ⟨b, hbA, hbB⟩ := Finset.mem_image.1 hu
    obtain ⟨c, hcA, hcB⟩ := Finset.mem_image.1 hv
    have hmem := hcon b hbA c hcA
    rw [← hbB, ← hcB, ← Int.cast_sub] at huv
    rw [← huv]
    exact hmem
  -- So `h(2t − 1) = |S| ≤ |B + H| = ht`, forcing `t = 1` and `B ⊆ H`.
  have hcard : (zkS l A₀).card ≤ (zkB l A₀ + (zkS l A₀).addStab).card :=
    Finset.card_le_card hSD
  rw [hsS, htB] at hcard
  have hst1 : s ≤ t := Nat.le_of_mul_le_mul_left hcard hHpos
  have ht1' : t = 1 := by omega
  have hHD : (zkS l A₀).addStab ⊆ zkB l A₀ + (zkS l A₀).addStab := by
    intro x hx
    exact Finset.mem_add.2 ⟨0, h0B, x, hx, zero_add x⟩
  have hDeq : zkB l A₀ + (zkS l A₀).addStab = (zkS l A₀).addStab := by
    apply Finset.eq_of_subset_of_card_le hHD
    rw [htB, ht1', mul_one]
  have hBH : zkB l A₀ ⊆ (zkS l A₀).addStab := by
    intro x hx
    rw [← hDeq]
    exact Finset.mem_add.2 ⟨x, hx, 0, h0H, add_zero x⟩
  -- But then all differences lie in `H`, contradicting the missing coset.
  obtain ⟨b, hb, c, hc, hbc⟩ := zk_exists_missing_coset hl h0 hmem hgen hlt
  apply hbc
  rw [Int.cast_sub]
  exact sub_mem_zkStab hSne (hBH (Finset.mem_image.2 ⟨b, hb, rfl⟩))
    (hBH (Finset.mem_image.2 ⟨c, hc, rfl⟩))

/-- **The tight periodic fibre count.**  With `η = ht − k` holes and a
single unoccupied difference coset, the free fibres plus the charge give
`|T| ≥ k − 1 + h − 1 − η`, hence `|S| + |T| ≥ 3k − 2`. -/
theorem zkTightCount : ZKTightCount := by
  classical
  intro l A₀ hl h0 hmem h2 hgen hstab hlt htight
  -- Standard nonempties and numerics.
  have h0B : (0 : ZMod l.toNat) ∈ zkB l A₀ := Finset.mem_image.2 ⟨0, h0, by simp⟩
  have h0S : (0 : ZMod l.toNat) ∈ zkS l A₀ :=
    Finset.mem_image₂.2 ⟨0, h0B, 0, h0B, sub_self 0⟩
  have hSne : (zkS l A₀).Nonempty := ⟨0, h0S⟩
  have h0H : (0 : ZMod l.toNat) ∈ (zkS l A₀).addStab := zero_mem_addStab.2 hSne
  have hHpos : 0 < (zkS l A₀).addStab.card := (⟨0, h0H⟩ : _).card_pos
  have hBcard : (zkB l A₀).card = A₀.card := zkB_card hl h0 hmem
  have hBD : zkB l A₀ ⊆ zkB l A₀ + (zkS l A₀).addStab := by
    intro x hx
    exact Finset.mem_add.2 ⟨x, hx, 0, h0H, add_zero x⟩
  have hBle : (zkB l A₀).card ≤ (zkB l A₀ + (zkS l A₀).addStab).card :=
    Finset.card_le_card hBD
  obtain ⟨s, t, hsS, htB, hst, ht1⟩ := zkTight_st htight hSne
  -- The unoccupied difference coset and its witnesses.
  obtain ⟨b, hbA, c, hcA, hbc⟩ :=
    zk_exists_unoccupied_diff_coset hl h0 hmem hgen hlt htight
  have hbn := hmem b hbA
  have hcn := hmem c hcA
  -- `(b − c) % l ∉ hintRes`: else `↑(b − c) ∈ H ⊆ B + H`.
  have hbc' : (b - c) % l ∉ hintRes l A₀ := by
    intro hx
    have h1 := cast_mem_zkStab_of_mem_hintRes hx
    rw [intCast_emod_self hl] at h1
    exact hbc (Finset.mem_add.2 ⟨0, h0B, _, h1, zero_add _⟩)
  -- The charge lemma on the integer lift.
  have hcharge := zk_cosDiff_charge_fiber hl (hintRes_bounds hl)
    (hintRes_zero hSne) (hintRes_add hl hSne) hbA hbn hcA hcn hbc'
  -- Charged fibres land in `zkT` and avoid `A₀`.
  have hchargedT : modTranslate l ((b - c) % l) (hintRes l A₀) ∩ posDiff A₀ ∩
      (posDiff A₀).image (l - ·) ⊆ zkT l A₀ := charge_land_subset_zkT
  have hdisj : Disjoint (A₀.erase 0)
      (modTranslate l ((b - c) % l) (hintRes l A₀) ∩ posDiff A₀ ∩
        (posDiff A₀).image (l - ·)) := by
    rw [Finset.disjoint_left]
    intro x hxe hxch
    obtain ⟨hxK, -⟩ := Finset.mem_inter.1 (Finset.mem_inter.1 hxch).1
    obtain ⟨hh, hhHint, hxx⟩ := mem_modTranslate.1 hxK
    have hhH := cast_mem_zkStab_of_mem_hintRes hhHint
    have hxA : x ∈ A₀ := (Finset.mem_erase.1 hxe).2
    rw [← hxx] at hxA
    have hxc : ((((b - c) % l + hh) % l : ℤ) : ZMod l.toNat) ∈ zkB l A₀ :=
      Finset.mem_image.2 ⟨_, hxA, rfl⟩
    rw [intCast_emod_self hl, Int.cast_add, intCast_emod_self hl] at hxc
    -- `↑(b − c) = (↑(b−c) + ↑hh) − ↑hh ∈ B + H`, contradiction.
    apply hbc
    refine Finset.mem_add.2 ⟨_, hxc, -((hh : ℤ) : ZMod l.toNat),
      neg_mem_zkStab hSne hhH, ?_⟩
    ring
  -- `|T| ≥ (k − 1) + charge`.
  have hsubT : A₀.erase 0 ∪ (modTranslate l ((b - c) % l) (hintRes l A₀) ∩
      posDiff A₀ ∩ (posDiff A₀).image (l - ·)) ⊆ zkT l A₀ :=
    Finset.union_subset (erase_zero_subset_zkT h0 hmem) hchargedT
  have hcardT : ((A₀.card : ℤ) - 1) +
      ((modTranslate l ((b - c) % l) (hintRes l A₀) ∩ posDiff A₀ ∩
        (posDiff A₀).image (l - ·)).card : ℤ) ≤ ((zkT l A₀).card : ℤ) := by
    have h1 := Finset.card_le_card hsubT
    have h2' := Finset.card_union_of_disjoint hdisj
    have h3 : (A₀.erase 0).card = A₀.card - 1 := Finset.card_erase_of_mem h0
    have h4 : 1 ≤ A₀.card := Finset.card_pos.2 ⟨0, h0⟩
    omega
  -- Hole accounting: the holes of the two cosets sum to at most `η = ht − k`.
  have hDcard : (((zkB l A₀ + (zkS l A₀).addStab).image
      (fun x : ZMod l.toNat => (x.val : ℤ))).card : ℤ) =
      ((zkB l A₀ + (zkS l A₀).addStab).card : ℤ) := by
    rw [Finset.card_image_of_injective _
      (fun a b h => ZMod.val_injective _ h)]
  have hbB : ((b : ℤ) : ZMod l.toNat) ∈ zkB l A₀ :=
    Finset.mem_image.2 ⟨b, hbA, rfl⟩
  have hcB : ((c : ℤ) : ZMod l.toNat) ∈ zkB l A₀ :=
    Finset.mem_image.2 ⟨c, hcA, rfl⟩
  have hRsub : modTranslate l b (hintRes l A₀) ⊆
      (zkB l A₀ + (zkS l A₀).addStab).image
        (fun x : ZMod l.toNat => (x.val : ℤ)) :=
    modTranslate_subset_valImage hl hbB
  have hRcsub : modTranslate l c (hintRes l A₀) ⊆
      (zkB l A₀ + (zkS l A₀).addStab).image
        (fun x : ZMod l.toNat => (x.val : ℤ)) :=
    modTranslate_subset_valImage hl hcB
  have hA0sub : A₀ ⊆ (zkB l A₀ + (zkS l A₀).addStab).image
      (fun x : ZMod l.toNat => (x.val : ℤ)) := by
    intro x hx
    have hxB : ((x : ℤ) : ZMod l.toNat) ∈ zkB l A₀ :=
      Finset.mem_image.2 ⟨x, hx, rfl⟩
    have hxD : ((x : ℤ) : ZMod l.toNat) ∈ zkB l A₀ + (zkS l A₀).addStab :=
      Finset.mem_add.2 ⟨_, hxB, 0, h0H, add_zero _⟩
    exact Finset.mem_image.2 ⟨_, hxD,
      val_intCast_of_mem_Ico hl (hmem x hx).1 (hmem x hx).2⟩
  -- `R` and `Rc` are disjoint (distinct cosets, reproof of the charge-lemma
  -- disjointness step).
  have hRR : modTranslate l b (hintRes l A₀) ∩ modTranslate l c (hintRes l A₀)
      = ∅ := by
    apply Finset.eq_empty_iff_forall_not_mem.2
    intro z hz
    obtain ⟨hzR, hzS⟩ := Finset.mem_inter.1 hz
    obtain ⟨h₁, hh₁, he₁⟩ := mem_modTranslate.1 hzR
    obtain ⟨h₂, hh₂, he₂⟩ := mem_modTranslate.1 hzS
    have hneg : (-h₁) % l ∈ hintRes l A₀ :=
      neg_emod_mem_of_add_closed (hintRes_zero hSne) (hintRes_add hl hSne) hh₁
    have hsub : (h₂ - h₁) % l ∈ hintRes l A₀ := by
      have hdvd : l ∣ -h₁ - (-h₁) % l := by
        refine ⟨-h₁ / l, ?_⟩
        have h := Int.emod_add_ediv_mul (-h₁) l
        rw [mul_comm l (-h₁ / l)]
        omega
      have e : (h₂ - h₁) % l = (h₂ + (-h₁) % l) % l := by
        rw [Int.emod_eq_emod_iff_emod_sub_eq_zero, ← Int.dvd_iff_emod_eq_zero]
        convert hdvd using 1
        ring
      rw [e]
      exact hintRes_add hl hSne _ hh₂ _ hneg
    have hbcH : (b - c) % l ∈ hintRes l A₀ := by
      have e : (b - c) % l = (h₂ - h₁) % l := by
        rw [Int.emod_eq_emod_iff_emod_sub_eq_zero, ← Int.dvd_iff_emod_eq_zero]
        have hz2 : (b + h₁) % l = (c + h₂) % l := by rw [he₁, he₂]
        rw [Int.emod_eq_emod_iff_emod_sub_eq_zero,
          ← Int.dvd_iff_emod_eq_zero] at hz2
        convert hz2 using 1
        ring
      rw [e]
      exact hsub
    exact hbc' hbcH
  have hRdisj : Disjoint (modTranslate l b (hintRes l A₀) \ A₀)
      (modTranslate l c (hintRes l A₀) \ A₀) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨hxR, -⟩ := Finset.mem_sdiff.1 hx
    obtain ⟨hxRc, -⟩ := Finset.mem_sdiff.1 hx'
    have hxI : x ∈ modTranslate l b (hintRes l A₀) ∩
        modTranslate l c (hintRes l A₀) := Finset.mem_inter.2 ⟨hxR, hxRc⟩
    rw [hRR] at hxI
    exact Finset.notMem_empty _ hxI
  have hholesZ : ((modTranslate l b (hintRes l A₀) \ A₀).card : ℤ) +
      ((modTranslate l c (hintRes l A₀) \ A₀).card : ℤ) ≤
      ((zkB l A₀ + (zkS l A₀).addStab).card : ℤ) - (A₀.card : ℤ) := by
    have hunion : (modTranslate l b (hintRes l A₀) \ A₀ ∪
        modTranslate l c (hintRes l A₀) \ A₀).card =
        (modTranslate l b (hintRes l A₀) \ A₀).card +
        (modTranslate l c (hintRes l A₀) \ A₀).card :=
      Finset.card_union_of_disjoint hRdisj
    have hhRA : modTranslate l b (hintRes l A₀) \ A₀ ∪
        modTranslate l c (hintRes l A₀) \ A₀ ⊆
        (zkB l A₀ + (zkS l A₀).addStab).image
          (fun x : ZMod l.toNat => (x.val : ℤ)) \ A₀ :=
      Finset.union_subset
        (Finset.sdiff_subset_sdiff hRsub (Finset.Subset.refl A₀))
        (Finset.sdiff_subset_sdiff hRcsub (Finset.Subset.refl A₀))
    have hle := Finset.card_le_card hhRA
    have hsdiff : (((zkB l A₀ + (zkS l A₀).addStab).image
        (fun x : ZMod l.toNat => (x.val : ℤ))) \ A₀).card =
        ((zkB l A₀ + (zkS l A₀).addStab).image
          (fun x : ZMod l.toNat => (x.val : ℤ))).card - A₀.card :=
      Finset.card_sdiff hA0sub
    have hAle : A₀.card ≤ ((zkB l A₀ + (zkS l A₀).addStab).image
        (fun x : ZMod l.toNat => (x.val : ℤ))).card :=
      Finset.card_le_card hA0sub
    rw [hunion] at hle
    omega
  -- `|R \ A₀| = h − f_b` and the same for `c`.
  have hRb : ((modTranslate l b (hintRes l A₀) \ A₀).card : ℤ) =
      ((zkS l A₀).addStab.card : ℤ) -
        ((A₀ ∩ modTranslate l b (hintRes l A₀)).card : ℤ) := by
    have hAR : A₀ ∩ modTranslate l b (hintRes l A₀) ⊆
        modTranslate l b (hintRes l A₀) := Finset.inter_subset_right
    have heq : modTranslate l b (hintRes l A₀) \ A₀ =
        modTranslate l b (hintRes l A₀) \ (A₀ ∩ modTranslate l b (hintRes l A₀)) := by
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_inter]
      tauto
    have hsdiff : (modTranslate l b (hintRes l A₀) \ A₀).card =
        (modTranslate l b (hintRes l A₀)).card -
          (A₀ ∩ modTranslate l b (hintRes l A₀)).card := by
      rw [heq]
      exact Finset.card_sdiff hAR
    have hcardR : (modTranslate l b (hintRes l A₀)).card =
        (hintRes l A₀).card := card_modTranslate hl (hintRes_bounds hl)
    have hle : (A₀ ∩ modTranslate l b (hintRes l A₀)).card ≤
        (modTranslate l b (hintRes l A₀)).card := Finset.card_le_card hAR
    rw [hsdiff, hcardR, hintRes_card]
    omega
  have hRc : ((modTranslate l c (hintRes l A₀) \ A₀).card : ℤ) =
      ((zkS l A₀).addStab.card : ℤ) -
        ((A₀ ∩ modTranslate l c (hintRes l A₀)).card : ℤ) := by
    have hAR : A₀ ∩ modTranslate l c (hintRes l A₀) ⊆
        modTranslate l c (hintRes l A₀) := Finset.inter_subset_right
    have heq : modTranslate l c (hintRes l A₀) \ A₀ =
        modTranslate l c (hintRes l A₀) \ (A₀ ∩ modTranslate l c (hintRes l A₀)) := by
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_inter]
      tauto
    have hsdiff : (modTranslate l c (hintRes l A₀) \ A₀).card =
        (modTranslate l c (hintRes l A₀)).card -
          (A₀ ∩ modTranslate l c (hintRes l A₀)).card := by
      rw [heq]
      exact Finset.card_sdiff hAR
    have hcardR : (modTranslate l c (hintRes l A₀)).card =
        (hintRes l A₀).card := card_modTranslate hl (hintRes_bounds hl)
    have hle : (A₀ ∩ modTranslate l c (hintRes l A₀)).card ≤
        (modTranslate l c (hintRes l A₀)).card := Finset.card_le_card hAR
    rw [hsdiff, hcardR, hintRes_card]
    omega
  have hsSz : ((zkS l A₀).card : ℤ) =
      2 * (((zkS l A₀).addStab.card : ℤ) * (t : ℤ)) -
        ((zkS l A₀).addStab.card : ℤ) := by
    have hs' : s = 2 * t - 1 := by omega
    rw [hsS, hs']
    have h2t : 1 ≤ 2 * t := by omega
    rw [Nat.cast_mul, Nat.cast_sub h2t]
    push_cast
    ring
  have hDz : ((zkB l A₀ + (zkS l A₀).addStab).card : ℤ) =
      ((zkS l A₀).addStab.card : ℤ) * (t : ℤ) := by
    rw [htB, Nat.cast_mul]
  have hHint : ((hintRes l A₀).card : ℤ) = ((zkS l A₀).addStab.card : ℤ) := by
    exact_mod_cast hintRes_card
  have hke : (A₀.card : ℤ) ≤
      ((zkS l A₀).addStab.card : ℤ) * (t : ℤ) := by
    have := hBle
    rw [hBcard, htB] at this
    exact_mod_cast this
  omega

end Assemble

end JSP000728
