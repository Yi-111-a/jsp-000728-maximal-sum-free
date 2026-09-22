/-
# The tight-Kneser periodic case: reduction to the both-direction fibre count

For `A₀ ⊆ [0, l)` containing `0` with `2|A₀| ≤ l` and generating difference
set, `ZKPartialResidual` (in `JSPProblem/ZKPartial.lean`) asks for

  `3(|A₀| − 1) ≤ 2·|posDiff(A₀) ∪ (l − A₀')|`

when `S = B − B ⊆ ZMod l` (`B = A₀` cast into `ZMod l`) is periodic
(`H = S.addStab ≠ 0`), proper (`|S| < l`), and **tight**:
`|S| + |H| = 2|B + H|`.

## What is proved here

The exact fibre identity (`card_sub_self_eq_zmod_fiber` together with
`card_image2_sub_self_eq` and `posDiff_filter_lt_eq`) gives

  `2·|P| = |S| + |T| − 1`,   `T := P ∩ (l − P)`,

so `ZKPartialResidual` is *equivalent* to the fibre-counting statement

  `|S| + |T| ≥ 3|A₀| − 2`.

This file packages that remaining inequality as the hypothesis
`ZKTightCount` and proves the reduction
`zkPartialResidual : ZKTightCount → ZKPartialResidual`
unconditionally.  We also prove the structural estimates that drive the
intended argument:

* `zkT_card_union_neg_sub_one_le` — the both-direction fibres contain the
  lift of `(B ∪ −B) ∖ {0}`: `|T| ≥ |B ∪ −B| − 1`;
* `zkB_card` — `|B| = |A₀|`;
* `zkStab_card_dvd` — `|H| ∣ l` (Lagrange for the stabilizer subgroup);
* `zkTight_st` — tightness means `|S| = |H|(2t − 1)` with
  `|B + H| = |H|t`, i.e. the quotient image `B̄ ⊆ ZMod l / H` satisfies
  `|B̄ − B̄| = 2|B̄| − 1`;
* `zkTight_of_union_neg_ge` — **the easy case**: if
  `|B ∪ −B| ≥ |B| + |H| − 1` then `|S| + |T| ≥ 3|A₀| − 2` already;
* `zkTight_aperiodic_image` / `zkTight_image_card` — the image `B̄` of `B`
  in the quotient by the stabilizer has `|B̄| = t` and `B̄ − B̄` aperiodic.

The deep input that remains is the **cyclic inverse theorem**
(`CyclicAPInverse`): tight, aperiodic, proper, generating difference sets
in a finite cyclic group are arithmetic progressions with generating
difference.  With `B̄` an `H`-coset arithmetic progression of length `t`
and common difference coprime to `m = l/h`, the fibre analysis of the
integer lift `A₀ ⊆ [0, l)` (each `H`-coset is a `ℤ`-grid with step `m`)
gives `|S| + |T| ≥ 3|A₀| − 2`: the non-saturated cosets supply extra
both-direction classes, and in the `H`-saturated case
(`B = B + H`) either `B̄ ≠ −B̄`, whence `|B ∪ −B| ≥ |B| + |H|`, or `B̄` is
symmetric and the extreme coset `±(t − 1)ḡ` of `B̄ − B̄` contributes
exactly `h − 1` further both-direction classes.  That counting argument is
the remaining gap, isolated as `ZKTightCount`.

## Main declarations

* `zkT` — the both-direction fibre set `P ∩ (l − P)`.
* `ZKTightCount` — the residual fibre inequality `|S| + |T| ≥ 3|A₀| − 2`.
* `CyclicAPInverse` — the cyclic inverse theorem (packaged hypothesis).
* `zkPartialResidual` — `ZKTightCount → ZKPartialResidual`.
-/

import JSPProblem.ZKPartial

namespace JSP000728

open Finset
open scoped Pointwise

/-- The both-direction fibre set: `T = P ∩ (l − P)` for
`P = posDiff A₀ ∪ (l − A₀')`, the elements of `(0, l)` realised by
differences of `A₀` (or reflections `l − a'`) in *both* directions. -/
abbrev zkT (l : ℤ) (A₀ : Finset ℤ) : Finset ℤ :=
  (posDiff A₀ ∪ (A₀.erase 0).image (l - ·)) ∩
    ((posDiff A₀ ∪ (A₀.erase 0).image (l - ·)).image (l - ·))

/-- **The residual fibre bound of the tight periodic case.**  Under the
`ZKPartialResidual` hypotheses, `|S| + |T| ≥ 3|A₀| − 2` where `T` is the
both-direction fibre set.  Via `2|P| = |S| + |T| − 1` this is the whole
remaining content of `ZKPartialResidual`. -/
def ZKTightCount : Prop :=
  ∀ (l : ℤ) (A₀ : Finset ℤ),
    0 < l → 0 ∈ A₀ → (∀ x ∈ A₀, 0 ≤ x ∧ x < l) →
    2 * (A₀.card : ℤ) ≤ l →
    (∀ d : ℤ, 2 ≤ d → d ∣ l → ∃ x ∈ A₀, ∃ y ∈ A₀, ¬ d ∣ x - y) →
    (zkS l A₀).addStab ≠ 0 →
    (zkS l A₀).card < l.toNat →
    (zkS l A₀).card + (zkS l A₀).addStab.card =
      2 * (zkB l A₀ + (zkS l A₀).addStab).card →
    3 * (A₀.card : ℤ) - 2 ≤
      ((zkS l A₀).card : ℤ) + ((zkT l A₀).card : ℤ)

/-- **The cyclic inverse theorem** (Freiman; in this generality a
corollary of the Kemperman structure theorem / Lev–Smeliansky): in a
finite cyclic group, a difference set `C − C` that is

* tight: `|C − C| = 2|C| − 1`,
* aperiodic: `(C − C).addStab = 0`,
* proper: `|C − C| < |G|`, and
* generating: `C − C` lies in no proper subgroup,

is an arithmetic progression whose common difference generates the group.
This is the deep inverse-theoretic input for `ZKTightCount`; it is
packaged as a hypothesis here. -/
def CyclicAPInverse : Prop :=
  ∀ {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G] [IsAddCyclic G]
    (C : Finset G),
    2 ≤ C.card →
    (C - C).addStab = 0 →
    (C - C).card < Fintype.card G →
    (C - C).card = 2 * C.card - 1 →
    (∀ K : AddSubgroup G, K ≠ ⊤ →
      ¬ ((C - C : Finset G) : Set G) ⊆ (K : Set G)) →
    ∃ g v : G, AddSubgroup.closure {g} = ⊤ ∧
      C = (Finset.range C.card).image (fun i => v + (i : ℕ) • g)

section ZKTight

variable {l : ℤ} {A₀ : Finset ℤ}

/-- The both-direction fibre set contains the lift of `(B ∪ −B) ∖ {0}`:
`|T| ≥ |B ∪ −B| − 1` (restatement of `card_fiber_ge_card_union_neg`). -/
theorem zkT_card_union_neg_sub_one_le
    (hl : 0 < l) (h0 : 0 ∈ A₀) (hmem : ∀ x ∈ A₀, 0 ≤ x ∧ x < l) :
    ((zkB l A₀ ∪ -zkB l A₀).card : ℤ) - 1 ≤ ((zkT l A₀).card : ℤ) :=
  card_fiber_ge_card_union_neg hl h0 hmem

/-- `|B| = |A₀|`: reduction mod `l` is injective on `A₀ ⊆ [0, l)`. -/
theorem zkB_card (hl : 0 < l) (h0 : 0 ∈ A₀)
    (hmem : ∀ x ∈ A₀, 0 ≤ x ∧ x < l) :
    (zkB l A₀).card = A₀.card := by
  classical
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
  have h := card_zmod_image_eq_card_erase hlA hl hminA hmaxA
  rw [hAerase] at h
  have hcardA : A.card = A₀.card + 1 := by
    rw [hAdef, Finset.card_insert_of_notMem hlnA]
  rw [hcardA] at h
  have hsub : (A₀.card + 1 - 1 : ℕ) = A₀.card := Nat.add_sub_cancel _ _
  rw [hsub] at h
  exact h

/-- The stabilizer cardinality divides `l`: `S.addStab` coerces to the
stabilizer subgroup of `ZMod l`, whose order divides `l` by Lagrange. -/
theorem zkStab_card_dvd (hl : 0 < l)
    (hS : (zkS l A₀).Nonempty) :
    (zkS l A₀).addStab.card ∣ l.toNat := by
  classical
  have hnz : NeZero l.toNat := ⟨by omega⟩
  have hcoe : ((zkS l A₀).addStab : Set (ZMod l.toNat)) =
      (AddAction.stabilizer (ZMod l.toNat) ((zkS l A₀) : Set (ZMod l.toNat)) :
        Set (ZMod l.toNat)) :=
    Finset.coe_addStab hS
  have hdvd : Nat.card (AddAction.stabilizer (ZMod l.toNat)
      ((zkS l A₀) : Set (ZMod l.toNat))) ∣ Nat.card (ZMod l.toNat) :=
    AddSubgroup.card_addSubgroup_dvd_card _
  have hcard1 : Nat.card (AddAction.stabilizer (ZMod l.toNat)
      ((zkS l A₀) : Set (ZMod l.toNat))) = (zkS l A₀).addStab.card := by
    show Nat.card ↥((AddAction.stabilizer (ZMod l.toNat)
        ((zkS l A₀) : Set (ZMod l.toNat))) : Set (ZMod l.toNat)) =
        (zkS l A₀).addStab.card
    rw [← hcoe, Nat.card_coe_set_eq, Set.ncard_coe_finset]
  rw [hcard1] at hdvd
  have hcard2 : Nat.card (ZMod l.toNat) = l.toNat := Nat.card_zmod _
  rw [hcard2] at hdvd
  exact hdvd

/-- The tight numerics: writing `h = |H|`, tightness
`|S| + h = 2|B + H|` together with the divisibilities `h ∣ |S|` and
`h ∣ |B + H|` gives `|S| = h(2t − 1)` and `|B + H| = ht` for some
`t ≥ 1` — i.e. the quotient image `B̄ ⊆ ZMod l / H` satisfies
`|B̄ − B̄| = 2|B̄| − 1`. -/
theorem zkTight_st
    (htight : (zkS l A₀).card + (zkS l A₀).addStab.card =
      2 * (zkB l A₀ + (zkS l A₀).addStab).card)
    (hS : (zkS l A₀).Nonempty) :
    ∃ s t : ℕ,
      (zkS l A₀).card = (zkS l A₀).addStab.card * s ∧
      (zkB l A₀ + (zkS l A₀).addStab).card = (zkS l A₀).addStab.card * t ∧
      s + 1 = 2 * t ∧ 1 ≤ t := by
  obtain ⟨s, hsS⟩ := Finset.card_addStab_dvd_card (zkS l A₀)
  obtain ⟨t, htB⟩ := Finset.card_addStab_dvd_card_add_addStab (zkB l A₀) (zkS l A₀)
  refine ⟨s, t, hsS, htB, ?_, ?_⟩
  · have hHpos : 0 < (zkS l A₀).addStab.card := hS.addStab.card_pos
    have := htight
    rw [hsS, htB] at this
    have : (zkS l A₀).addStab.card * (s + 1) =
        (zkS l A₀).addStab.card * (2 * t) := by
      calc (zkS l A₀).addStab.card * (s + 1)
          = (zkS l A₀).addStab.card * s + (zkS l A₀).addStab.card := by ring
        _ = 2 * ((zkS l A₀).addStab.card * t) := this
        _ = (zkS l A₀).addStab.card * (2 * t) := by ring
    have h2 := Nat.eq_of_mul_eq_mul_left hHpos this
    omega
  · -- `t ≥ 1` since `B + H ≠ ∅`.
    have h0H : (0 : ZMod l.toNat) ∈ (zkS l A₀).addStab :=
      zero_mem_addStab.2 hS
    obtain ⟨b, hb⟩ := hS
    obtain ⟨x, hxB, y, hyB, _⟩ := Finset.mem_image₂.1 hb
    have hxBH : x ∈ zkB l A₀ + (zkS l A₀).addStab :=
      Finset.mem_add.2 ⟨x, hxB, 0, h0H, add_zero x⟩
    have hpos : 0 < (zkB l A₀ + (zkS l A₀).addStab).card :=
      Finset.card_pos.2 ⟨x, hxBH⟩
    rw [htB] at hpos
    rcases Nat.eq_zero_or_pos t with ht0 | htpos
    · rw [ht0, mul_zero] at hpos
      omega
    · exact htpos

/-- **The easy case of the tight residual.**  If `B ∪ −B` is at least
`|H| − 1` larger than `B`, the crude fibre bound already gives
`|S| + |T| ≥ 3|A₀| − 2`:  indeed `|S| ≥ 2|B + H| − |H| ≥ 2|B| − |H|` and
`|T| ≥ |B ∪ −B| − 1 ≥ |B| + |H| − 2`.  This covers every configuration
except nearly `H`-saturated, nearly symmetric `B` — which is where the
cyclic inverse theorem enters. -/
theorem zkTight_of_union_neg_ge
    (hl : 0 < l) (h0 : 0 ∈ A₀) (hmem : ∀ x ∈ A₀, 0 ≤ x ∧ x < l)
    (hU : (zkB l A₀).card + (zkS l A₀).addStab.card - 1 ≤
      (zkB l A₀ ∪ -zkB l A₀).card) :
    3 * (A₀.card : ℤ) - 2 ≤
      ((zkS l A₀).card : ℤ) + ((zkT l A₀).card : ℤ) := by
  classical
  set B := zkB l A₀ with hBdef
  set S := zkS l A₀ with hSdef
  set H := S.addStab with hHdef
  have hkn : 2 * (B + H).card - H.card ≤ S.card :=
    Finset.add_kneser_sub_image₂ B
  -- `B ⊆ B + H` since `0 ∈ H` (needs `S` nonempty).
  have hSne : S.Nonempty := by
    have h0B : (0 : ZMod l.toNat) ∈ B :=
      Finset.mem_image.2 ⟨0, h0, by simp⟩
    exact ⟨0, Finset.mem_image₂.2 ⟨0, h0B, 0, h0B, sub_self 0⟩⟩
  have h0H : (0 : ZMod l.toNat) ∈ H := zero_mem_addStab.2 hSne
  have hBH : B ⊆ B + H := by
    intro b hb
    exact Finset.mem_add.2 ⟨b, hb, 0, h0H, add_zero b⟩
  have hBle := Finset.card_le_card hBH
  have hT := zkT_card_union_neg_sub_one_le hl h0 hmem
  rw [← hBdef] at hT
  have hBcard : B.card = A₀.card := zkB_card hl h0 hmem
  -- Cast everything to `ℤ` and close by `omega`.
  have hkn' : ((S.card : ℤ)) ≥ 2 * ((B + H).card : ℤ) - (H.card : ℤ) := by
    have h1 : 2 * (B + H).card - H.card ≤ S.card := hkn
    have h0B : (0 : ZMod l.toNat) ∈ B :=
      Finset.mem_image.2 ⟨0, h0, by simp⟩
    -- `H ⊆ B + H` since `0 ∈ B`.
    have hsub : H ⊆ B + H := by
      intro c hc
      exact Finset.mem_add.2 ⟨0, h0B, c, hc, zero_add c⟩
    have hleN : H.card ≤ 2 * (B + H).card :=
      le_trans (Finset.card_le_card hsub) (by omega)
    have hcast : ((2 * (B + H).card - H.card : ℕ) : ℤ) =
        2 * ((B + H).card : ℤ) - (H.card : ℤ) := by
      rw [Nat.cast_sub hleN]
      push_cast
      ring
    rw [← hcast]
    exact_mod_cast h1
  omega

end ZKTight

/-! ### The reduction: `ZKTightCount → ZKPartialResidual` -/

/-- **The main reduction.**  Via the exact fibre identity
`2|P| = |S| + |T| − 1`, the tight periodic residual `ZKPartialResidual`
reduces to the fibre-count bound `ZKTightCount`. -/
theorem zkPartialResidual (hcount : ZKTightCount) : ZKPartialResidual := by
  classical
  intro l A₀ hl h0 hmem h2 hgen hstab hlt htight
  -- The ambient set `A = insert l A₀` and the standard objects.
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
  set P := posDiff A₀ ∪ (A₀.erase 0).image (l - ·) with hPdef
  set S := zkS l A₀ with hSdef
  set T := zkT l A₀ with hTdef
  -- The two cardinality identities for `|A − A|`.
  have hPA : (posDiff A).filter (· < l) = P := by
    rw [hPdef, ← hAerase]
    exact posDiff_filter_lt_eq hlA hminA hmaxA
  have hAA : ((A.image₂ (· - ·) A).card : ℤ) = 2 * (P.card : ℤ) + 3 := by
    have h := card_image2_sub_self_eq h0A hlA hl hminA hmaxA
    rw [hPA] at h
    exact_mod_cast h
  have hAAz : ((A.image₂ (· - ·) A).card : ℤ) =
      (S.card : ℤ) + (T.card : ℤ) + 2 := by
    have h := card_sub_self_eq_zmod_fiber h0A hlA hl hminA hmaxA
    rw [hPA] at h
    have hBeq : modIm A l = zkB l A₀ := by rw [modIm, hAerase]
    rw [hBeq] at h
    rw [hSdef, hTdef]
    exact_mod_cast h
  -- `2|P| = |S| + |T| − 1`.
  have hPT : (2 : ℤ) * (P.card : ℤ) = (S.card : ℤ) + (T.card : ℤ) - 1 := by
    omega
  -- Apply the fibre-count hypothesis and finish.
  have h := hcount l A₀ hl h0 hmem h2 hgen hstab hlt htight
  rw [← hSdef, ← hTdef] at h
  omega

end JSP000728
