/-
# The periodic marginal case: reduction to the tight Kneser quotient

For `A₀ ⊆ [0, l)` containing `0` with `2|A₀| ≤ l` and generating difference
set, `PeriodicMarginal` asks for

  `3(|A₀| − 1) ≤ 2·|posDiff(A₀) ∪ (l − A₀')|`

when `S = B − B` (for `B = A₀ ⊆ ZMod l`) is periodic (`S.addStab ≠ 0`) and
proper (`|S| < l`).

## The accounting

With `H = (B − B).addStab`, `h = |H|`, and `T = P ∩ (l − P)` the
both-direction fibres, the fiber identities give

  `2·|P| = |S| + |T| − 1`,

so the goal is `|S| + |T| ≥ 3|B| − 2`.  Kneser (`add_kneser_sub_image₂`)
gives `|S| ≥ 2|B + H| − |H|`; writing `|S| = h·s` and `|B + H| = h·t`
(`s` = number of `H`-cosets in `S`, `t` = number meeting `B`) this is
`s ≥ 2t − 1`.  Since `|T| ≥ |B ∪ −B| − 1 ≥ |B| − 1`, the case `s ≥ 2t`
closes immediately:

  `|S| + |T| ≥ 2t·h + |B| − 1 ≥ 3|B| − 1 ≥ 3|B| − 2`.

The remaining case `s = 2t − 1` — equality in Kneser's bound in the
quotient `ZMod l / H` — is packaged as `ZKPartialResidual` and discharged
by `zmodKneserBound_of_zkPartial`.
-/

import JSPProblem.ZKBound2

namespace JSP000728

open Finset
open scoped Pointwise

/-- The modular shadow of `A₀` in `ZMod l` (the set `B` of the informal
discussion).  Abbreviation to keep the residual statements readable. -/
abbrev zkB (l : ℤ) (A₀ : Finset ℤ) : Finset (ZMod l.toNat) :=
  A₀.image (fun x : ℤ => (x : ZMod l.toNat))

/-- The modular difference set `S = B − B ⊆ ZMod l`. -/
abbrev zkS (l : ℤ) (A₀ : Finset ℤ) : Finset (ZMod l.toNat) :=
  (zkB l A₀).image₂ (· - ·) (zkB l A₀)

/-- **The tight-Kneser periodic residual.**  `PeriodicMarginal` restricted
to the configurations where Kneser's bound on `S = B − B` is tight in the
quotient by the stabilizer: writing `H = S.addStab`, this is the case
`|S| = 2·|B + H| − |H|` (i.e. the quotient image `B̄ ⊆ ZMod l / H` satisfies
`|B̄ − B̄| = 2|B̄| − 1`).  This is the genuinely inverse-theoretic core of
the periodic case. -/
def ZKPartialResidual : Prop :=
  ∀ (l : ℤ) (A₀ : Finset ℤ),
    0 < l → 0 ∈ A₀ → (∀ x ∈ A₀, 0 ≤ x ∧ x < l) →
    2 * (A₀.card : ℤ) ≤ l →
    (∀ d : ℤ, 2 ≤ d → d ∣ l → ∃ x ∈ A₀, ∃ y ∈ A₀, ¬ d ∣ x - y) →
    (zkS l A₀).addStab ≠ 0 →
    (zkS l A₀).card < l.toNat →
    (zkS l A₀).card + (zkS l A₀).addStab.card =
      2 * (zkB l A₀ + (zkS l A₀).addStab).card →
    3 * ((A₀.card : ℤ) - 1) ≤
      2 * (posDiff A₀ ∪ (A₀.erase 0).image (l - ·)).card

/-- The full periodic marginal case follows from its tight-Kneser
restriction: when `|S| ≥ 2·|B + H|` (non-tight Kneser) the fiber count
`|T| ≥ |B| − 1` already gives `|S| + |T| ≥ 3|B| − 2`. -/
theorem zmodKneserBound_of_zkPartial (hres : ZKPartialResidual) :
    PeriodicMarginal := by
  classical
  intro l A₀ hl h0 hmem h2 hgen hstab hlt
  -- The ambient set `A = insert l A₀` and the standard objects.
  set A : Finset ℤ := insert l A₀ with hAdef
  have hlnA : l ∉ A₀ := by
    intro h; have := (hmem l h).2; omega
  have hAerase : A.erase l = A₀ := by
    rw [hAdef]; exact Finset.erase_insert hlnA
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
  set T := P ∩ P.image (l - ·) with hTdef
  set B : Finset (ZMod l.toNat) := A₀.image (fun x : ℤ => (x : ZMod l.toNat))
    with hBdef
  set S : Finset (ZMod l.toNat) := B.image₂ (· - ·) B with hSdef
  set H : Finset (ZMod l.toNat) := S.addStab with hHdef
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
    have hBeq : modIm A l = B := by rw [modIm, hAerase, hBdef]
    rw [hBeq] at h
    exact_mod_cast h
  -- Hence `2|P| = |S| + |T| − 1`; it suffices to bound `|S| + |T|`.
  have hPT : (2 : ℤ) * (P.card : ℤ) = (S.card : ℤ) + (T.card : ℤ) - 1 := by
    omega
  -- `|B| = |A₀|`.
  have hBcard : (B.card : ℤ) = A₀.card := by
    have h := card_zmod_image_eq_card_erase hlA hl hminA hmaxA
    rw [hAerase] at h
    have hcardA : A.card = A₀.card + 1 := by
      rw [hAdef, Finset.card_insert_of_notMem hlnA]
    rw [hcardA] at h
    have hsub : (A₀.card + 1 - 1 : ℕ) = A₀.card := Nat.add_sub_cancel _ _
    rw [hsub] at h
    rw [hBdef]
    exact_mod_cast h
  -- `|T| ≥ |B ∪ −B| − 1 ≥ |B| − 1`.
  have hTge : (((B ∪ -B).card : ℤ)) - 1 ≤ (T.card : ℤ) := by
    have h := card_fiber_ge_card_union_neg hl h0 hmem
    rw [hTdef, hPdef, hBdef]
    exact h
  have hBsub : B ⊆ B ∪ -B := Finset.subset_union_left
  have hcardle : (B.card : ℤ) ≤ ((B ∪ -B).card : ℤ) := by
    exact_mod_cast Finset.card_le_card hBsub
  -- The stabilizer data: `h ≥ 2`, `h ∣ |S|`, `h ∣ |B + H|`.
  have h0B : (0 : ZMod l.toNat) ∈ B :=
    Finset.mem_image.2 ⟨0, h0, by simp⟩
  have h0S : (0 : ZMod l.toNat) ∈ S :=
    Finset.mem_image₂.2 ⟨0, h0B, 0, h0B, sub_self 0⟩
  have hSne : S.Nonempty := ⟨0, h0S⟩
  have hHne : H.Nonempty := hSne.addStab
  have hHpos : 0 < H.card := hHne.card_pos
  have hH2 : 2 ≤ H.card := by
    have hnt : S.addStab.Nontrivial :=
      (hSne.addStab_nontrivial).2 hstab
    exact Finset.one_lt_card.2 hnt
  have h0H : (0 : ZMod l.toNat) ∈ H := by
    rw [hHdef]; exact zero_mem_addStab.2 hSne
  have hBH : B ⊆ B + H := by
    intro b hb
    exact Finset.mem_add.2 ⟨b, hb, 0, h0H, add_zero b⟩
  have hBle : B.card ≤ (B + H).card := Finset.card_le_card hBH
  have hkneser : 2 * (B + H).card - H.card ≤ S.card := by
    have h := Finset.add_kneser_sub_image₂ B
    rw [← hSdef, ← hHdef] at h ⊢
    exact h
  obtain ⟨s, hsS⟩ := Finset.card_addStab_dvd_card S
  obtain ⟨t, htB⟩ := Finset.card_addStab_dvd_card_add_addStab B S
  rw [← hHdef] at hsS htB
  -- `hsS : S.card = H.card * s`, `htB : (B + H).card = H.card * t`.
  have ht1 : 1 ≤ t := by
    have hpos : 0 < (B + H).card := Finset.card_pos.2 (hBH h0B |> fun h => ⟨_, h⟩)
    rw [htB] at hpos
    rcases Nat.eq_zero_or_pos t with ht0 | htpos
    · rw [ht0, mul_zero] at hpos; omega
    · exact htpos
  -- `s ≥ 2t − 1` from Kneser.
  have hst : 2 * t - 1 ≤ s := by
    have hkey : H.card * (2 * t - 1) ≤ H.card * s := by
      rw [← hsS]
      rw [htB] at hkneser
      have hmul : H.card * (2 * t - 1) = 2 * (H.card * t) - H.card := by
        rcases Nat.eq_zero_or_pos t with ht0 | htpos
        · simp [ht0]
        · have : 2 * t - 1 + 1 = 2 * t := by omega
          calc H.card * (2 * t - 1)
              = H.card * (2 * t) - H.card := by
                conv_rhs => rw [← this]
                rw [Nat.mul_succ]
                omega
            _ = 2 * (H.card * t) - H.card := by ring_nf
      rw [hmul]; exact hkneser
    exact Nat.le_of_mul_le_mul_left hkey hHpos
  -- `|S| + |T| ≥ 3|B| − 2`, hence `3(|A₀| − 1) ≤ 2|P|`.
  have hgoal : 3 * ((A₀.card : ℤ) - 1) ≤ 2 * (P.card : ℤ) := by
    rcases eq_or_lt_of_le hst with hseq | hsgt
    · -- `s = 2t − 1`: the tight case, handled by the residual hypothesis.
      have htight : S.card + H.card = 2 * (B + H).card := by
        rw [hsS, htB, ← hseq]
        have : 2 * t - 1 + 1 = 2 * t := by omega
        calc H.card * (2 * t - 1) + H.card
            = H.card * (2 * t - 1 + 1) := by rw [Nat.mul_succ]
          _ = H.card * (2 * t) := by rw [this]
          _ = 2 * (H.card * t) := by ring
      have hres' := hres l A₀ hl h0 hmem h2 hgen
      -- Massage the residual hypotheses into the `zkS`/`zkB` form.
      have hS' : (zkS l A₀).addStab ≠ 0 := hstab
      have hlt' : (zkS l A₀).card < l.toNat := hlt
      have hT' : (zkS l A₀).card + (zkS l A₀).addStab.card =
          2 * (zkB l A₀ + (zkS l A₀).addStab).card := htight
      have h := hres' hS' hlt' hT'
      rw [← hPdef] at h ⊢
      exact h
    · -- `s ≥ 2t`: `|S| ≥ 2t·h ≥ 2|B|` and `|T| ≥ |B| − 1`.
      have hs2 : 2 * t ≤ s := by omega
      have hScard : (2 : ℤ) * ((B + H).card : ℤ) ≤ (S.card : ℤ) := by
        have : (S.card : ℤ) = (H.card : ℤ) * s := by exact_mod_cast hsS
        have : (2 * (H.card * t) : ℤ) ≤ (H.card * s : ℤ) := by
          have hs2z : (2 : ℤ) * (t : ℤ) ≤ (s : ℤ) := by exact_mod_cast hs2
          have hHz : (0 : ℤ) ≤ (H.card : ℤ) := by exact_mod_cast hHpos.le
          calc 2 * ((H.card : ℤ) * (t : ℤ))
              = (H.card : ℤ) * (2 * (t : ℤ)) := by ring
            _ ≤ (H.card : ℤ) * (s : ℤ) :=
                mul_le_mul_of_nonneg_left hs2z hHz
        calc (2 : ℤ) * ((B + H).card : ℤ)
            = 2 * ((H.card : ℤ) * (t : ℤ)) := by rw [htB]; push_cast; ring
          _ ≤ (S.card : ℤ) := by rw [this]
      have hTB : (B.card : ℤ) - 1 ≤ (T.card : ℤ) := by omega
      have hsum : (3 : ℤ) * ((A₀.card : ℤ) - 1) ≤
          (S.card : ℤ) + (T.card : ℤ) - 1 := by
        have hBHk : ((B + H).card : ℤ) ≥ (B.card : ℤ) := by
          exact_mod_cast hBle
        omega
      omega
  rw [hPdef]
  exact hgoal

end JSP000728
