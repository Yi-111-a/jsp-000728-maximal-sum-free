/-
# The `r = 1` (near-symmetric) case of `RemoveMaxResidual`

This file develops the `r = 1` branch of the elementary remove-max route to
Freiman's `3k − 4` difference bound (`JSPProblem/FreimanResidualB.lean`).

Setup: `A ⊆ [0, l]` contains `0` and `l`, satisfies the generation/coprimality
hypothesis and `2|A| − 2 ≤ l`.  With `A' = A ∖ {l}` and `l' = max A'`, the
remove-max residual asks for `|A − A| ≥ 3|A| − 3` when `A'` is coprime and
either `r = 1` or `l' + 2r < 2|A| − 2`, where
`r = #{a' ∈ A' : l − a' ∉ A' − A'}`.

## The `r = 1` case (`RemoveMaxSym`)

When `r = 1`, the filter is exactly `{0}`: every `b ∈ B := A' ∖ {0}` already
has `l − b ∈ posDiff A'`.  Writing `B̄ ⊆ ZMod l` for the modular shadow of `A'`
(`modIm`), the exact modular fibre identity `card_sub_self_eq_zmod_fiber`
gives

  `|A − A| = |B̄ − B̄| + |P ∩ (l − P)| + 2`,   `P := posDiff A'`.

Since `B ⊆ P ∩ (l − P)` one has `|P ∩ (l − P)| ≥ |B| = |A| − 2`.  Kneser's
theorem for the cyclic group `ZMod l`
(`JSPProblem/KneserZMod.lean`) then gives

* **Aperiodic case** (trivial stabilizer): `|B̄ − B̄| ≥ 2|B̄| − 1 = 2|A| − 3`,
  hence `|A − A| ≥ (2|A| − 3) + (|A| − 2) + 2 = 3|A| − 3` exactly.
* **Periodic case** (`|B̄ − B̄|` stabilised by a nontrivial subgroup `H`):
  the analysis of the `B̄ + H` cosets is isolated as the residual hypothesis
  `RemoveMaxSymPeriodic`.

* `RemoveMaxSym` — the `r = 1` disjunct of `RemoveMaxResidual`.
* `RemoveMaxGap` — the second (`l' + 2r < 2|A| − 2`) disjunct.
* `removeMaxResidual_of_parts` — the case split `RemoveMaxSym ∧
  RemoveMaxGap → RemoveMaxResidual`.
* `RemoveMaxSymPeriodic` — the residual periodic-configuration Prop.
* `removeMaxSym_of_periodic` — `RemoveMaxSymPeriodic → RemoveMaxSym`.
-/

import JSPProblem.FreimanResidualB
import JSPProblem.FreimanResidual
import JSPProblem.KneserZMod

namespace JSP000728

open Finset
open scoped Pointwise

/-! ### The two disjuncts of `RemoveMaxResidual` -/

/-- The **near-symmetric (`r = 1`) disjunct** of `RemoveMaxResidual`: same
hypotheses, with the filter cardinality pinned to `1`. -/
def RemoveMaxSym : Prop :=
  ∀ (A : Finset ℤ) (l l' : ℤ),
    0 ∈ A → l ∈ A → (∀ x ∈ A, 0 ≤ x ∧ x ≤ l) →
    (∀ d : ℤ, 2 ≤ d → ∃ x ∈ A, ∃ y ∈ A, ¬ d ∣ x - y) →
    2 * (A.card : ℤ) - 2 ≤ l →
    l' ∈ A.erase l → (∀ a' ∈ A.erase l, a' ≤ l') →
    (∀ d : ℤ, 2 ≤ d → ∃ x ∈ A.erase l, ∃ y ∈ A.erase l, ¬ d ∣ x - y) →
    (((A.erase l).filter (fun a' => l - a' ∉
        (A.erase l).image₂ (· - ·) (A.erase l))).card = 1) →
    3 * (A.card : ℤ) - 3 ≤ ((A.image₂ (· - ·) A).card : ℤ)

/-- The **small-diameter gap disjunct** of `RemoveMaxResidual`: same
hypotheses, with `l' + 2r < 2|A| − 2`. -/
def RemoveMaxGap : Prop :=
  ∀ (A : Finset ℤ) (l l' : ℤ),
    0 ∈ A → l ∈ A → (∀ x ∈ A, 0 ≤ x ∧ x ≤ l) →
    (∀ d : ℤ, 2 ≤ d → ∃ x ∈ A, ∃ y ∈ A, ¬ d ∣ x - y) →
    2 * (A.card : ℤ) - 2 ≤ l →
    l' ∈ A.erase l → (∀ a' ∈ A.erase l, a' ≤ l') →
    (∀ d : ℤ, 2 ≤ d → ∃ x ∈ A.erase l, ∃ y ∈ A.erase l, ¬ d ∣ x - y) →
    (l' + 2 * (((A.erase l).filter (fun a' => l - a' ∉
        (A.erase l).image₂ (· - ·) (A.erase l))).card : ℤ)
        < 2 * (A.card : ℤ) - 2) →
    3 * (A.card : ℤ) - 3 ≤ ((A.image₂ (· - ·) A).card : ℤ)

/-- **The case split.**  `RemoveMaxResidual` is the disjunction of the two
configuration classes handled by `RemoveMaxSym` and `RemoveMaxGap`. -/
theorem removeMaxResidual_of_parts (h1 : RemoveMaxSym) (h2 : RemoveMaxGap) :
    RemoveMaxResidual := by
  intro A l l' h0 hl hmem hgcd hlarge hl'mem hl'max hgcd' hdisj
  rcases hdisj with hr | hr
  · exact h1 A l l' h0 hl hmem hgcd hlarge hl'mem hl'max hgcd' hr
  · exact h2 A l l' h0 hl hmem hgcd hlarge hl'mem hl'max hgcd' hr

/-! ### The residual periodic configurations -/

/-- The **periodic residual** of the `r = 1` analysis: the same hypotheses as
`RemoveMaxSym`, together with the condition that the modular difference set
`B̄ − B̄ ⊆ ZMod l` is *genuinely periodic* — its stabilizer `H` is nontrivial
(`2 ≤ |H|`) and `B̄` meets at least two `H`-cosets (`|H| < |B̄ + H|`).  These
are precisely the inverse configurations in which the near-symmetric set `B̄`
is spread over several cosets of a nontrivial period. -/
def RemoveMaxSymPeriodic : Prop :=
  ∀ (A : Finset ℤ) (l l' : ℤ),
    0 ∈ A → l ∈ A → (∀ x ∈ A, 0 ≤ x ∧ x ≤ l) →
    (∀ d : ℤ, 2 ≤ d → ∃ x ∈ A, ∃ y ∈ A, ¬ d ∣ x - y) →
    2 * (A.card : ℤ) - 2 ≤ l →
    l' ∈ A.erase l → (∀ a' ∈ A.erase l, a' ≤ l') →
    (∀ d : ℤ, 2 ≤ d → ∃ x ∈ A.erase l, ∃ y ∈ A.erase l, ¬ d ∣ x - y) →
    (((A.erase l).filter (fun a' => l - a' ∉
        (A.erase l).image₂ (· - ·) (A.erase l))).card = 1) →
    2 ≤ (((modIm A l).image₂ (· - ·) (modIm A l)).addStab).card →
    (((modIm A l).image₂ (· - ·) (modIm A l)).addStab).card <
      ((modIm A l) + ((modIm A l).image₂ (· - ·) (modIm A l)).addStab).card →
    3 * (A.card : ℤ) - 3 ≤ ((A.image₂ (· - ·) A).card : ℤ)

/-! ### The `r = 1` argument -/

section RemoveMaxSym

variable {A : Finset ℤ} {l l' : ℤ}

/-- The modular difference set `B̄ − B̄ ⊆ ZMod l` is `0` together with the
residues of `P ∪ (l − P)` for `P = posDiff A'`.  In particular
`|B̄ − B̄| = |P ∪ (l − P)| + 1` when `π` is injective on `(0, l)`; we only
need the displayed form here. -/
theorem removeMaxSym_aperiodic
    (h0 : 0 ∈ A) (hl : l ∈ A)
    (hmem : ∀ x ∈ A, 0 ≤ x ∧ x ≤ l)
    (hgcd : ∀ d : ℤ, 2 ≤ d → ∃ x ∈ A, ∃ y ∈ A, ¬ d ∣ x - y)
    (hlarge : 2 * (A.card : ℤ) - 2 ≤ l)
    (hl'mem : l' ∈ A.erase l) (hl'max : ∀ a' ∈ A.erase l, a' ≤ l')
    (hgcd' : ∀ d : ℤ, 2 ≤ d → ∃ x ∈ A.erase l, ∃ y ∈ A.erase l,
      ¬ d ∣ x - y)
    (hr1 : ((A.erase l).filter (fun a' => l - a' ∉
        (A.erase l).image₂ (· - ·) (A.erase l))).card = 1)
    (hstab : (((modIm A l).image₂ (· - ·) (modIm A l)).addStab).card ≤ 1) :
    3 * (A.card : ℤ) - 3 ≤ ((A.image₂ (· - ·) A).card : ℤ) := by
  classical
  have hmin : ∀ x ∈ A, 0 ≤ x := fun x hx => (hmem x hx).1
  have hmax : ∀ x ∈ A, x ≤ l := fun x hx => (hmem x hx).2
  -- `|A| ≥ 2` from the generation hypothesis at `d = 2`.
  obtain ⟨x₂, hx₂, y₂, hy₂, hxy₂⟩ := hgcd 2 (le_refl 2)
  have hne2 : x₂ ≠ y₂ := by
    intro h'; subst h'; exact hxy₂ (dvd_refl 2)
  have hk2 : 2 ≤ A.card := by
    have hsub : ({x₂, y₂} : Finset ℤ) ⊆ A := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact hx₂
      · exact hy₂
    have h := Finset.card_le_card hsub
    rwa [Finset.card_pair hne2] at h
  have hl0 : 0 < l := by have h := hmin l hl; omega
  set A' := A.erase l with hA'def
  have h0' : (0 : ℤ) ∈ A' := Finset.mem_erase.2 ⟨ne_of_lt hl0, h0⟩
  have hcardA' : A'.card = A.card - 1 := Finset.card_erase_of_mem hl
  have hl'ne : l' ≠ l := (Finset.mem_erase.1 hl'mem).1
  have hl'A : l' ∈ A := (Finset.mem_erase.1 hl'mem).2
  have hl'l : l' < l := lt_of_le_of_ne (hmax l' hl'A) hl'ne
  set B := A'.erase 0 with hBdef
  set D' := A'.image₂ (· - ·) A' with hD'def
  set P := posDiff A' with hPdef
  set F := A'.filter (fun a' => l - a' ∉ D') with hFdef
  -- `0 ∈ F`, so `F = {0}`.
  have h0F : (0 : ℤ) ∈ F := by
    refine Finset.mem_filter.2 ⟨h0', ?_⟩
    intro hmem'
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.mem_image₂.1 hmem'
    have hx' := hl'max x hx
    have hy0 := hmin y (Finset.mem_erase.1 hy).2
    omega
  have hF : F = {0} := by
    obtain ⟨a, ha⟩ := Finset.card_eq_one.1 hr1
    rw [ha] at h0F
    rw [ha, Finset.mem_singleton] at h0F
    rw [ha, h0F]
  -- Key: every `a' ∈ A'`, `a' ≠ 0`, has `l − a' ∈ posDiff A'`.
  have hkey : ∀ a' ∈ A', a' ≠ 0 → l - a' ∈ P := by
    intro a' ha' ha'0
    have ha'F : a' ∉ F := by rw [hF]; simp [ha'0]
    have h1 : l - a' ∈ D' := by
      by_contra h
      exact ha'F (Finset.mem_filter.2 ⟨ha', h⟩)
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.mem_image₂.1 h1
    refine mem_posDiff.2 ⟨⟨x, hx, y, hy, hxy⟩, ?_⟩
    have ha'l : a' < l :=
      lt_of_le_of_ne (hmax a' (Finset.mem_erase.1 ha').2)
        (Finset.mem_erase.1 ha').1
    omega
  -- `PA := posDiff A ∩ (0, l)` collapses to `P`.
  set PA := (posDiff A).filter (· < l) with hPAdef
  have hPA : PA = P := by
    rw [posDiff_filter_lt_eq hl hmin hmax]
    apply Finset.union_eq_left.2
    intro z hz
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hz
    obtain ⟨hb0, hbA'⟩ := Finset.mem_erase.1 hb
    exact hkey b hbA' hb0
  -- The exact modular fibre identity.
  set B̄ := modIm A l with hB̄def
  have hid := card_sub_self_eq_zmod_fiber h0 hl hl0 hmin hmax
  rw [← hPA] at hid
  -- `|B̄| = |A'|` by injectivity of reduction on `[0, l)`.
  have hinj : Set.InjOn (fun x : ℤ => (x : ZMod l.toNat)) ↑A' := by
    intro x hx y hy hxy
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at hxy
    obtain ⟨k, hk⟩ := hxy
    rw [Int.toNat_of_nonneg (le_of_lt hl0)] at hk
    have hxb : 0 ≤ x ∧ x < l :=
      ⟨hmin x (Finset.mem_erase.1 hx).2,
        lt_of_le_of_ne (hmax x (Finset.mem_erase.1 hx).2)
          (Finset.mem_erase.1 hx).1⟩
    have hyb : 0 ≤ y ∧ y < l :=
      ⟨hmin y (Finset.mem_erase.1 hy).2,
        lt_of_le_of_ne (hmax y (Finset.mem_erase.1 hy).2)
          (Finset.mem_erase.1 hy).1⟩
    have hk0 : k = 0 := by
      rcases lt_trichotomy k 0 with hkc | hkc | hkc
      · have : l * k ≤ l * (-1) :=
          mul_le_mul_of_nonneg_left (by omega) (by omega)
        omega
      · exact hkc
      · have : l * 1 ≤ l * k :=
          mul_le_mul_of_nonneg_left (by omega) (by omega)
        omega
    rw [hk0] at hk
    omega
  have hB̄card : B̄.card = A'.card := Finset.card_image_of_injOn hinj
  -- `B ⊆ P ∩ (l − P)`.
  have hBsub : B ⊆ P ∩ P.image (l - ·) := by
    intro b hb
    obtain ⟨hb0, hbA'⟩ := Finset.mem_erase.1 hb
    refine Finset.mem_inter.2 ⟨?_, ?_⟩
    · refine mem_posDiff.2 ⟨⟨b, hbA', 0, h0', by ring⟩, ?_⟩
      have hb0' := hmin b (Finset.mem_erase.1 hbA').2
      omega
    · exact Finset.mem_image.2 ⟨l - b, hkey b hbA' hb0, by ring⟩
  have hPcard : B.card ≤ (P ∩ P.image (l - ·)).card :=
    Finset.card_le_card hBsub
  have hBcard : B.card = A'.card - 1 := Finset.card_erase_of_mem h0'
  -- The aperiodic Kneser bound.
  have hB̄ne : B̄.Nonempty := by
    refine ⟨(0 : ZMod l.toNat), ?_⟩
    exact Finset.mem_image.2 ⟨0, h0', by simp⟩
  have hBBne : (B̄.image₂ (· - ·) B̄).Nonempty := hB̄ne.image₂ hB̄ne
  have h0H : (0 : ZMod l.toNat) ∈ (B̄.image₂ (· - ·) B̄).addStab :=
    zero_mem_addStab.2 hBBne
  have hH0 : (B̄.image₂ (· - ·) B̄).addStab = 0 := by
    apply Finset.eq_singleton_iff_unique_mem.2 ⟨h0H, ?_⟩
    intro x hx
    have h1 := Finset.card_le_one.1 hstab
    have h2 := h1 x hx 0 h0H
    exact h2
  have hkn : 2 * B̄.card - 1 ≤ (B̄.image₂ (· - ·) B̄).card := by
    have h := ZMod.kneser_sub_aperiodic hB̄ne hH0
    exact h
  -- Count: `|A − A| = |B̄ − B̄| + |P ∩ (l − P)| + 2`.
  have hk' : (A.card : ℤ) = (B.card : ℤ) + 2 := by
    have h1 : A.card = B.card + 2 := by omega
    rw [h1]; push_cast; ring
  have hfin : ((A.image₂ (· - ·) A).card : ℤ) ≥
      (2 * B̄.card - 1 : ℤ) + B.card + 2 := by
    have h1 : (B̄.image₂ (· - ·) B̄).card ≥ 2 * B̄.card - 1 := hkn
    have h2 : (P ∩ P.image (l - ·)).card ≥ B.card := hPcard
    omega
  omega
```

end RemoveMaxSym
