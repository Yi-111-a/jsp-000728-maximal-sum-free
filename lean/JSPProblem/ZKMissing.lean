/-
# Missing-coset existence and free both-direction fibres for `ZKTightCount`

Two ingredients for the AFP-style assembly of the tight periodic case:

* `erase_zero_subset_zkT` — every nonzero `a ∈ A₀` is a *free* both-direction
  fibre: `a = a − 0 ∈ posDiff A₀ ⊆ P` and `l − a ∈ (l − (A₀ ∖ {0})) ⊆ P`, so
  `a ∈ T = P ∩ (l − P)`.  Hence `|T| ≥ |A₀| − 1`.

* `zk_exists_missing_coset` — in the tight periodic case there is a missing
  coset: `b, c ∈ A₀` in distinct `H`-cosets whose difference coset
  `(b − c) + H` contains no element of `B`.  Otherwise the occupied cosets are
  difference-closed, `D = B + H` is a subgroup, tightness forces `D = H`,
  and `gcd 1` is contradicted since every element of `A₀` is divisible by
  `m = l / |H| ≥ 2`.

## Main declarations

* `erase_zero_subset_zkT` — `A₀.erase 0 ⊆ zkT l A₀`.
* `zkT_card_ge_card_sub_one` — `|A₀| − 1 ≤ |zkT l A₀|`.
* `zk_exists_missing_coset` — existence of a missing difference coset.
-/

import JSPProblem.ZKTight

namespace JSP000728

open Finset
open scoped Pointwise

/-- **Free both-direction fibres.**  Every nonzero `a ∈ A₀` lies in
`T = P ∩ (l − P)`: `a = a − 0 ∈ posDiff A₀ ⊆ P` and `l − a` lies in the
reflection summand of `P`, i.e. `a ∈ l − P`. -/
theorem erase_zero_subset_zkT {l : ℤ} {A₀ : Finset ℤ}
    (h0 : 0 ∈ A₀) (hmem : ∀ x ∈ A₀, 0 ≤ x ∧ x < l) :
    A₀.erase 0 ⊆ zkT l A₀ := by
  intro a ha
  obtain ⟨ha0, haA⟩ := Finset.mem_erase.1 ha
  have hapos : 0 < a := lt_of_le_of_ne' (hmem a haA).1 ha0
  refine Finset.mem_inter.2 ⟨?_, ?_⟩
  · exact Finset.mem_union.2 (Or.inl
      (mem_posDiff.2 ⟨⟨a, haA, 0, h0, by ring⟩, hapos⟩))
  · refine Finset.mem_image.2 ⟨l - a, ?_, by ring⟩
    exact Finset.mem_union.2 (Or.inr (Finset.mem_image.2 ⟨a, ha, rfl⟩))

/-- `|T| ≥ |A₀| − 1` from the free fibres. -/
theorem zkT_card_ge_card_sub_one {l : ℤ} {A₀ : Finset ℤ}
    (h0 : 0 ∈ A₀) (hmem : ∀ x ∈ A₀, 0 ≤ x ∧ x < l) :
    (A₀.card : ℤ) - 1 ≤ ((zkT l A₀).card : ℤ) := by
  have h := Finset.card_le_card (erase_zero_subset_zkT h0 hmem)
  rw [Finset.card_erase_of_mem h0] at h
  exact_mod_cast h

section MissingCoset

variable {l : ℤ} {A₀ : Finset ℤ}

/-- The integer-residue stabilizer: `H : Finset (ZMod l)` lifted to `[0, l)`. -/
private noncomputable abbrev hintRes (l : ℤ) (A₀ : Finset ℤ) : Finset ℤ :=
  ((zkS l A₀).addStab).image (fun x : ZMod l.toNat => (x.val : ℤ))

private theorem hintRes_card {l : ℤ} {A₀ : Finset ℤ} :
    (hintRes l A₀).card = (zkS l A₀).addStab.card :=
  Finset.card_image_of_injective _ (fun a b h => ZMod.val_injective _ h)

private theorem hintRes_bounds {l : ℤ} {A₀ : Finset ℤ} (hl : 0 < l) :
    ∀ x ∈ hintRes l A₀, 0 ≤ x ∧ x < l := by
  intro x hx
  obtain ⟨h, -, rfl⟩ := Finset.mem_image.1 hx
  have := ZMod.val_lt (n := l.toNat) h
  refine ⟨Int.natCast_nonneg _, ?_⟩
  have hl' : (l.toNat : ℤ) = l := Int.toNat_of_nonneg (le_of_lt hl)
  omega

private theorem hintRes_zero {l : ℤ} {A₀ : Finset ℤ}
    (hSne : (zkS l A₀).Nonempty) : (0 : ℤ) ∈ hintRes l A₀ := by
  refine Finset.mem_image.2 ⟨0, ?_, by simp⟩
  exact zero_mem_addStab.2 hSne

private theorem hintRes_add {l : ℤ} {A₀ : Finset ℤ} (hl : 0 < l)
    (hSne : (zkS l A₀).Nonempty) :
    ∀ x ∈ hintRes l A₀, ∀ y ∈ hintRes l A₀, (x + y) % l ∈ hintRes l A₀ := by
  intro x hx y hy
  obtain ⟨h₁, hh₁, rfl⟩ := Finset.mem_image.1 hx
  obtain ⟨h₂, hh₂, rfl⟩ := Finset.mem_image.1 hy
  have hadd : h₁ + h₂ ∈ (zkS l A₀).addStab := by
    rw [mem_addStab hSne] at hh₁ hh₂ ⊢
    rw [add_vadd, hh₂, hh₁]
  refine Finset.mem_image.2 ⟨h₁ + h₂, hadd, ?_⟩
  have hv : ((h₁ + h₂).val : ℤ) = ((h₁.val + h₂.val : ℕ) : ℤ) % l.toNat := by
    rw [ZMod.val_add]; rfl
  rw [hv]
  have hl' : (l.toNat : ℤ) = l := Int.toNat_of_nonneg (le_of_lt hl)
  push_cast
  rw [hl', Nat.cast_add, Int.add_emod]

end MissingCoset

end JSP000728
