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
noncomputable abbrev hintRes (l : ℤ) (A₀ : Finset ℤ) : Finset ℤ :=
  ((zkS l A₀).addStab).image (fun x : ZMod l.toNat => (x.val : ℤ))

theorem hintRes_card {l : ℤ} {A₀ : Finset ℤ} :
    (hintRes l A₀).card = (zkS l A₀).addStab.card :=
  Finset.card_image_of_injective _ (fun a b h => ZMod.val_injective _ h)

theorem hintRes_bounds {l : ℤ} {A₀ : Finset ℤ} (hl : 0 < l) :
    ∀ x ∈ hintRes l A₀, 0 ≤ x ∧ x < l := by
  intro x hx
  obtain ⟨h, -, rfl⟩ := Finset.mem_image.1 hx
  have := ZMod.val_lt (n := l.toNat) h
  refine ⟨Int.natCast_nonneg _, ?_⟩
  have hl' : (l.toNat : ℤ) = l := Int.toNat_of_nonneg (le_of_lt hl)
  omega

theorem hintRes_zero {l : ℤ} {A₀ : Finset ℤ}
    (hSne : (zkS l A₀).Nonempty) : (0 : ℤ) ∈ hintRes l A₀ := by
  refine Finset.mem_image.2 ⟨0, ?_, by simp⟩
  exact zero_mem_addStab.2 hSne

/-- Cast of an `hintRes` element back to `ZMod l` lies in `H`. -/
theorem cast_mem_zkStab_of_mem_hintRes {l : ℤ} {A₀ : Finset ℤ} {x : ℤ}
    (hx : x ∈ hintRes l A₀) :
    ((x : ℤ) : ZMod l.toNat) ∈ (zkS l A₀).addStab := by
  obtain ⟨h, hh, rfl⟩ := Finset.mem_image.1 hx
  rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  exact hh

/-- The stabilizer `H` is negation-closed. -/
theorem neg_mem_zkStab {l : ℤ} {A₀ : Finset ℤ} (hS : (zkS l A₀).Nonempty)
    {x : ZMod l.toNat} (hx : x ∈ (zkS l A₀).addStab) :
    -x ∈ (zkS l A₀).addStab := by
  have h := Finset.neg_addStab hS
  rw [← h]
  exact Finset.mem_neg.2 (neg_neg x ▸ hx)

/-- The stabilizer `H` is closed under subtraction. -/
theorem sub_mem_zkStab {l : ℤ} {A₀ : Finset ℤ} (hS : (zkS l A₀).Nonempty)
    {x y : ZMod l.toNat}
    (hx : x ∈ (zkS l A₀).addStab) (hy : y ∈ (zkS l A₀).addStab) :
    x - y ∈ (zkS l A₀).addStab := by
  have h2 : x + -y ∈ (zkS l A₀).addStab + (zkS l A₀).addStab :=
    Finset.add_mem_add hx (neg_mem_zkStab hS hy)
  have hHH : (zkS l A₀).addStab + (zkS l A₀).addStab = (zkS l A₀).addStab :=
    Finset.addStab_add_addStab _
  rw [sub_eq_add_neg]
  rwa [hHH] at h2

/-- The stabilizer `H` is closed under addition. -/
theorem add_mem_zkStab {l : ℤ} {A₀ : Finset ℤ}
    {x y : ZMod l.toNat}
    (hx : x ∈ (zkS l A₀).addStab) (hy : y ∈ (zkS l A₀).addStab) :
    x + y ∈ (zkS l A₀).addStab := by
  have h2 : x + y ∈ (zkS l A₀).addStab + (zkS l A₀).addStab :=
    Finset.add_mem_add hx hy
  have hHH : (zkS l A₀).addStab + (zkS l A₀).addStab = (zkS l A₀).addStab :=
    Finset.addStab_add_addStab _
  rwa [hHH] at h2

theorem hintRes_add {l : ℤ} {A₀ : Finset ℤ} (hl : 0 < l)
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

/-- **Existence of a missing difference coset.**  If every difference of
`B = A₀ ⊆ ZMod l` lay in the stabilizer `H`, then in particular every
element of `A₀` would cast into `H`.  Every element of `H` is killed by
`h = |H|` (Lagrange in the stabilizer subgroup), so every element of `A₀`
would be divisible by `m = l / h`.  Since `|H| ≤ |S| < l`, this `m ≥ 2`
divides `l`, contradicting the generating hypothesis. -/
theorem zk_exists_missing_coset
    (hl : 0 < l) (h0 : 0 ∈ A₀) (hmem : ∀ x ∈ A₀, 0 ≤ x ∧ x < l)
    (hgen : ∀ d : ℤ, 2 ≤ d → d ∣ l → ∃ x ∈ A₀, ∃ y ∈ A₀, ¬ d ∣ x - y)
    (hlt : (zkS l A₀).card < l.toNat) :
    ∃ b ∈ A₀, ∃ c ∈ A₀, ((b - c : ℤ) : ZMod l.toNat) ∉ (zkS l A₀).addStab := by
  classical
  have h0B : (0 : ZMod l.toNat) ∈ zkB l A₀ := Finset.mem_image.2 ⟨0, h0, by simp⟩
  have h0S : (0 : ZMod l.toNat) ∈ zkS l A₀ :=
    Finset.mem_image₂.2 ⟨0, h0B, 0, h0B, sub_self 0⟩
  have hSne : (zkS l A₀).Nonempty := ⟨0, h0S⟩
  have h0H : (0 : ZMod l.toNat) ∈ (zkS l A₀).addStab := zero_mem_addStab.2 hSne
  have hHpos : 0 < (zkS l A₀).addStab.card := (⟨0, h0H⟩ : _).card_pos
  -- `H ⊆ S`, hence `|H| < l`.
  have hsubHS : (zkS l A₀).addStab ⊆ zkS l A₀ := by
    intro x hx
    have h := Finset.vadd_finset_addStab_subset h0S
    exact h (Finset.mem_vadd.2 ⟨x, hx, zero_vadd _⟩)
  have hltH : (zkS l A₀).addStab.card < l.toNat :=
    lt_of_le_of_lt (Finset.card_le_card hsubHS) hlt
  have hdvdH : (zkS l A₀).addStab.card ∣ l.toNat := zkStab_card_dvd hl hSne
  obtain ⟨m, hm⟩ := hdvdH
  -- `l.toNat = |H| * m` with `m ≥ 2`.
  have hcastl : (l.toNat : ℤ) = l := Int.toNat_of_nonneg (le_of_lt hl)
  have hm2 : 2 ≤ m := by
    rcases lt_or_ge m 2 with h2 | h2
    · interval_cases m <;> simp only [Nat.mul_zero, Nat.mul_one] at hm <;> omega
    · exact h2
  -- `x ∈ H` implies `|H| • x = 0` (Lagrange in the stabilizer subgroup).
  have hcoe : (((zkS l A₀).addStab : Finset (ZMod l.toNat)) : Set (ZMod l.toNat)) =
      (AddAction.stabilizer (ZMod l.toNat) ((zkS l A₀) : Set (ZMod l.toNat)) :
        Set (ZMod l.toNat)) :=
    Finset.coe_addStab hSne
  have hcardstab :
      Nat.card (AddAction.stabilizer (ZMod l.toNat) ((zkS l A₀) : Set (ZMod l.toNat))) =
        (zkS l A₀).addStab.card := by
    rw [← hcoe]
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_coe _
  have hnsmul : ∀ x : ZMod l.toNat, x ∈ (zkS l A₀).addStab →
      (zkS l A₀).addStab.card • x = 0 := by
    intro x hx
    have hx' : x ∈ AddAction.stabilizer (ZMod l.toNat)
        ((zkS l A₀) : Set (ZMod l.toNat)) := by
      have hxc : x ∈ ((zkS l A₀).addStab : Set (ZMod l.toNat)) :=
        Finset.mem_coe.2 hx
      rw [hcoe] at hxc
      exact hxc
    have hdvd : addOrderOf (⟨x, hx'⟩ : AddAction.stabilizer (ZMod l.toNat)
        ((zkS l A₀) : Set (ZMod l.toNat))) ∣ (zkS l A₀).addStab.card := by
      rw [← hcardstab]
      exact addOrderOf_dvd_natCard _
    have hz : (zkS l A₀).addStab.card • (⟨x, hx'⟩ : AddAction.stabilizer
        (ZMod l.toNat) ((zkS l A₀) : Set (ZMod l.toNat))) = 0 :=
      addOrderOf_dvd_iff_nsmul_eq_zero.mp hdvd
    have hz' := congrArg Subtype.val hz
    simpa using hz'
  -- Suppose, for contradiction, that every difference lies in `H`.
  by_contra hcon
  push_neg at hcon
  -- Then every `a ∈ A₀` has `↑a ∈ H` (write `a = a − 0`), hence `m ∣ a`.
  have hdiv : ∀ a ∈ A₀, (m : ℤ) ∣ a := by
    intro a ha
    have haH : ((a : ℤ) : ZMod l.toNat) ∈ (zkS l A₀).addStab := by
      have := hcon a ha 0 h0
      rwa [sub_zero] at this
    have hz := hnsmul _ haH
    rw [nsmul_eq_mul] at hz
    -- `((|H| : ℤ) * a : ZMod l) = 0`, so `l ∣ |H| * a`.
    have hz' : (((zkS l A₀).addStab.card : ℤ) * a : ZMod l.toNat) = 0 := by
      rw [Int.cast_mul]
      have e : (((zkS l A₀).addStab.card : ℤ) : ZMod l.toNat) =
          ((zkS l A₀).addStab.card : ZMod l.toNat) := by norm_cast
      rw [e]
      exact hz
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hz'
    -- `l = |H| * m` divides `|H| * a`; cancel `|H| > 0`.
    rw [hm, Nat.cast_mul] at hz'
    obtain ⟨k, hk⟩ := hz'
    refine ⟨k, ?_⟩
    have hk' : ((zkS l A₀).addStab.card : ℤ) * a =
        ((zkS l A₀).addStab.card : ℤ) * ((m : ℤ) * k) := by
      rw [hk]
      ring
    exact mul_left_cancel₀
      (show ((zkS l A₀).addStab.card : ℤ) ≠ 0 by exact_mod_cast hHpos.ne') hk'
  -- `m ∣ l` and `m ≥ 2`: contradict the generating hypothesis.
  have hml : (m : ℤ) ∣ l := by
    refine ⟨(zkS l A₀).addStab.card, ?_⟩
    rw [← hcastl, hm]
    push_cast
    ring
  obtain ⟨x, hx, y, hy, hxy⟩ := hgen m (by exact_mod_cast hm2) hml
  exact hxy (dvd_sub (hdiv x hx) (hdiv y hy))

end MissingCoset

end JSP000728
