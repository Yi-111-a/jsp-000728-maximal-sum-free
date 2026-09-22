/-
# Inverse theorem for minimal difference sets over `ℤ`

This file proves the classical inverse theorem for difference sets of
minimal size: a nonempty finite set `X ⊆ ℤ` with

  `|X − X| = 2·|X| − 1`

is an arithmetic progression, i.e. `X = {a, a + d, …, a + (k − 1) d}` for
some `d > 0`.  We also record the converse direction (an arithmetic
progression attains the bound), so that the pair of results gives an exact
characterisation.

## Proof sketch (integer inverse theorem)

Write `k = |X|`.  Since `|X − X| = 2·|posDiff X| + 1` (`card_image_sub_self`),
the hypothesis forces `|posDiff X| = k − 1`.  Translating so that the
minimum of `X` is `0` produces a set `A ⊆ ℤ≥0` with `0 ∈ A`, `|A| = k` and
`posDiff A = A \ {0}`: every positive difference of two elements of `A` is
again an element of `A`.

* Let `g` be the smallest positive element of `A`.  Subtracting `g`
  repeatedly (each iterate stays in `A` while positive, by the closure
  property) shows `g ∣ a` for every `a ∈ A`.
* Write `M = max A` and `w = M / g`.  The multiples
  `{0, g, 2g, …, w g} = {M − w g, M − (w−1) g, …, M}` lie in `A`
  (repeated subtraction of `g` from `M`), and every element of `A` is a
  multiple of `g` in `[0, M]`, so `A = {0, g, …, w g}` and `w = k − 1`.

Hence `A = {0, g, 2g, …, (k−1) g}` and `X = x₀ + A` is an arithmetic
progression.

## Main declarations

* `exists_eq_image_range_of_card_image₂_sub`: the inverse theorem.
* `card_image₂_sub_image_range`: the converse bound for progressions.
* `card_image₂_sub_eq_two_mul_sub_one_iff`: bundled characterisation.
* `ZModFreimanInverse`: the (unproven) cyclic-group analogue — Freiman's
  `(2.4)`-theorem — recorded as a `Prop`-valued definition for future work.
-/

import JSPProblem.DFSTBridge
import JSPProblem.KneserZMod

namespace JSP000728

open Finset

section IntInverse

variable {X : Finset ℤ}

/-- **Inverse theorem for `|X − X| = 2·|X| − 1` over `ℤ`.**

A nonempty finite set of integers whose difference set has the minimal
possible size `2·|X| − 1` is an arithmetic progression. -/
theorem exists_eq_image_range_of_card_image₂_sub (hX : X.Nonempty)
    (hcard : (X.image₂ (· - ·) X).card = 2 * X.card - 1) :
    ∃ a d : ℤ, 0 < d ∧
      X = (Finset.range X.card).image (fun (i : ℕ) => a + d * (i : ℤ)) := by
  classical
  by_cases hk1 : X.card = 1
  · -- `|X| = 1`: trivially a progression.
    obtain ⟨x, rfl⟩ := Finset.card_eq_one.1 hk1
    exact ⟨x, 1, one_pos, by simp⟩
  · -- `|X| ≥ 2`.
    have hk2 : 2 ≤ X.card := by
      have := Finset.card_pos.2 hX; omega
    set x₀ := X.min' hX with hx₀def
    have hx₀mem : x₀ ∈ X := X.min'_mem hX
    have hx₀le : ∀ x ∈ X, x₀ ≤ x := fun x hx => X.min'_le x hx
    -- Translate so the minimum is `0`.
    set A := X.image (· - x₀) with hAdef
    have hAcard : A.card = X.card := by
      rw [hAdef]
      exact Finset.card_image_of_injective _ (fun a b h => by omega)
    have hA0 : (0 : ℤ) ∈ A := Finset.mem_image.2 ⟨x₀, hx₀mem, sub_self x₀⟩
    have hAne : A.Nonempty := ⟨0, hA0⟩
    have hAnonneg : ∀ a ∈ A, (0 : ℤ) ≤ a := by
      intro a ha
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 ha
      have hxle := hx₀le x hx
      omega
    have hAdiff : A.image₂ (· - ·) A = X.image₂ (· - ·) X := by
      rw [hAdef, Finset.image₂_image_left, Finset.image₂_image_right]
      apply Finset.image₂_congr
      intro a _ b _
      ring
    -- Counting: `|posDiff A| = |A| − 1`, so `posDiff A = A \ {0}`.
    have hpd : (posDiff A).card = A.card - 1 := by
      have h := card_image_sub_self hAne
      rw [hAdiff, hcard] at h
      have hk : (1 : ℕ) ≤ X.card := Finset.card_pos.2 hX
      omega
    have hsub : A.erase 0 ⊆ posDiff A := by
      intro a ha
      rw [Finset.mem_erase] at ha
      have hapos : (0 : ℤ) < a := lt_of_le_of_ne (hAnonneg a ha.2) ha.1.symm
      exact mem_posDiff.2 ⟨⟨a, ha.2, 0, hA0, sub_zero a⟩, hapos⟩
    have hpdeq : posDiff A = A.erase 0 :=
      (Finset.eq_of_subset_of_card_le hsub (by
        rw [Finset.card_erase_of_mem hA0]; exact hpd.le)).symm
    -- `A` is closed under positive differences.
    have hclosed : ∀ a ∈ A, ∀ b ∈ A, b < a → a - b ∈ A := by
      intro a ha b hb hba
      have hd : a - b ∈ posDiff A :=
        mem_posDiff.2 ⟨⟨a, ha, b, hb, rfl⟩, by omega⟩
      rw [hpdeq] at hd
      exact (Finset.mem_erase.1 hd).2
    -- `g`: the smallest positive element of `A`.
    have hne' : (A.erase 0).Nonempty := by
      rw [← Finset.card_pos, Finset.card_erase_of_mem hA0]
      omega
    set g := (A.erase 0).min' hne' with hgdef
    have hg_erase : g ∈ A.erase 0 := (A.erase 0).min'_mem hne'
    have hgmem : g ∈ A := (Finset.mem_erase.1 hg_erase).2
    have hgne : g ≠ 0 := (Finset.mem_erase.1 hg_erase).1
    have hgpos : (0 : ℤ) < g := lt_of_le_of_ne (hAnonneg g hgmem) hgne.symm
    have hge : ∀ a ∈ A, (0 : ℤ) < a → g ≤ a := by
      intro a ha hapos
      exact (A.erase 0).min'_le a (Finset.mem_erase.2 ⟨hapos.ne', ha⟩)
    -- Every element of `A` is a multiple of `g`: subtract `g` repeatedly.
    have hdivaux : ∀ n : ℕ, ∀ a ∈ A, a.toNat = n → g ∣ a := by
      intro n
      induction n using Nat.strong_induction_on with
      | h n ih =>
        intro a ha han
        rcases eq_or_ne a 0 with rfl | ha0
        · exact dvd_zero g
        · have hapos : (0 : ℤ) < a := lt_of_le_of_ne (hAnonneg a ha) ha0.symm
          have hage : g ≤ a := hge a ha hapos
          have hadmem : a - g ∈ A := by
            rcases eq_or_lt_of_le hage with hga | hga
            · have h0 : a - g = 0 := by omega
              rw [h0]; exact hA0
            · exact hclosed a ha g hgmem hga
          have hlt : (a - g).toNat < n := by
            have h1 : ((a - g).toNat : ℤ) = a - g :=
              Int.toNat_of_nonneg (by omega)
            have h2 : (a.toNat : ℤ) = a := Int.toNat_of_nonneg (hAnonneg a ha)
            omega
          have h3 := ih (a - g).toNat hlt (a - g) hadmem rfl
          have h4 := dvd_add h3 (dvd_refl g)
          rwa [sub_add_cancel] at h4
    have hdiv : ∀ a ∈ A, g ∣ a := fun a ha => hdivaux a.toNat a ha rfl
    -- `M = max A`, `w = M / g`; so `M = w * g`.
    set M := A.max' hAne with hMdef
    have hMmem : M ∈ A := A.max'_mem hAne
    have hMge : (0 : ℤ) ≤ M := hAnonneg M hMmem
    set w := M / g with hwdef
    have hwge : (0 : ℤ) ≤ w := Int.ediv_nonneg hMge hgpos.le
    have hMdiv : w * g = M := Int.ediv_mul_cancel (hdiv M hMmem)
    -- Repeated subtraction: `M − j·g ∈ A` for `0 ≤ j ≤ w`.
    have hmem : ∀ j : ℕ, (j : ℤ) ≤ w → M - (j : ℤ) * g ∈ A := by
      intro j
      induction j with
      | zero => intro _; simpa using hMmem
      | succ j ih =>
        intro hj
        push_cast at hj ⊢
        have hjw : (j : ℤ) ≤ w := by omega
        have hv : M - (j : ℤ) * g ∈ A := ih hjw
        have hvg : g ≤ M - (j : ℤ) * g := by
          have h2 : (j : ℤ) * g + g ≤ M := by
            have h3 : ((j : ℤ) + 1) * g ≤ w * g :=
              mul_le_mul_of_nonneg_right (by omega) hgpos.le
            rwa [hMdiv, add_mul, one_mul] at h3
          omega
        rcases eq_or_lt_of_le hvg with hga | hga
        · -- `M − j·g = g`, so `M − (j+1)·g = 0 ∈ A`.
          have e : M - ((j : ℤ) + 1) * g = 0 := by
            have h5 : ((j : ℤ) + 1) * g = (j : ℤ) * g + g := by ring
            rw [h5]; omega
          rwa [e]
        · have h2 := hclosed _ hv _ hgmem hga
          have e : M - ((j : ℤ) + 1) * g = M - (j : ℤ) * g - g := by
            have h5 : ((j : ℤ) + 1) * g = (j : ℤ) * g + g := by ring
            rw [h5]; ring
          rwa [e]
    -- `A` is exactly the multiples `{0, g, …, w·g}`.
    set S : Finset ℤ := (Finset.Icc 0 w).image (fun i => i * g) with hSdef
    have hSsub : S ⊆ A := by
      intro s hs
      rw [hSdef, Finset.mem_image] at hs
      obtain ⟨i, hi, rfl⟩ := hs
      rw [Finset.mem_Icc] at hi
      have hwi : (0 : ℤ) ≤ w - i := by omega
      have h1 := hmem (w - i).toNat (by
        rw [Int.toNat_of_nonneg hwi]; omega)
      rw [Int.toNat_of_nonneg hwi] at h1
      have e : M - (w - i) * g = i * g := by
        rw [sub_mul, hMdiv]; ring
      rwa [e] at h1
    have hAsub : A ⊆ S := by
      intro a ha
      rw [hSdef, Finset.mem_image]
      refine ⟨a / g, ?_, ?_⟩
      · rw [Finset.mem_Icc]
        refine ⟨Int.ediv_nonneg (hAnonneg a ha) hgpos.le, ?_⟩
        rw [← mul_le_mul_right hgpos]
        rw [Int.ediv_mul_cancel (hdiv a ha), hMdiv]
        exact Finset.le_max' _ _ ha
      · exact Int.ediv_mul_cancel (hdiv a ha)
    have hSeq : S = A := le_antisymm hSsub hAsub
    have hScard : S.card = w.toNat + 1 := by
      rw [hSdef,
        Finset.card_image_of_injective _
          (fun a b h => mul_right_cancel₀ (ne_of_gt hgpos) h),
        Int.card_Icc]
      simp only [sub_zero]
      omega
    have hwk : w.toNat + 1 = X.card := by
      rw [← hScard, hSeq, hAcard]
    -- `Icc 0 w` is the image of `range (w.toNat + 1) = range |X|`.
    have hIcc : Finset.Icc (0 : ℤ) w =
        (Finset.range (w.toNat + 1)).image ((↑) : ℕ → ℤ) := by
      ext i
      simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
      constructor
      · rintro ⟨h0, hi⟩
        exact ⟨i.toNat, by omega, Int.toNat_of_nonneg h0⟩
      · rintro ⟨j, hj, rfl⟩
        refine ⟨by omega, by omega⟩
    have hAeq : A = (Finset.range X.card).image (fun (i : ℕ) => (i : ℤ) * g) := by
      rw [← hSeq, hSdef, hIcc, ← Finset.image_image, hwk]
      apply Finset.image_congr
      intro i _
      rfl
    -- Pull the progression back to `X = x₀ + A`.
    have hXeq : X = A.image (· + x₀) := by
      calc X = X.image id := Finset.image_id.symm
        _ = X.image ((· + x₀) ∘ (· - x₀)) :=
          Finset.image_congr fun x _ => (sub_add_cancel x x₀).symm
        _ = (X.image (· - x₀)).image (· + x₀) := Finset.image_image.symm
        _ = A.image (· + x₀) := by rw [← hAdef]
    refine ⟨x₀, g, hgpos, ?_⟩
    rw [hXeq, hAeq, Finset.image_image]
    apply Finset.image_congr
    intro i _
    show (i : ℤ) * g + x₀ = x₀ + g * (i : ℤ)
    ring

/-- The converse direction: an arithmetic progression `a, a + d, …,
a + (k−1) d` with `d > 0` has difference set of size `2k − 1`. -/
theorem card_image₂_sub_image_range (k : ℕ) (a d : ℤ) (hd : 0 < d) :
    (((Finset.range k).image fun (i : ℕ) => a + d * (i : ℤ)).image₂ (· - ·)
        ((Finset.range k).image fun (i : ℕ) => a + d * (i : ℤ))).card =
      2 * k - 1 := by
  classical
  rcases k with _ | k
  · simp
  · -- For `range (k+1)`, the differences are exactly `{−k d, …, k d}`.
    set s := (Finset.range (k + 1)).image fun (i : ℕ) => a + d * (i : ℤ)
      with hsdef
    set T : Finset ℤ := (Finset.Icc (-(k : ℤ)) (k : ℤ)).image (· * d) with hTdef
    have hsub : s.image₂ (· - ·) s ⊆ T := by
      intro z hz
      rw [hsdef, Finset.image₂_image_left, Finset.image₂_image_right] at hz
      obtain ⟨i, hi, j, hj, rfl⟩ := Finset.mem_image₂.1 hz
      rw [Finset.mem_range] at hi hj
      rw [hTdef, Finset.mem_image]
      refine ⟨(i : ℤ) - (j : ℤ), ?_, ?_⟩
      · rw [Finset.mem_Icc]
        constructor <;> omega
      · show ((i : ℤ) - (j : ℤ)) * d = a + d * (i : ℤ) - (a + d * (j : ℤ))
        ring
    have hsup : T ⊆ s.image₂ (· - ·) s := by
      intro z hz
      rw [hTdef, Finset.mem_image] at hz
      obtain ⟨n, hn, rfl⟩ := hz
      rw [Finset.mem_Icc] at hn
      rw [hsdef, Finset.image₂_image_left, Finset.image₂_image_right]
      rcases le_or_gt (0 : ℤ) n with hnp | hnp
      · -- `n ≥ 0`: `n * d = (a + d·n) − (a + d·0)`.
        refine Finset.mem_image₂.2 ⟨n.toNat, ?_, 0, ?_, ?_⟩
        · rw [Finset.mem_range]; omega
        · rw [Finset.mem_range]; omega
        · show a + d * ((n.toNat : ℕ) : ℤ) - (a + d * ((0 : ℕ) : ℤ)) = n * d
          rw [Nat.cast_zero, Int.toNat_of_nonneg hnp]
          ring
      · -- `n < 0`: `n * d = (a + d·0) − (a + d·(−n))`.
        refine Finset.mem_image₂.2 ⟨0, ?_, (-n).toNat, ?_, ?_⟩
        · rw [Finset.mem_range]; omega
        · rw [Finset.mem_range]; omega
        · show a + d * ((0 : ℕ) : ℤ) - (a + d * (((-n).toNat : ℕ) : ℤ)) = n * d
          rw [Nat.cast_zero, Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ -n)]
          ring
    have heq : s.image₂ (· - ·) s = T := le_antisymm hsub hsup
    rw [heq, hTdef,
      Finset.card_image_of_injective _
        (fun x y h => mul_right_cancel₀ (ne_of_gt hd) h),
      Int.card_Icc]
    omega

/-- Bundled characterisation: `X` has minimal difference set iff it is an
arithmetic progression. -/
theorem card_image₂_sub_eq_two_mul_sub_one_iff (hX : X.Nonempty) :
    (X.image₂ (· - ·) X).card = 2 * X.card - 1 ↔
      ∃ a d : ℤ, 0 < d ∧
        X = (Finset.range X.card).image (fun (i : ℕ) => a + d * (i : ℤ)) := by
  refine ⟨exists_eq_image_range_of_card_image₂_sub hX, ?_⟩
  rintro ⟨a, d, hd, hXeq⟩
  have h := card_image₂_sub_image_range X.card a d hd
  rwa [← hXeq] at h

end IntInverse

/-! ### The cyclic analogue (statement for future work)

Freiman's `(2.4)`-theorem is the cyclic-group analogue of
`exists_eq_image_range_of_card_image₂_sub`.  The following `Prop`-valued
definition records the precise statement needed by the residual arguments;
**proving it is open** (it requires substantially more machinery — the
combinatorial Nullstellensatz / Dias da Silva–Hamidoune theorem or
Freiman's own rectifiability argument — than the integer case above).
-/

/-- **Freiman's cyclic inverse theorem** (`(2.4)`-theorem), stated for
future work.

For `X ⊆ ZMod m` with `2·|X| ≤ m` (so `X` is "small"), suppose

* `|X − X| = 2·|X| − 1` (minimal difference set),
* `X − X` is aperiodic: its finset stabilizer `addStab` (see
  `JSPProblem/KneserZMod.lean`, `Finset.addStab`/`Finset.mem_addStab`) is
  trivial, and
* the differences generate `ZMod m`.

Then `X` is an arithmetic progression whose common difference is a unit of
`ZMod m` (i.e. coprime to `m`). -/
def ZModFreimanInverse (m : ℕ) : Prop :=
  ∀ X : Finset (ZMod m), X.Nonempty →
    2 * X.card ≤ m →
    (X.image₂ (· - ·) X).card = 2 * X.card - 1 →
    (X.image₂ (· - ·) X).addStab ⊆ {0} →
    AddSubgroup.closure ((X.image₂ (· - ·) X) : Set (ZMod m)) = ⊤ →
    ∃ a d : ZMod m, IsUnit d ∧
      X = (Finset.range X.card).image (fun (i : ℕ) => a + d * (i : ZMod m))

/-- The full statement of Freiman's cyclic inverse theorem, to be proved:
`ZModFreimanInverse m` holds for every `m`.  See the docstring of
`ZModFreimanInverse` for the hypotheses and the required conclusion. -/
def ZModFreimanInverseStatement : Prop := ∀ m : ℕ, ZModFreimanInverse m

end JSP000728
