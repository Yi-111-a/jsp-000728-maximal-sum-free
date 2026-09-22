/-
# The small-diameter case of Freiman's difference-set bound

For `A ⊆ [0, ℓ]` containing `0` and `ℓ` with `ℓ + 3 ≤ 2|A|`, the difference
set satisfies `|A − A| ≥ ℓ + |A|`.  This is the dense half of Freiman's
`min (ℓ + |A|, 3|A| − 3)` bound used by Deshouillers–Freiman–Sós–Temkin
(the `Freiman3k4` hypothesis in `JSPProblem/DFSTBridge.lean`).

## Proof sketch

Write `S = A ∪ (ℓ − A)` for the symmetric hull of `A` inside `[0, ℓ]` and
`P = posDiff A ⊆ [1, ℓ]` for the positive differences, so
`|A − A| = 2|P| + 1` (`card_image_sub_self`).

* `S ∖ {0} ⊆ P`: an element `a ∈ A`, `a ≠ 0` is the difference `a − 0`, and an
  element `ℓ − a ≠ 0` is the difference `ℓ − a`.
* For `d ∈ T := [1, ℓ − 1] ∖ S` (a symmetric hole, i.e. `d ∉ A` and
  `ℓ − d ∉ A`), at least one of `d`, `ℓ − d` lies in `P`.  Otherwise the
  disjoint-translate bounds
    `|A ∩ [d, ℓ]| + |A ∩ [0, ℓ − d]| ≤ ℓ − d + 1`,
    `|A ∩ [ℓ − d, ℓ]| + |A ∩ [0, d]| ≤ d + 1`
  sum to `2|A| ≤ ℓ + 2`, contradicting `ℓ + 3 ≤ 2|A|`.
* Since `S` is symmetric under `d ↦ ℓ − d`, the residues of `T` not already in
  `P` inject into those that are, so `|T| ≤ 2|T ∩ P|`, and hence
  `2|P| ≥ 2(|S| − 1) + |T| = |S| + ℓ − 1 ≥ |A| + ℓ − 1`.

The coprime-differences hypothesis is in fact implied by the diameter bound
(`A ⊆ dℤ` would force `2|A| ≤ ℓ + 2`), so the proof never uses it.
-/

import JSPProblem.DFSTBridge
import JSPProblem.Freiman3k4

namespace JSP000728

open Finset

section DiffSmall

variable {A : Finset ℤ} {ℓ : ℤ}

/-- If `1 ≤ d ≤ ℓ − 1` is not a positive difference of `A ⊆ [0, ℓ]`, then the
two pieces `A ∩ [d, ℓ]` and `(A ∩ [0, ℓ − d]) + d` are disjoint subsets of
`[d, ℓ]`, hence `|A ∩ [d, ℓ]| + |A ∩ [0, ℓ − d]| ≤ ℓ − d + 1`. -/
lemma card_inter_Icc_le_of_not_mem_posDiff {d : ℤ}
    (hd : 1 ≤ d) (hd' : d ≤ ℓ - 1) (hdn : d ∉ posDiff A) :
    ((A ∩ Finset.Icc d ℓ).card : ℤ) + ((A ∩ Finset.Icc 0 (ℓ - d)).card : ℤ) ≤
      ℓ - d + 1 := by
  classical
  set L := A ∩ Finset.Icc 0 (ℓ - d) with hLdef
  set H := A ∩ Finset.Icc d ℓ with hHdef
  have hdisj : Disjoint H (L.image (· + d)) := by
    rw [Finset.disjoint_left]
    intro y hyH hyL
    obtain ⟨x, hxL, rfl⟩ := Finset.mem_image.1 hyL
    have hxA := (Finset.mem_inter.1 hxL).1
    have hyA := (Finset.mem_inter.1 hyH).1
    exact hdn (mem_posDiff.2 ⟨⟨x + d, hyA, x, hxA, by ring⟩, by omega⟩)
  have hsub : H ∪ L.image (· + d) ⊆ Finset.Icc d ℓ := by
    intro y hy
    rcases Finset.mem_union.1 hy with h | h
    · exact (Finset.mem_inter.1 h).2
    · obtain ⟨x, hxL, rfl⟩ := Finset.mem_image.1 h
      have hxI := Finset.mem_Icc.1 (Finset.mem_inter.1 hxL).2
      rw [Finset.mem_Icc]
      omega
  have himg : (L.image (· + d)).card = L.card :=
    Finset.card_image_of_injective _ (add_left_injective d)
  have hle := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj, himg] at hle
  have hIcc : (Finset.Icc d ℓ).card = (ℓ - d + 1).toNat := by
    rw [Int.card_Icc]
    congr 1
    omega
  rw [hIcc] at hle
  have hle' : ((H.card + L.card : ℕ) : ℤ) ≤ (((ℓ - d + 1).toNat : ℕ) : ℤ) := by
    exact_mod_cast hle
  rw [Int.toNat_of_nonneg (by omega : 0 ≤ ℓ - d + 1)] at hle'
  push_cast at hle'
  exact hle'

/-- Splitting `A ⊆ [0, ℓ]` at a non-member `d ∈ [0, ℓ]`:
`|A ∩ [0, d]| + |A ∩ [d, ℓ]| = |A|`. -/
lemma card_split_eq {d : ℤ}
    (hlo : ∀ x ∈ A, 0 ≤ x) (hhi : ∀ x ∈ A, x ≤ ℓ)
    (hd0 : 0 ≤ d) (hdl : d ≤ ℓ) (hdn : d ∉ A) :
    (A ∩ Finset.Icc 0 d).card + (A ∩ Finset.Icc d ℓ).card = A.card := by
  classical
  have hunion : (A ∩ Finset.Icc 0 d) ∪ (A ∩ Finset.Icc d ℓ) = A := by
    ext x
    constructor
    · intro hx
      rcases Finset.mem_union.1 hx with h | h
      · exact (Finset.mem_inter.1 h).1
      · exact (Finset.mem_inter.1 h).1
    · intro hx
      have hx0 := hlo x hx
      have hxl := hhi x hx
      rcases le_or_gt x d with h | h
      · exact Finset.mem_union.2 (Or.inl
          (Finset.mem_inter.2 ⟨hx, Finset.mem_Icc.2 ⟨hx0, h⟩⟩))
      · exact Finset.mem_union.2 (Or.inr
          (Finset.mem_inter.2 ⟨hx, Finset.mem_Icc.2 ⟨le_of_lt h, hxl⟩⟩))
  have hdisj : Disjoint (A ∩ Finset.Icc 0 d) (A ∩ Finset.Icc d ℓ) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    have h1 := Finset.mem_Icc.1 (Finset.mem_inter.1 hx1).2
    have h2 := Finset.mem_Icc.1 (Finset.mem_inter.1 hx2).2
    have hdx : x = d := by omega
    subst hdx
    exact hdn (Finset.mem_inter.1 hx1).1
  calc (A ∩ Finset.Icc 0 d).card + (A ∩ Finset.Icc d ℓ).card
      = ((A ∩ Finset.Icc 0 d) ∪ (A ∩ Finset.Icc d ℓ)).card :=
        (Finset.card_union_of_disjoint hdisj).symm
    _ = A.card := by rw [hunion]

/-- **Hole covering for difference sets.** If `d ∈ [1, ℓ − 1]` misses the
symmetric hull (`d ∉ A` and `ℓ − d ∉ A`), then at least one of `d`, `ℓ − d`
is a positive difference: otherwise the two translate bounds give
`2|A| ≤ ℓ + 2`, contradicting `ℓ + 3 ≤ 2|A|`. -/
lemma mem_posDiff_or_of_symmetric_hole {d : ℤ}
    (hlo : ∀ x ∈ A, 0 ≤ x) (hhi : ∀ x ∈ A, x ≤ ℓ)
    (hd1 : 1 ≤ d) (hd2 : d ≤ ℓ - 1)
    (hdA : d ∉ A) (hdlA : ℓ - d ∉ A)
    (hdiam : ℓ + 3 ≤ 2 * A.card) :
    d ∈ posDiff A ∨ ℓ - d ∈ posDiff A := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨hdn, hdn'⟩ := hcon
  have h1 := card_inter_Icc_le_of_not_mem_posDiff hd1 hd2 hdn
  have h2 := @card_inter_Icc_le_of_not_mem_posDiff A ℓ (ℓ - d)
    (by omega) (by omega) hdn'
  have he : ℓ - (ℓ - d) = d := by ring
  rw [he] at h2
  have hP := card_split_eq hlo hhi (by omega) (by omega) hdA
  have hR := card_split_eq hlo hhi (by omega) (by omega) hdlA
  omega

/-- **Small-diameter Freiman bound for difference sets.**  For `A ⊆ [0, ℓ]`
containing `0` and `ℓ` with `ℓ + 3 ≤ 2|A|`, the difference set satisfies
`|A − A| ≥ ℓ + |A|`. -/
theorem card_sdiff_self_ge_diam_add_card {A : Finset ℤ} {ℓ : ℤ}
    (h0 : (0 : ℤ) ∈ A) (hl : ℓ ∈ A) (hlo : ∀ x ∈ A, 0 ≤ x) (hhi : ∀ x ∈ A, x ≤ ℓ)
    (hgcd : ∀ d : ℤ, 2 ≤ d → ∃ x ∈ A, ∃ y ∈ A, ¬ d ∣ x - y)
    (hdiam : ℓ + 3 ≤ 2 * A.card) :
    ℓ + A.card ≤ ((A.image₂ (· - ·) A).card : ℤ) := by
  classical
  have hne : A.Nonempty := ⟨0, h0⟩
  have hl0 : 0 ≤ ℓ := hhi 0 h0
  have hsub : A ⊆ Finset.Icc 0 ℓ :=
    fun x hx => Finset.mem_Icc.2 ⟨hlo x hx, hhi x hx⟩
  have hl1 : 1 ≤ ℓ := by
    have hcard := Finset.card_le_card hsub
    have hIcc : (Finset.Icc (0 : ℤ) ℓ).card = (ℓ + 1).toNat := by
      rw [Int.card_Icc]
      congr 1
      omega
    rw [hIcc] at hcard
    have hcast : (A.card : ℤ) ≤ (((ℓ + 1).toNat : ℕ) : ℤ) := by
      exact_mod_cast hcard
    rw [Int.toNat_of_nonneg (by omega : 0 ≤ ℓ + 1)] at hcast
    omega
  -- The symmetric hull `S = A ∪ (ℓ − A)` inside `[0, ℓ]`.
  set S := A ∪ A.image (ℓ - ·) with hSdef
  have hSA : A ⊆ S := Finset.subset_union_left
  have hScard : A.card ≤ S.card := Finset.card_le_card hSA
  have hSsub : S ⊆ Finset.Icc 0 ℓ := by
    intro x hx
    rcases Finset.mem_union.1 hx with h | h
    · exact hsub h
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 h
      have h1 := hlo a ha
      have h2 := hhi a ha
      rw [Finset.mem_Icc]
      omega
  have h0S : (0 : ℤ) ∈ S := Finset.mem_union.2 (Or.inl h0)
  have hlS : ℓ ∈ S := Finset.mem_union.2 (Or.inl hl)
  have hSsym : ∀ x ∈ S, ℓ - x ∈ S := by
    intro x hx
    rcases Finset.mem_union.1 hx with h | h
    · exact Finset.mem_union.2 (Or.inr (Finset.mem_image.2 ⟨x, h, by ring⟩))
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 h
      have e : ℓ - (ℓ - a) = a := by ring
      rw [e]
      exact Finset.mem_union.2 (Or.inl ha)
  -- Positive differences contain `S ∖ {0}`.
  have hSpos : S \ {0} ⊆ posDiff A := by
    intro x hx
    obtain ⟨hxS, hx0⟩ := Finset.mem_sdiff.1 hx
    rw [Finset.mem_singleton] at hx0
    rcases Finset.mem_union.1 hxS with h | h
    · have hxp : 0 < x := lt_of_le_of_ne (hlo x h) (Ne.symm hx0)
      exact mem_posDiff.2 ⟨⟨x, h, 0, h0, by ring⟩, hxp⟩
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 h
      have hlt : a < ℓ := by
        rcases eq_or_ne a ℓ with e | e
        · exfalso
          apply hx0
          rw [e]
          ring
        · exact lt_of_le_of_ne (hhi a ha) e
      exact mem_posDiff.2 ⟨⟨ℓ, hl, a, ha, by ring⟩, by omega⟩
  -- The symmetric holes `T = [1, ℓ − 1] ∖ S`; each is covered by `posDiff`
  -- up to the partner `d ↦ ℓ − d`.
  set T := Finset.Icc 1 (ℓ - 1) \ S with hTdef
  set T₁ := T.filter (· ∈ posDiff A) with hT₁def
  have hT₁pos : T₁ ⊆ posDiff A := fun x hx => (Finset.mem_filter.1 hx).2
  have hkey : ∀ d ∈ T, d ∈ posDiff A ∨ ℓ - d ∈ posDiff A := by
    intro d hd
    obtain ⟨hdI, hdS⟩ := Finset.mem_sdiff.1 hd
    have hdI' := Finset.mem_Icc.1 hdI
    have hdA : d ∉ A := fun h => hdS (Finset.mem_union.2 (Or.inl h))
    have hdlA : ℓ - d ∉ A := fun h =>
      hdS (Finset.mem_union.2 (Or.inr (Finset.mem_image.2 ⟨ℓ - d, h, by ring⟩)))
    exact mem_posDiff_or_of_symmetric_hole hlo hhi hdI'.1 hdI'.2 hdA hdlA hdiam
  have hmap : ∀ d ∈ T \ T₁, ℓ - d ∈ T₁ := by
    intro d hd
    obtain ⟨hdT, hdT₁⟩ := Finset.mem_sdiff.1 hd
    have hdpd : d ∉ posDiff A := fun h => hdT₁ (Finset.mem_filter.2 ⟨hdT, h⟩)
    obtain ⟨hdI, hdS⟩ := Finset.mem_sdiff.1 hdT
    have hdI' := Finset.mem_Icc.1 hdI
    have hld : ℓ - d ∈ posDiff A := (hkey d hdT).resolve_left hdpd
    have hldT : ℓ - d ∈ T := by
      refine Finset.mem_sdiff.2 ⟨Finset.mem_Icc.2 ⟨by omega, by omega⟩, fun h => ?_⟩
      have e : ℓ - (ℓ - d) = d := by ring
      exact hdS (e ▸ hSsym (ℓ - d) h)
    exact Finset.mem_filter.2 ⟨hldT, hld⟩
  have hinj : Set.InjOn (fun d => ℓ - d) ((T \ T₁ : Finset ℤ) : Set ℤ) := by
    intro x _ y _ h
    have h' : ℓ - x = ℓ - y := h
    omega
  have hT₂le : (T \ T₁).card ≤ T₁.card :=
    Finset.card_le_card_of_injOn (fun d => ℓ - d) hmap hinj
  have hT₁sub : T₁ ⊆ T := fun x hx => (Finset.mem_filter.1 hx).1
  have hTsplit : T.card = T₁.card + (T \ T₁).card := by
    have hdisj : Disjoint T₁ (T \ T₁) := Finset.disjoint_sdiff
    have hunion : T₁ ∪ (T \ T₁) = T := Finset.union_sdiff_of_subset hT₁sub
    have hc := Finset.card_union_of_disjoint hdisj
    rw [hunion] at hc
    exact hc
  -- `posDiff ⊇ (S ∖ {0}) ∪ T₁`, a disjoint union.
  have hunion2 : (S \ {0}) ∪ T₁ ⊆ posDiff A := Finset.union_subset hSpos hT₁pos
  have hdisj2 : Disjoint (S \ {0}) T₁ := by
    rw [Finset.disjoint_left]
    intro x hx hxT
    have hxS := (Finset.mem_sdiff.1 hx).1
    exact (Finset.mem_sdiff.1 (Finset.mem_filter.1 hxT).1).2 hxS
  have hposge : (S \ {0}).card + T₁.card ≤ (posDiff A).card := by
    have hc := Finset.card_le_card hunion2
    rwa [Finset.card_union_of_disjoint hdisj2] at hc
  have hS0card : (S \ {0}).card = S.card - 1 := by
    rw [Finset.sdiff_singleton_eq_erase, Finset.card_erase_of_mem h0S]
  -- `|T| = ℓ + 1 − |S|`.
  have hcap : S ∩ Finset.Icc 1 (ℓ - 1) = S \ {0, ℓ} := by
    ext x
    constructor
    · intro hx
      obtain ⟨hxS, hxI⟩ := Finset.mem_inter.1 hx
      have hI := Finset.mem_Icc.1 hxI
      refine Finset.mem_sdiff.2 ⟨hxS, ?_⟩
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨by omega, by omega⟩
    · intro hx
      obtain ⟨hxS, hx2⟩ := Finset.mem_sdiff.1 hx
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx2
      have hxB := Finset.mem_Icc.1 (hSsub hxS)
      exact Finset.mem_inter.2 ⟨hxS, Finset.mem_Icc.2 ⟨by omega, by omega⟩⟩
  have hsub2 : ({0, ℓ} : Finset ℤ) ⊆ S := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact h0S
    · exact hlS
  have hc2 : ({0, ℓ} : Finset ℤ).card = 2 := by
    have hne' : (0 : ℤ) ≠ ℓ := by omega
    rw [Finset.card_insert_of_notMem, Finset.card_singleton]
    rwa [Finset.mem_singleton]
  have hSge2 : 2 ≤ S.card := hc2 ▸ Finset.card_le_card hsub2
  have hScard' : (S \ {0, ℓ}).card + 2 = S.card := by
    have hsd := Finset.card_sdiff_of_subset hsub2
    omega
  have hcaple : (S \ {0, ℓ}).card ≤ (Finset.Icc 1 (ℓ - 1)).card := by
    rw [← hcap]
    exact Finset.card_le_card Finset.inter_subset_right
  have hTcard' : T.card + (S \ {0, ℓ}).card = (Finset.Icc 1 (ℓ - 1)).card := by
    have hsd : T.card =
        (Finset.Icc 1 (ℓ - 1)).card - (S ∩ Finset.Icc 1 (ℓ - 1)).card :=
      Finset.card_sdiff
    rw [hcap] at hsd
    omega
  have hIcc : (Finset.Icc (1 : ℤ) (ℓ - 1)).card = (ℓ - 1).toNat := by
    rw [Int.card_Icc]
    congr 1
    omega
  -- Final assembly.
  have hmain : ((A.image₂ (· - ·) A).card : ℤ) = 2 * (posDiff A).card + 1 := by
    exact_mod_cast card_image_sub_self hne
  have htl : (((ℓ - 1).toNat : ℕ) : ℤ) = ℓ - 1 :=
    Int.toNat_of_nonneg (by omega : 0 ≤ ℓ - 1)
  omega

end DiffSmall

end JSP000728
