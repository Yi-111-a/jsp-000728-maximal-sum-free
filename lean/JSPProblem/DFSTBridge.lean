import JSPProblem.DFSTattack
import JSPProblem.Trichotomy

/-!
# The Freiman–DFST bridge

This file isolates the hard additive-combinatorics input of the
Deshouillers–Freiman–Sós–Temkin theorem behind a named hypothesis
`Freiman3k4`, and derives the DFST trichotomy and the sharp asymptotic
from it.

The classical DFST argument (the Freiman 1992 paper *On the structure and
the number of sum-free sets*, refined by DFST) only needs Freiman's
small-doubling theorem in its difference-set form: for a finite set `A`
with minimum `0`, maximum `ℓ` and coprime differences, the difference set
is large,

  `|A − A| ≥ min (ℓ + |A|, 3 |A| − 3)`.

This is the genuinely hard input, packaged as `Freiman3k4`; everything
downstream in this file is elementary interval counting and parity.
-/

noncomputable section

open Finset Filter

/-- **Freiman's small-doubling hypothesis (difference-set form).**

For a finite set `A` of integers with minimum `0`, maximum `ℓ`, and whose
differences are coprime (`A` is not contained in a nontrivial arithmetic
progression), the difference set satisfies

  `|A − A| ≥ min (ℓ + |A|, 3 |A| − 3)`.

This is the Freiman `3k − 4`-type bound used by Deshouillers–Freiman–
Sós–Temkin (their Lemma 2.1 applied to `A − m` and `ℓ − A`).  It is the
genuinely hard input, to be discharged by a proof of Freiman's theorem;
everything downstream in this file is elementary. -/
def Freiman3k4 : Prop :=
  ∀ A : Finset ℤ, ∀ ℓ : ℤ,
    0 ∈ A → ℓ ∈ A → (∀ x ∈ A, 0 ≤ x ∧ x ≤ ℓ) →
    (∀ d : ℤ, 2 ≤ d → ∃ x ∈ A, ∃ y ∈ A, ¬ d ∣ x - y) →
      min (ℓ + (A.card : ℤ)) (3 * (A.card : ℤ) - 3) ≤
        ((A.image₂ (· - ·) A).card : ℤ)

namespace JSP000728

open Finset

/-! ### Positive differences of a sum-free set -/

/-- The set of positive differences of a finite set of integers. -/
def posDiff (s : Finset ℤ) : Finset ℤ :=
  (s.image₂ (· - ·) s).filter (0 < ·)

theorem mem_posDiff {s : Finset ℤ} {d : ℤ} :
    d ∈ posDiff s ↔ (∃ x ∈ s, ∃ y ∈ s, x - y = d) ∧ 0 < d := by
  simp only [posDiff, Finset.mem_filter, Finset.mem_image₂]

/-- The difference set of a nonempty set is `posDiff ∪ {0} ∪ (−posDiff)`. -/
theorem image_sub_self_eq {s : Finset ℤ} (hne : s.Nonempty) :
    s.image₂ (· - ·) s =
      posDiff s ∪ ({0} : Finset ℤ) ∪ (posDiff s).image (fun d => -d) := by
  ext d
  constructor
  · intro hd
    obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_image₂.1 hd
    rcases lt_trichotomy (x - y) 0 with h | h | h
    · -- `x − y < 0`, so `y − x ∈ posDiff`.
      exact Finset.mem_union.2 (Or.inr (Finset.mem_image.2
        ⟨y - x, mem_posDiff.2 ⟨⟨y, hy, x, hx, rfl⟩, by omega⟩, by omega⟩))
    · exact Finset.mem_union.2 (Or.inl (Finset.mem_union.2
        (Or.inr (Finset.mem_singleton.2 h))))
    · exact Finset.mem_union.2 (Or.inl (Finset.mem_union.2
        (Or.inl (mem_posDiff.2 ⟨⟨x, hx, y, hy, rfl⟩, h⟩))))
  · intro hd
    rw [Finset.mem_union] at hd
    rcases hd with hd | hneg
    · rw [Finset.mem_union] at hd
      rcases hd with hpd | h0
      · obtain ⟨⟨x, hx, y, hy, rfl⟩, _⟩ := mem_posDiff.1 hpd
        exact Finset.mem_image₂.2 ⟨x, hx, y, hy, rfl⟩
      · rw [Finset.mem_singleton] at h0
        obtain ⟨z, hz⟩ := hne
        rw [h0]
        exact Finset.mem_image₂.2 ⟨z, hz, z, hz, sub_self z⟩
    · obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hneg
      obtain ⟨⟨x, hx, y, hy, rfl⟩, hdpos⟩ := mem_posDiff.1 he
      exact Finset.mem_image₂.2 ⟨y, hy, x, hx, by omega⟩

/-- The three pieces are pairwise disjoint, so `|s − s| = 2·|posDiff s| + 1`. -/
theorem card_image_sub_self {s : Finset ℤ} (hne : s.Nonempty) :
    (s.image₂ (· - ·) s).card = 2 * (posDiff s).card + 1 := by
  rw [image_sub_self_eq hne]
  have hneg : ((posDiff s).image (fun d => -d)).card = (posDiff s).card :=
    Finset.card_image_of_injective _ (fun a b h => by omega)
  have hd1 : Disjoint (posDiff s) ({0} : Finset ℤ) := by
    rw [Finset.disjoint_left]
    intro d hd h0
    rw [Finset.mem_singleton] at h0
    have := (Finset.mem_filter.1 hd).2
    omega
  have hd2 : Disjoint (posDiff s) ((posDiff s).image (fun d => -d)) := by
    rw [Finset.disjoint_left]
    intro d hd hd'
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hd'
    have h1 := (Finset.mem_filter.1 hd).2
    have h2 := (Finset.mem_filter.1 he).2
    omega
  have hd3 : Disjoint ({0} : Finset ℤ) ((posDiff s).image (fun d => -d)) := by
    rw [Finset.disjoint_left]
    intro d hd hd'
    rw [Finset.mem_singleton] at hd
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hd'
    have h2 := (Finset.mem_filter.1 he).2
    omega
  rw [Finset.card_union_of_disjoint
      (Finset.disjoint_union_left.2 ⟨hd2, hd3⟩),
    Finset.card_union_of_disjoint hd1, Finset.card_singleton, hneg]
  ring

/-- Positive differences are bounded by the spread: `posDiff s ⊆ [1, ℓ − m]`
when `s ⊆ [m, ℓ]`. -/
theorem posDiff_subset_Icc {s : Finset ℤ} {m ℓ : ℤ}
    (hmin : ∀ x ∈ s, m ≤ x) (hmax : ∀ x ∈ s, x ≤ ℓ) :
    posDiff s ⊆ Finset.Icc 1 (ℓ - m) := by
  intro d hd
  obtain ⟨⟨x, hx, y, hy, rfl⟩, hdpos⟩ := mem_posDiff.1 hd
  have := hmin y hy; have := hmax x hx
  rw [Finset.mem_Icc]
  omega

/-- A sum-free set is disjoint from its positive differences. -/
theorem disjoint_posDiff_of_isSumFree {s : Finset ℤ} (hsf : IsSumFree s) :
    Disjoint s (posDiff s) := by
  rw [Finset.disjoint_left]
  intro x hx hd
  obtain ⟨⟨a, ha, b, hb, rfl⟩, hdpos⟩ := mem_posDiff.1 hd
  have hsum : b + (a - b) ∈ s := by
    have : b + (a - b) = a := by ring
    rw [this]; exact ha
  exact hsf b hb (a - b) hx hsum

/-- The fundamental disjointness bound: `|s| + |posDiff s| ≤ ℓ` for a nonempty
sum-free `s ⊆ [m, ℓ]` with `m ≥ 1`. -/
theorem card_add_posDiff_le {s : Finset ℤ} {m ℓ : ℤ}
    (hsf : IsSumFree s) (hmin : ∀ x ∈ s, m ≤ x) (hmax : ∀ x ∈ s, x ≤ ℓ)
    (hm : m ∈ s) (hm1 : 1 ≤ m) :
    (s.card : ℤ) + (posDiff s).card ≤ ℓ := by
  have hℓ : 0 ≤ ℓ := by have := hmax m hm; omega
  have hsub : s ⊆ Finset.Icc 1 ℓ := fun x hx =>
    Finset.mem_Icc.2 ⟨by have := hmin x hx; omega, hmax x hx⟩
  have hsubd : posDiff s ⊆ Finset.Icc 1 ℓ :=
    (posDiff_subset_Icc hmin hmax).trans (Finset.Icc_subset_Icc_right (by omega))
  have hunion : s ∪ posDiff s ⊆ Finset.Icc 1 ℓ := Finset.union_subset hsub hsubd
  have hcard : (s ∪ posDiff s).card ≤ (Finset.Icc 1 ℓ).card :=
    Finset.card_le_card hunion
  rw [Finset.card_union_of_disjoint (disjoint_posDiff_of_isSumFree hsf)] at hcard
  have hIcc : (Finset.Icc 1 ℓ).card = ℓ.toNat := by
    rw [Int.card_Icc]
    omega
  rw [hIcc] at hcard
  have hcast : ((s.card + (posDiff s).card : ℕ) : ℤ) ≤ (ℓ.toNat : ℤ) := by
    exact_mod_cast hcard
  rw [Nat.cast_add, Int.toNat_of_nonneg hℓ] at hcast
  exact hcast

/-! ### The Freiman bound applied to the translate `s − m` -/

/-- The difference set is invariant under translation. -/
theorem image₂_sub_translate (s : Finset ℤ) (t : ℤ) :
    (s.image (· - t)).image₂ (· - ·) (s.image (· - t)) =
      s.image₂ (· - ·) s := by
  ext d
  simp only [Finset.mem_image₂, Finset.mem_image]
  constructor
  · rintro ⟨a, ⟨a', ha', rfl⟩, b, ⟨b', hb', rfl⟩, rfl⟩
    exact ⟨a', ha', b', hb', by ring⟩
  · rintro ⟨x, hx, y, hy, rfl⟩
    exact ⟨x - t, ⟨x, hx, rfl⟩, y - t, ⟨y, hy, rfl⟩, by ring⟩

/-- Applying `Freiman3k4` to the translate `A = s − m`, whose difference set
coincides with `s − s` and whose gcd condition is that of `s`. -/
theorem freiman_applied (hF : Freiman3k4) {s : Finset ℤ} {m ℓ : ℤ}
    (hmm : m ∈ s) (hℓm : ℓ ∈ s)
    (hmin : ∀ x ∈ s, m ≤ x) (hmax : ∀ x ∈ s, x ≤ ℓ)
    (hgcd : ∀ d : ℤ, 2 ≤ d → ∃ x ∈ s, ∃ y ∈ s, ¬ d ∣ x - y) :
    min ((ℓ - m) + (s.card : ℤ)) (3 * (s.card : ℤ) - 3) ≤
      ((s.image₂ (· - ·) s).card : ℤ) := by
  set A := s.image (· - m) with hA
  have hcardA : A.card = s.card :=
    Finset.card_image_of_injective _ sub_left_injective
  have h0 : 0 ∈ A := Finset.mem_image.2 ⟨m, hmm, by ring⟩
  have hL : ℓ - m ∈ A := Finset.mem_image.2 ⟨ℓ, hℓm, rfl⟩
  have hmem : ∀ x ∈ A, 0 ≤ x ∧ x ≤ ℓ - m := by
    intro x hx
    obtain ⟨x', hx', rfl⟩ := Finset.mem_image.1 hx
    have := hmin x' hx'; have := hmax x' hx'
    omega
  have hgcd' : ∀ d : ℤ, 2 ≤ d → ∃ x ∈ A, ∃ y ∈ A, ¬ d ∣ x - y := by
    intro d hd
    obtain ⟨x, hx, y, hy, hdxy⟩ := hgcd d hd
    refine ⟨x - m, Finset.mem_image.2 ⟨x, hx, rfl⟩,
      y - m, Finset.mem_image.2 ⟨y, hy, rfl⟩, ?_⟩
    have : (x - m) - (y - m) = x - y := by ring
    rwa [this]
  have hdiff : A.image₂ (· - ·) A = s.image₂ (· - ·) s :=
    image₂_sub_translate s m
  have h := hF A (ℓ - m) h0 hL hmem hgcd'
  rw [hcardA, hdiff] at h
  exact h

/-! ### The gcd condition for large mixed sets -/

/-- For `a ≥ 0` and `d ≥ c ≥ 1`, `a / d ≤ a / c`. -/
theorem ediv_le_ediv_denom {a c d : ℤ} (ha : 0 ≤ a) (hc : 1 ≤ c) (hcd : c ≤ d) :
    a / d ≤ a / c := by
  have hd : 0 < d := by omega
  have h0 : 0 ≤ a / d := Int.ediv_nonneg ha (le_of_lt hd)
  have hmul : d * (a / d) ≤ a := by
    have h := Int.emod_add_mul_ediv a d
    have hmod : 0 ≤ a % d := Int.emod_nonneg a (ne_of_gt hd)
    omega
  have h1 : (a / d) * c ≤ (a / d) * d := mul_le_mul_of_nonneg_left hcd h0
  have h2 : (a / d) * d ≤ a := by rw [mul_comm]; exact hmul
  rw [Int.le_ediv_iff_mul_le (by omega : 0 < c)]
  exact le_trans h1 h2

/-- If all elements of `s` are congruent to `m = min s` modulo `d ≥ 1`, then
`|s| ≤ (ℓ − m)/d + 1`: the map `x ↦ (x − m)/d` embeds `s` into
`[0, (ℓ − m)/d]`. -/
theorem card_le_of_eq_mod {s : Finset ℤ} {m ℓ d : ℤ} (hd : 1 ≤ d)
    (hmin : ∀ x ∈ s, m ≤ x) (hmax : ∀ x ∈ s, x ≤ ℓ)
    (hm : m ∈ s) (hcong : ∀ x ∈ s, ∀ y ∈ s, d ∣ x - y) :
    (s.card : ℤ) ≤ (ℓ - m) / d + 1 := by
  have hdiv : ∀ x ∈ s, d ∣ x - m := fun x hx => hcong x hx m hm
  have hdpos : 0 < d := by omega
  have hmap : ∀ x ∈ s, (x - m) / d ∈ Finset.Icc 0 ((ℓ - m) / d) := by
    intro x hx
    have h0 : 0 ≤ x - m := by have := hmin x hx; omega
    have h1 : x - m ≤ ℓ - m := by have := hmax x hx; omega
    rw [Finset.mem_Icc]
    refine ⟨Int.ediv_nonneg h0 (le_of_lt hdpos), ?_⟩
    rw [Int.le_ediv_iff_mul_le hdpos, Int.ediv_mul_cancel (hdiv x hx)]
    exact h1
  have hinj : Set.InjOn (fun x => (x - m) / d) s := by
    intro x hx y hy hxy
    have hxm := Int.ediv_mul_cancel (hdiv x hx)
    have hym := Int.ediv_mul_cancel (hdiv y hy)
    have hxy' : (x - m) / d = (y - m) / d := hxy
    have hsub : x - m = y - m := by rw [← hxm, hxy', hym]
    omega
  have hcard := Finset.card_le_card_of_injOn (fun x => (x - m) / d) hmap hinj
  have hIcc : ((Finset.Icc (0 : ℤ) ((ℓ - m) / d)).card : ℤ) = (ℓ - m) / d + 1 := by
    have h := Int.card_Icc_of_le (a := (0 : ℤ)) (b := (ℓ - m) / d) (by
      have h0 : 0 ≤ ℓ - m := by have := hmax m hm; have := hmin m hm; omega
      have := Int.ediv_nonneg h0 (le_of_lt hdpos)
      omega)
    omega
  have hcast : (s.card : ℤ) ≤ ((Finset.Icc (0 : ℤ) ((ℓ - m) / d)).card : ℤ) := by
    exact_mod_cast hcard
  omega

/-- A large mixed set has no common difference `d ≥ 2`: for every `d ≥ 2` there
are two elements of `s` whose difference is not divisible by `d`. -/
theorem gcd_one {s : Finset ℤ} {m ℓ : ℤ}
    (hmin : ∀ x ∈ s, m ≤ x) (hmax : ∀ x ∈ s, x ≤ ℓ) (hm : m ∈ s) (hm1 : 1 ≤ m)
    (he : ∃ e ∈ s, e % 2 = 0) (ho : ∃ o ∈ s, o % 2 = 1)
    (ha : 2 * ℓ + 5 < 5 * (s.card : ℤ)) :
    ∀ d : ℤ, 2 ≤ d → ∃ x ∈ s, ∃ y ∈ s, ¬ d ∣ x - y := by
  intro d hd
  by_contra hcon
  push Not at hcon
  rcases eq_or_lt_of_le hd with hd2 | hd3
  · -- `d = 2`: an even and an odd element have an odd difference.
    subst hd2
    obtain ⟨e, he, hee⟩ := he
    obtain ⟨o, ho, hoe⟩ := ho
    have h2 : 2 ∣ e - o := hcon e he o ho
    omega
  · -- `d ≥ 3`: `s` would sit in one residue class, so `a ≤ (ℓ−m)/3 + 1`.
    have hcard := card_le_of_eq_mod (by omega : 1 ≤ d) hmin hmax hm hcon
    have h0lm : 0 ≤ ℓ - m := by have := hmax m hm; omega
    have hle : (ℓ - m) / d ≤ (ℓ - m) / 3 :=
      ediv_le_ediv_denom h0lm (by omega) (by omega)
    omega

/-- **The Freiman consequence.** For a large mixed sum-free set `s ⊆ [m, ℓ]`
with `gcd(s) = 1`, either `s` is sparse (`5a ≤ 2ℓ + 4`, the `3a − 3` bound)
or it is dense and `m ≥ 3a − ℓ − 1` (the `ℓ + a` bound). -/
theorem freiman_consequence (hF : Freiman3k4) {s : Finset ℤ} {m ℓ : ℤ}
    (hsf : IsSumFree s) (hne : s.Nonempty)
    (hmm : m ∈ s) (hℓm : ℓ ∈ s)
    (hmin : ∀ x ∈ s, m ≤ x) (hmax : ∀ x ∈ s, x ≤ ℓ) (hm1 : 1 ≤ m)
    (he : ∃ e ∈ s, e % 2 = 0) (ho : ∃ o ∈ s, o % 2 = 1)
    (ha : 2 * ℓ + 5 < 5 * (s.card : ℤ)) :
    5 * (s.card : ℤ) ≤ 2 * ℓ + 4 ∨ m ≥ 3 * (s.card : ℤ) - ℓ - 1 := by
  have hgcd := gcd_one hmin hmax hmm hm1 he ho ha
  have hF' := freiman_applied hF hmm hℓm hmin hmax hgcd
  have hcard := card_image_sub_self hne
  have hpd := card_add_posDiff_le hsf hmin hmax hmm hm1
  have hss : ((s.image₂ (· - ·) s).card : ℤ) ≤ 2 * ℓ - 2 * (s.card : ℤ) + 1 := by
    have hcast : ((s.image₂ (· - ·) s).card : ℤ) = 2 * (posDiff s).card + 1 := by
      exact_mod_cast hcard
    omega
  have hmin_le := hF'.trans hss
  rw [min_le_iff] at hmin_le
  rcases hmin_le with h | h
  · right; omega
  · left; omega

/-! ### Translate counting in intervals (DFST Proposition 2.1 (vi)/(vii)) -/

/-- For a sum-free `s` containing `m`, the `+m` translate of `s ∩ [a,b]` avoids
`s`, so `|s ∩ [a,b]| + |s ∩ [a+m, b+m]| ≤ b − a + 1`. -/
theorem card_Icc_add_Icc_shift {s : Finset ℤ} {m a b : ℤ} (hsf : IsSumFree s)
    (hm : m ∈ s) (hab : a ≤ b) :
    (s ∩ Finset.Icc a b).card + (s ∩ Finset.Icc (a + m) (b + m)).card ≤
      b - a + 1 := by
  classical
  have hdisj : Disjoint (s ∩ Finset.Icc (a + m) (b + m))
      ((s ∩ Finset.Icc a b).image (· + m)) := by
    rw [Finset.disjoint_left]
    intro x hxC hxB
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hxB
    have hyA := (Finset.mem_inter.1 hy).1
    have : y + m ∉ s := hsf y hyA m hm
    exact this (Finset.mem_inter.1 hxC).1
  have hsub : (s ∩ Finset.Icc (a + m) (b + m)) ∪
      (s ∩ Finset.Icc a b).image (· + m) ⊆ Finset.Icc (a + m) (b + m) := by
    intro x hx
    rcases Finset.mem_union.1 hx with h | h
    · exact (Finset.mem_inter.1 h).2
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 h
      have := Finset.mem_Icc.1 (Finset.mem_inter.1 hy).2
      rw [Finset.mem_Icc]
      omega
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj,
    Finset.card_image_of_injective _ (add_left_injective m)] at hcard
  have hIcc : ((Finset.Icc (a + m) (b + m)).card : ℤ) = b - a + 1 := by
    have h := Int.card_Icc_of_le (a := a + m) (b := b + m) (by omega)
    omega
  have hcardZ : ((s ∩ Finset.Icc (a + m) (b + m)).card +
      (s ∩ Finset.Icc a b).card : ℤ) ≤
      ((Finset.Icc (a + m) (b + m)).card : ℤ) := by
    exact_mod_cast hcard
  rw [hIcc] at hcardZ
  omega

/-- The `−m` variant: `|s ∩ [c,d]| + |s ∩ [c−m, d−m]| ≤ d − c + 1` when `m ∈ s`. -/
theorem card_Icc_add_Icc_shift_neg {s : Finset ℤ} {m c d : ℤ} (hsf : IsSumFree s)
    (hm : m ∈ s) (hcd : c ≤ d) :
    (s ∩ Finset.Icc c d).card + (s ∩ Finset.Icc (c - m) (d - m)).card ≤
      d - c + 1 := by
  classical
  have hdisj : Disjoint (s ∩ Finset.Icc (c - m) (d - m))
      ((s ∩ Finset.Icc c d).image (· - m)) := by
    rw [Finset.disjoint_left]
    intro x hxC hxB
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hxB
    have hyA := (Finset.mem_inter.1 hy).1
    have hxA := (Finset.mem_inter.1 hxC).1
    have : (y - m) + m ∉ s := hsf (y - m) hxA m hm
    have hym : (y - m) + m = y := by ring
    rw [hym] at this
    exact this hyA
  have hsub : (s ∩ Finset.Icc (c - m) (d - m)) ∪
      (s ∩ Finset.Icc c d).image (· - m) ⊆ Finset.Icc (c - m) (d - m) := by
    intro x hx
    rcases Finset.mem_union.1 hx with h | h
    · exact (Finset.mem_inter.1 h).2
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 h
      have := Finset.mem_Icc.1 (Finset.mem_inter.1 hy).2
      rw [Finset.mem_Icc]
      omega
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj,
    Finset.card_image_of_injective _ sub_left_injective] at hcard
  have hIcc : ((Finset.Icc (c - m) (d - m)).card : ℤ) = d - c + 1 := by
    have h := Int.card_Icc_of_le (a := c - m) (b := d - m) (by omega)
    omega
  have hcardZ : ((s ∩ Finset.Icc (c - m) (d - m)).card +
      (s ∩ Finset.Icc c d).card : ℤ) ≤
      ((Finset.Icc (c - m) (d - m)).card : ℤ) := by
    exact_mod_cast hcard
  rw [hIcc] at hcardZ
  omega

/-- DFST Prop 2.1 (vii): for a sum-free `s` containing `m`, any interval
`]u, u+2m]` of length `2m` contains at most `m` elements of `s`. -/
theorem card_Ioc_le {s : Finset ℤ} {m u : ℤ} (hsf : IsSumFree s) (hm : m ∈ s)
    (hm1 : 1 ≤ m) :
    (s ∩ Finset.Icc (u + 1) (u + 2 * m)).card ≤ m := by
  have hshift := card_Icc_add_Icc_shift hsf hm (a := u + 1) (b := u + m) (by omega)
  -- split `Icc (u+1) (u+2m)` at `u+m`
  have hsplit : s ∩ Finset.Icc (u + 1) (u + 2 * m) ⊆
      (s ∩ Finset.Icc (u + 1) (u + m)) ∪ (s ∩ Finset.Icc (u + m + 1) (u + 2 * m)) := by
    intro x hx
    have h1 := Finset.mem_inter.1 hx
    have hxI := Finset.mem_Icc.1 h1.2
    rw [Finset.mem_union]
    by_cases hx2 : x ≤ u + m
    · left
      rw [Finset.mem_inter]
      refine ⟨h1.1, ?_⟩
      rw [Finset.mem_Icc]
      omega
    · right
      rw [Finset.mem_inter]
      refine ⟨h1.1, ?_⟩
      rw [Finset.mem_Icc]
      omega
  have hcard := Finset.card_le_card hsplit
  have hunion := Finset.card_union_le
    (s ∩ Finset.Icc (u + 1) (u + m)) (s ∩ Finset.Icc (u + m + 1) (u + 2 * m))
  -- `card_Icc_add_Icc_shift` bounds the sum
  have hkey : ((s ∩ Finset.Icc (u + 1) (u + m)).card : ℤ) +
      ((s ∩ Finset.Icc (u + m + 1) (u + 2 * m)).card : ℤ) ≤ m := by
    have h' := hshift
    have heq : u + 1 + m = u + m + 1 ∧ u + m + m = u + 2 * m := ⟨by ring, by ring⟩
    rw [heq.1, heq.2] at h'
    have hbound : (u + m) - (u + 1) + 1 = m := by ring
    rw [hbound] at h'
    have hadd : ((s ∩ Finset.Icc (u + 1) (u + m)).card +
        (s ∩ Finset.Icc (u + m + 1) (u + 2 * m)).card : ℤ) =
        ((s ∩ Finset.Icc (u + 1) (u + m)).card : ℤ) +
        ((s ∩ Finset.Icc (u + m + 1) (u + 2 * m)).card : ℤ) := by
      exact_mod_cast Nat.cast_add _ _
    rw [hadd] at h'
    exact h'
  calc ((s ∩ Finset.Icc (u + 1) (u + 2 * m)).card : ℤ)
      ≤ (((s ∩ Finset.Icc (u + 1) (u + m)) ∪
          (s ∩ Finset.Icc (u + m +1) (u + 2 * m))).card : ℤ) := by
        exact_mod_cast hcard
    _ ≤ ((s ∩ Finset.Icc (u + 1) (u + m)).card : ℤ) +
        ((s ∩ Finset.Icc (u + m + 1) (u + 2 * m)).card : ℤ) := by
        exact_mod_cast hunion
    _ ≤ m := hkey

/-- If `3m > M`, then `s ⊆ [m,M]` has `|s| ≤ m` (the minimum dominates the
cardinality), giving the "large minimum" alternative. -/
theorem card_le_min_of_third {s : Finset ℤ} {m M : ℤ} (hsf : IsSumFree s)
    (hmm : m ∈ s) (hmin : ∀ x ∈ s, m ≤ x) (hmax : ∀ x ∈ s, x ≤ M)
    (hm3 : M < 3 * m) (hm1 : 1 ≤ m) :
    (s.card : ℤ) ≤ m := by
  -- `s ⊆ [M-2m+1, M]` since `m > M-2m`
  have hsub : s ⊆ s ∩ Finset.Icc (M - 2 * m + 1) M := by
    intro x hx
    rw [Finset.mem_inter]
    refine ⟨hx, ?_⟩
    rw [Finset.mem_Icc]
    have hxm := hmin x hx
    have hxM := hmax x hx
    omega
  have hbound := card_Ioc_le hsf hmm hm1 (u := M - 2 * m)
  have heq : M - 2 * m + 1 = (M - 2 * m) + 1 ∧ M - 2 * m + 2 * m = M :=
    ⟨by ring, by ring⟩
  have hcard : (s ∩ Finset.Icc (M - 2 * m + 1) M).card ≤ m := by
    have h' := hbound
    have hrew : (M - 2 * m) + 1 = M - 2 * m + 1 ∧ (M - 2 * m) + 2 * m = M :=
      ⟨by ring, by ring⟩
    rw [hrew.1, hrew.2] at h'
    exact h'
  have hsub' : s ⊆ Finset.Icc (M - 2 * m + 1) M := by
    intro x hx
    have := hsub hx
    exact (Finset.mem_inter.1 this).2
  calc (s.card : ℤ)
      = ((s ∩ Finset.Icc (M - 2 * m + 1) M).card : ℤ) := by
        congr 1
        rw [Finset.inter_eq_left.2 hsub']
    _ ≤ m := by exact_mod_cast hcard

/-! ### The bridge theorem: `Freiman3k4 → DFSTMixed → DFST` -/

/-- Sumset lower bound in `ℤ`: `2|B| − 1 ≤ |B + B|`.  The translates
`min B + B` and `B + max B` lie in `B + B` and overlap in exactly one
point (`min B + max B`). -/
theorem two_mul_card_sub_one_le_card_image₂_add {B : Finset ℤ} (hne : B.Nonempty) :
    2 * (B.card : ℤ) ≤ (B.image₂ (· + ·) B).card + 1 := by
  classical
  set bmin := B.min' hne with hbmindef
  set bmax := B.max' hne with hbmaxdef
  have hbmin : bmin ∈ B := B.min'_mem hne
  have hbmax : bmax ∈ B := B.max'_mem hne
  have hsub : B.image (fun x => bmin + x) ∪ B.image (fun x => x + bmax) ⊆
      B.image₂ (· + ·) B := by
    intro x hx
    rcases Finset.mem_union.1 hx with h | h
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 h
      exact Finset.mem_image₂.2 ⟨bmin, hbmin, y, hy, rfl⟩
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 h
      exact Finset.mem_image₂.2 ⟨y, hy, bmax, hbmax, rfl⟩
  have hcard1 : (B.image fun x => bmin + x).card = B.card :=
    Finset.card_image_of_injective _ (add_right_injective bmin)
  have hcard2 : (B.image fun x => x + bmax).card = B.card :=
    Finset.card_image_of_injective _ (add_left_injective bmax)
  have hinter : B.image (fun x => bmin + x) ∩ B.image (fun x => x + bmax) ⊆
      {bmin + bmax} := by
    intro z hz
    obtain ⟨h1, h2⟩ := Finset.mem_inter.1 hz
    obtain ⟨x, hx, hzx⟩ := Finset.mem_image.1 h1
    obtain ⟨y, hy, hzy⟩ := Finset.mem_image.1 h2
    have hxle := B.le_max' x hx
    have hyge := B.min'_le y hy
    have hz : z = bmin + bmax := by omega
    exact Finset.mem_singleton.2 hz
  have hcardle := Finset.card_le_card hsub
  have hcap : (B.image (fun x => bmin + x) ∩ B.image (fun x => x + bmax)).card ≤ 1 :=
    (Finset.card_le_card hinter).trans (by simp)
  have hunion := Finset.card_union_add_card_inter
    (B.image fun x => bmin + x) (B.image fun x => x + bmax)
  omega

/-- **The Freiman–DFST bridge.**  Under Freiman's small-doubling
hypothesis `Freiman3k4`, the DFST trichotomy holds for mixed-parity
low-minimum sum-free sets — this is exactly the Deshouillers–Freiman–Sós
argument at the sharp `2n/5` threshold.

*Proof.*  Let `m = min s`, `ℓ = max s`, `k = |s|`.  We may assume `m < k`
(otherwise alternative (iii)) and `5k > 2n + 5` (otherwise (i)).
Freiman applied to the translate `s − m` (whose difference gcd is `1` by
`gcd_one`) gives `min (ℓ−m+k) (3k−3) ≤ |s−s| = 2|posDiff s| + 1`, and the
disjointness `s ∩ posDiff s = ∅` inside `[1,ℓ]` gives `k + |posDiff s| ≤ ℓ`.
The `3k−3` branch then yields `5k ≤ 2ℓ+4`, contradiction.  In the
`ℓ−m+k` branch we get `3k ≤ ℓ+m+1`, hence `5m ≥ ℓ+13`: the set is in the
"large minimum" regime.  If `ℓ ≤ 3m`, the interval-translate bound
`card_Ioc_le` gives `k ≤ m+1`, again a contradiction.  If `ℓ ≥ 3m+1`, the
four-interval covering
`[m,v] ∪ (v,t] ∪ (ℓ−2m,ℓ] ∪ [2m,v+m]` with `v = ⌈(ℓ−m)/2⌉`, `t = ⌊ℓ/2⌋`,
combined with the disjointness of `2B` (`B = s∩(v,t]`) from `s` and from
`posDiff s`, yields `7k ≤ 3ℓ−m+9`; together with `m ≥ 3k−ℓ−1` this gives
`5k ≤ 2ℓ+5`, contradicting `5k ≥ 2n+6 ≥ 2ℓ+6`. -/
theorem dfstMixed_of_freiman3k4 (hF : Freiman3k4) : DFSTMixed := by
  apply Filter.Eventually.of_forall
  intro n s hsub hsf hmin' heven hodd
  obtain ⟨m, hmm, hmin, h3m⟩ := hmin'
  obtain ⟨e, he, hep⟩ := heven
  obtain ⟨o, ho, hop⟩ := hodd
  by_cases hsmall : ∀ x ∈ s, (s.card : ℤ) ≤ x
  · exact Or.inr hsmall
  · left
    push Not at hsmall
    obtain ⟨x₀, hx₀s, hx₀k⟩ := hsmall
    by_contra hbig
    have hne : s.Nonempty := ⟨m, hmm⟩
    set ℓ : ℤ := s.max' hne with hℓdef
    have hℓm : ℓ ∈ s := s.max'_mem hne
    have hmax : ∀ x ∈ s, x ≤ ℓ := fun x hx => s.le_max' x hx
    have hm1 : 1 ≤ m := (Finset.mem_Icc.1 (hsub hmm)).1
    have hℓn : ℓ ≤ (n : ℤ) := (Finset.mem_Icc.1 (hsub hℓm)).2
    have hmk : m < (s.card : ℤ) := lt_of_le_of_lt (hmin x₀ hx₀s) hx₀k
    have hbig' : (2 / 5 : ℝ) * (n : ℝ) + 1 < (s.card : ℝ) := not_le.1 hbig
    have h5k : 2 * (n : ℤ) + 6 ≤ 5 * (s.card : ℤ) := by
      have hr : (2 : ℝ) * (n : ℝ) + 5 < 5 * (s.card : ℝ) := by linarith
      have hr' : (2 : ℤ) * (n : ℤ) + 5 < 5 * (s.card : ℤ) := by exact_mod_cast hr
      omega
    -- The gcd condition (`s` is not contained in one residue class).
    have hgcd : ∀ d : ℤ, 2 ≤ d → ∃ x ∈ s, ∃ y ∈ s, ¬ d ∣ x - y :=
      gcd_one hmin hmax hmm hm1 ⟨e, he, hep⟩ ⟨o, ho, hop⟩ (by omega)
    have hF' := freiman_applied hF hmm hℓm hmin hmax hgcd
    have hcard : ((s.image₂ (· - ·) s).card : ℤ) = 2 * (posDiff s).card + 1 := by
      exact_mod_cast card_image_sub_self hne
    have hpd : (s.card : ℤ) + (posDiff s).card ≤ ℓ :=
      card_add_posDiff_le hsf hmin hmax hmm hm1
    have hdiff : min (ℓ - m + (s.card : ℤ)) (3 * (s.card : ℤ) - 3) ≤
        2 * ℓ - 2 * (s.card : ℤ) + 1 := by omega
    -- The `3k − 3` branch is immediately contradictory.
    rcases le_or_gt (3 * (s.card : ℤ) - 3) (ℓ - m + (s.card : ℤ)) with hA | hB
    · omega
    · -- `ℓ − m + k` branch: `3k ≤ ℓ + m + 1` and `5m ≥ ℓ + 13`.
      have hpd2 : ℓ - m + (s.card : ℤ) ≤ 2 * (posDiff s).card + 1 := by
        have hmin_eq : min (ℓ - m + (s.card : ℤ)) (3 * (s.card : ℤ) - 3) =
            ℓ - m + (s.card : ℤ) := min_eq_left (le_of_lt hB)
        omega
      have hB1 : 3 * (s.card : ℤ) ≤ ℓ + m + 1 := by omega
      have h5m : 5 * m ≥ ℓ + 13 := by omega
      rcases le_or_gt ℓ (3 * m) with hℓ3 | hℓ3
      · -- `ℓ ≤ 3m`: then `k ≤ m + 1`, contradicting `5k ≥ 6m + 8`.
        rcases lt_or_eq_of_le hℓ3 with hlt | heq
        · have hk := card_le_min_of_third hsf hmm hmin hmax hlt hm1
          omega
        · -- `ℓ = 3m` (kept as hypothesis `heq`; `ℓ` is `set`-bound).
          have hIoc := card_Ioc_le hsf hmm hm1 (u := m - 1)
          have heq1 : m - 1 + 1 = m := by ring
          have heq2 : m - 1 + 2 * m = 3 * m - 1 := by ring
          rw [heq1, heq2] at hIoc
          have hcover2 : s ⊆ (s ∩ Finset.Icc m (3 * m - 1)) ∪ {3 * m} := by
            intro x hx
            have hxm := hmin x hx
            have hxM := hmax x hx
            rw [Finset.mem_union]
            rcases le_or_gt x (3 * m - 1) with hx' | hx'
            · exact Or.inl (Finset.mem_inter.2 ⟨hx, Finset.mem_Icc.2 ⟨hxm, hx'⟩⟩)
            · exact Or.inr (Finset.mem_singleton.2 (by omega))
          have hcard2 : (s.card : ℤ) ≤ m + 1 := by
            have h1 := Finset.card_le_card hcover2
            have h2 : (((s ∩ Finset.Icc m (3 * m - 1)) ∪ {3 * m} : Finset ℤ).card : ℤ) ≤
                m + 1 := by
              have h3 := Finset.card_union_le (s ∩ Finset.Icc m (3 * m - 1)) {3 * m}
              have h4 : (({3 * m} : Finset ℤ).card : ℤ) = 1 := by simp
              have h5 : ((s ∩ Finset.Icc m (3 * m - 1)).card : ℤ) ≤ m := hIoc
              have h6 : (((s ∩ Finset.Icc m (3 * m - 1)) ∪ {3 * m} : Finset ℤ).card : ℤ) ≤
                  ((s ∩ Finset.Icc m (3 * m - 1)).card : ℤ) +
                  (({3 * m} : Finset ℤ).card : ℤ) := by exact_mod_cast h3
              omega
            have h7 : (s.card : ℤ) ≤
                (((s ∩ Finset.Icc m (3 * m - 1)) ∪ {3 * m} : Finset ℤ).card : ℤ) := by
              exact_mod_cast h1
            omega
          omega
      · -- `ℓ ≥ 3m+1`: the four-interval covering argument.
        set v : ℤ := (ℓ - m + 1) / 2 with hvdef
        set t : ℤ := ℓ / 2 with htdef
        have hvbounds : ℓ - m ≤ 2 * v ∧ 2 * v ≤ ℓ - m + 1 := by
          have h2 : 2 * ((ℓ - m + 1) / 2) + (ℓ - m + 1) % 2 = ℓ - m + 1 := by
            rw [← hvdef]
            have := Int.mul_ediv_add_emod (ℓ - m + 1) 2
            omega
          have h3 : 0 ≤ (ℓ - m + 1) % 2 := Int.emod_nonneg _ (by norm_num)
          have h4 : (ℓ - m + 1) % 2 < 2 := Int.emod_lt_of_pos _ (by norm_num)
          omega
        have htbounds : 2 * t ≤ ℓ ∧ ℓ ≤ 2 * t + 1 := by
          have h2 : 2 * (ℓ / 2) + ℓ % 2 = ℓ := by
            rw [← htdef]
            have := Int.mul_ediv_add_emod ℓ 2
            omega
          have h3 : 0 ≤ ℓ % 2 := Int.emod_nonneg _ (by norm_num)
          have h4 : ℓ % 2 < 2 := Int.emod_lt_of_pos _ (by norm_num)
          omega
        have hvge : m ≤ v := by omega
        -- `|s ∩ [m,v]| + |s ∩ [2m, v+m]| ≤ v − m + 1` (translate by `m`).
        have hI14 := card_Icc_add_Icc_shift hsf hmm (a := m) (b := v) hvge
        -- `|s ∩ (ℓ−2m, ℓ]| ≤ m` (DFST Prop 2.1 (vii)).
        have hI3 := card_Ioc_le hsf hmm hm1 (u := ℓ - 2 * m)
        have hI3eq : ℓ - 2 * m + 2 * m = ℓ := by ring
        rw [hI3eq] at hI3
        -- The middle block `B = s ∩ (v, t]` and its doubling bound.
        set B : Finset ℤ := s ∩ Finset.Icc (v + 1) t with hBdef
        have hBbound : 4 * (B.card : ℤ) ≤ ℓ + m - 3 * (s.card : ℤ) + 3 := by
          by_cases hBne : B.Nonempty
          · set B2 := B.image₂ (· + ·) B with hB2def
            have hB2sub : B2 ⊆ Finset.Icc (ℓ - m + 2) ℓ := by
              intro z hz
              obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := Finset.mem_image₂.1 hz
              obtain ⟨-, hb₁I⟩ := Finset.mem_inter.1 hb₁
              obtain ⟨-, hb₂I⟩ := Finset.mem_inter.1 hb₂
              obtain ⟨hb₁l, hb₁u⟩ := Finset.mem_Icc.1 hb₁I
              obtain ⟨hb₂l, hb₂u⟩ := Finset.mem_Icc.1 hb₂I
              rw [Finset.mem_Icc]
              omega
            have hdisj1 : Disjoint s B2 := by
              rw [Finset.disjoint_left]
              intro x hx hx2
              obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := Finset.mem_image₂.1 hx2
              have hb₁s := (Finset.mem_inter.1 hb₁).1
              have hb₂s := (Finset.mem_inter.1 hb₂).1
              exact hsf b₁ hb₁s b₂ hb₂s hx
            have hdisj2 : Disjoint (posDiff s) B2 := by
              rw [Finset.disjoint_left]
              intro x hxp hx2
              obtain ⟨⟨a, ha, b, hb, rfl⟩, hxpos⟩ := mem_posDiff.1 hxp
              obtain ⟨b₁, hb₁, b₂, hb₂, h12⟩ := Finset.mem_image₂.1 hx2
              obtain ⟨-, hb₁I⟩ := Finset.mem_inter.1 hb₁
              obtain ⟨-, hb₂I⟩ := Finset.mem_inter.1 hb₂
              obtain ⟨hb₁l, hb₁u⟩ := Finset.mem_Icc.1 hb₁I
              obtain ⟨hb₂l, hb₂u⟩ := Finset.mem_Icc.1 hb₂I
              have hale := hmax a ha
              have hbge := hmin b hb
              omega
            have hdisj3 : Disjoint s (posDiff s) := disjoint_posDiff_of_isSumFree hsf
            have hunion : s ∪ posDiff s ∪ B2 ⊆ Finset.Icc 1 ℓ := by
              intro x hx
              rcases Finset.mem_union.1 hx with h | hx2
              · rcases Finset.mem_union.1 h with hxs | hxp
                · rw [Finset.mem_Icc]
                  have hxm := hmin x hxs
                  have hxM := hmax x hxs
                  omega
                · have hthis := posDiff_subset_Icc hmin hmax hxp
                  rw [Finset.mem_Icc] at hthis ⊢
                  omega
              · have hthis := hB2sub hx2
                rw [Finset.mem_Icc] at hthis ⊢
                omega
            have hcount := Finset.card_le_card hunion
            rw [Finset.card_union_of_disjoint
                  (Finset.disjoint_union_left.2 ⟨hdisj1, hdisj2⟩),
              Finset.card_union_of_disjoint hdisj3, Int.card_Icc] at hcount
            have hcountZ : (s.card : ℤ) + (posDiff s).card + (B2.card : ℤ) ≤ ℓ := by
              have h1 : ((s.card + (posDiff s).card + B2.card : ℕ) : ℤ) ≤
                  ((ℓ + 1 - 1 : ℤ).toNat : ℤ) := by exact_mod_cast hcount
              have h2 : ((ℓ + 1 - 1 : ℤ).toNat : ℤ) = ℓ := by
                rw [Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ ℓ + 1 - 1)]
                ring
              rw [h2] at h1
              push_cast at h1
              omega
            have h2B : 2 * (B.card : ℤ) ≤ (B2.card : ℤ) + 1 :=
              two_mul_card_sub_one_le_card_image₂_add hBne
            omega
          · have hBe : B = ∅ := Finset.not_nonempty_iff_eq_empty.1 hBne
            rw [hBe, Finset.card_empty]
            omega
        -- The covering `s ⊆ [m,v] ∪ (v,t] ∪ (ℓ−2m,ℓ] ∪ [2m,v+m]`.
        have hsplit : s ⊆ (s ∩ Finset.Icc m v) ∪ (s ∩ Finset.Icc (v + 1) t) ∪
            (s ∩ Finset.Icc (ℓ - 2 * m + 1) ℓ) ∪ (s ∩ Finset.Icc (m + m) (v + m)) := by
          intro x hx
          have hxm := hmin x hx
          have hxM := hmax x hx
          rcases le_or_gt x v with h | h
          · exact Finset.mem_union.2 (Or.inl (Or.inl (Or.inl
              (Finset.mem_inter.2 ⟨hx, Finset.mem_Icc.2 ⟨hxm, h⟩⟩))))
          · rcases le_or_gt x t with h2 | h2
            · exact Finset.mem_union.2 (Or.inl (Or.inl (Or.inr
                (Finset.mem_inter.2 ⟨hx, Finset.mem_Icc.2 ⟨by omega, h2⟩⟩))))
            · rcases le_or_gt x (ℓ - 2 * m) with h3 | h3
              · -- `t < x ≤ ℓ − 2m`: then `2m ≤ x ≤ v + m` by `5m ≥ ℓ`.
                exact Finset.mem_union.2 (Or.inr
                  (Finset.mem_inter.2 ⟨hx, Finset.mem_Icc.2 ⟨by omega, by omega⟩⟩))
              · exact Finset.mem_union.2 (Or.inl (Or.inr
                  (Finset.mem_inter.2 ⟨hx, Finset.mem_Icc.2 ⟨by omega, hxM⟩⟩)))
        -- Assemble: `k ≤ (v−m+1) + |B| + m`, so `7k ≤ 3ℓ − m + 9`,
        -- i.e. `5k ≤ 2ℓ + 5`, contradicting `5k ≥ 2n + 6 ≥ 2ℓ + 6`.
        have hcardle := Finset.card_le_card hsplit
        have hunion : ((s ∩ Finset.Icc m v) ∪ (s ∩ Finset.Icc (v + 1) t) ∪
            (s ∩ Finset.Icc (ℓ - 2 * m + 1) ℓ) ∪
            (s ∩ Finset.Icc (m + m) (v + m)) : Finset ℤ).card ≤
            (s ∩ Finset.Icc m v).card + (s ∩ Finset.Icc (v + 1) t).card +
            (s ∩ Finset.Icc (ℓ - 2 * m + 1) ℓ).card +
            (s ∩ Finset.Icc (m + m) (v + m)).card := by
          have h1 := Finset.card_union_le ((s ∩ Finset.Icc m v) ∪
            (s ∩ Finset.Icc (v + 1) t) ∪ (s ∩ Finset.Icc (ℓ - 2 * m + 1) ℓ))
            (s ∩ Finset.Icc (m + m) (v + m))
          have h2 := Finset.card_union_le ((s ∩ Finset.Icc m v) ∪
            (s ∩ Finset.Icc (v + 1) t)) (s ∩ Finset.Icc (ℓ - 2 * m + 1) ℓ)
          have h3 := Finset.card_union_le (s ∩ Finset.Icc m v)
            (s ∩ Finset.Icc (v + 1) t)
          omega
        have hI14' : ((s ∩ Finset.Icc m v).card : ℤ) +
            ((s ∩ Finset.Icc (m + m) (v + m)).card : ℤ) ≤ v - m + 1 := by
          have h := hI14
          push_cast at h ⊢
          exact h
        have hI3' : ((s ∩ Finset.Icc (ℓ - 2 * m + 1) ℓ).card : ℤ) ≤ m := hI3
        have hBcard : ((s ∩ Finset.Icc (v + 1) t).card : ℤ) = (B.card : ℤ) := by
          rw [hBdef]
        have hkZ : (s.card : ℤ) ≤ v + (B.card : ℤ) + 1 := by
          have h1 : (s.card : ℤ) ≤ (((s ∩ Finset.Icc m v) ∪
              (s ∩ Finset.Icc (v + 1) t) ∪ (s ∩ Finset.Icc (ℓ - 2 * m + 1) ℓ) ∪
              (s ∩ Finset.Icc (m + m) (v + m)) : Finset ℤ).card : ℤ) := by
            exact_mod_cast hcardle
          have h2 : (((s ∩ Finset.Icc m v) ∪ (s ∩ Finset.Icc (v + 1) t) ∪
              (s ∩ Finset.Icc (ℓ - 2 * m + 1) ℓ) ∪
              (s ∩ Finset.Icc (m + m) (v + m)) : Finset ℤ).card : ℤ) ≤
              ((s ∩ Finset.Icc m v).card : ℤ) + ((s ∩ Finset.Icc (v + 1) t).card : ℤ) +
              ((s ∩ Finset.Icc (ℓ - 2 * m + 1) ℓ).card : ℤ) +
              ((s ∩ Finset.Icc (m + m) (v + m)).card : ℤ) := by
            exact_mod_cast hunion
          omega
        omega

/-- **Freiman implies DFST.**  Combined with
`dfst_of_dfstMixed` (the unconditional reduction handling the
high-minimum, all-odd and all-even cases), this completes the bridge:
the DFST trichotomy follows from Freiman's `3k − 4` theorem in its
difference-set form. -/
theorem dfst_of_freiman3k4 (hF : Freiman3k4) : DFST :=
  dfst_of_dfstMixed (dfstMixed_of_freiman3k4 hF)

end JSP000728
