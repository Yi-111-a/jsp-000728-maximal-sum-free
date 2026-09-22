/-
# Attack on `ZKTightCount`: the difference analogue of the AFP coset-charge lemma

This file ports the coset-hole accounting of the Isabelle AFP
`Freiman_3k_4` development (lemma `sum_coset_lower_upper_inter_card`) to
**difference** sets, which is the setting of `ZKTightCount`.

## The charge lemma for differences

For `n > 0`, `H ⊆ [0, n)` closed under `(· + ·) % n` with `0 ∈ H` (the
integer lift of a subgroup of `ZMod n`), `b, c ∈ A ∩ [0, n)` in distinct
`H`-cosets (`(b − c) % n ∉ H`), and `R, S, K` the residues in `[0, n)` of
the `H`-cosets through `b`, `c` and `b − c` respectively,

  `|H| ≤ 1 + |K ∩ posDiff A ∩ (n − posDiff A)| + |R ∖ A| + |S ∖ A|`.

**Proof mechanism** (adapted from `sum_coset_lower_upper_inter_card`):
with `X = A ∩ R`, `Y = A ∩ S`, the difference set `D = X − Y` satisfies
`|D| ≥ |X| + |Y| − 1` (integer Cauchy–Davenport).  Every `d ∈ D` has
`d % n ∈ K`; splitting `D` into `D⁺ = D ∩ (0, n)` and `D⁻ = D ∩ (−n, 0)`
(with `0 ∉ D` since `R ∩ S = ∅`), we get `D⁺ ⊆ K ∩ posDiff A` and
`n + D⁻ ⊆ K ∩ (n − posDiff A)`.  Hence
`|D⁺| + |n + D⁻| ≤ |K| + |K ∩ posDiff A ∩ (n − posDiff A)|`, and
`|X| = |H| − |R ∖ A|`, `|Y| = |H| − |S ∖ A|` close the count.

Note that, unlike the sumset original, **no** `K ∩ A = ∅` hypothesis is
needed: a positive difference `d ∈ K` is automatically a both-direction
fibre when it also lies in `n − posDiff`, and these fibres land in the
both-direction set `zkT` (`charge_land_subset_zkT`).

## Contents

* `modTranslate` — the residues of an `H`-coset in `[0, n)`.
* `neg_emod_mem_of_add_closed` — `H` is negation-closed mod `n`.
* `card_image₂_sub_ge` — `|X − Y| ≥ |X| + |Y| − 1` for `X Y ⊆ ℤ`.
* `zk_cosDiff_charge` — the charge lemma above.
* `zk_cosDiff_charge_fiber` — fibre form: the `K`-both-direction fibres
  number at least `f_b + f_c − h − 1`.
* `charge_land_subset_zkT` — the charged fibres land in `zkT`.
-/

import JSPProblem.ZKBound2

namespace JSP000728

open Finset
open scoped Pointwise

/-- `a − a % n` is divisible by `n` (the `Int.emod_add_ediv_mul` identity). -/
private theorem dvd_sub_emod_self {n a : ℤ} : n ∣ a - a % n := by
  refine ⟨a / n, ?_⟩
  have h := Int.emod_add_ediv_mul a n
  rw [mul_comm n (a / n)]
  omega

/-! ### The `H`-coset residues in `[0, n)` -/

/-- The integer lift of the `H`-coset through `b`: the residues
`(b + h) % n` for `h ∈ H`, realised in `[0, n)`. -/
def modTranslate (n b : ℤ) (H : Finset ℤ) : Finset ℤ :=
  H.image fun h => (b + h) % n

theorem mem_modTranslate {n b : ℤ} {H : Finset ℤ} {x : ℤ} :
    x ∈ modTranslate n b H ↔ ∃ h ∈ H, (b + h) % n = x := by
  simp [modTranslate]

theorem modTranslate_mem_bounds {n b : ℤ} (hn : 0 < n) {H : Finset ℤ} {x : ℤ}
    (hx : x ∈ modTranslate n b H) : 0 ≤ x ∧ x < n := by
  obtain ⟨h, -, rfl⟩ := mem_modTranslate.1 hx
  exact ⟨Int.emod_nonneg _ (ne_of_gt hn), Int.emod_lt_of_pos _ hn⟩

/-- `(b + ·) % n` is injective on `H ⊆ [0, n)`, so `|modTranslate| = |H|`. -/
theorem card_modTranslate {n b : ℤ} (hn : 0 < n) {H : Finset ℤ}
    (hH : ∀ x ∈ H, 0 ≤ x ∧ x < n) : (modTranslate n b H).card = H.card := by
  apply Finset.card_image_of_injOn
  intro x hx y hy hxy
  obtain ⟨hx0, hxn⟩ := hH x hx
  obtain ⟨hy0, hyn⟩ := hH y hy
  rw [Int.emod_eq_emod_iff_emod_sub_eq_zero] at hxy
  have hdvd : n ∣ x - y := by
    rw [Int.dvd_iff_emod_eq_zero]
    have hh : (b + x - (b + y)) % n = 0 := hxy
    rwa [show b + x - (b + y) = x - y by ring] at hh
  obtain ⟨k, hk⟩ := hdvd
  have hk0 : k = 0 := by
    rcases lt_trichotomy k 0 with hkc | hkc | hkc
    · have : n * k ≤ n * (-1) := mul_le_mul_of_nonneg_left (by omega) (by omega)
      omega
    · exact hkc
    · have : n * 1 ≤ n * k := mul_le_mul_of_nonneg_left (by omega) (by omega)
      omega
  rw [hk0, mul_zero] at hk
  omega

/-- `b` itself is a residue of its own coset when `0 ∈ H` and `b ∈ [0, n)`. -/
theorem mem_modTranslate_self {n b : ℤ} (hb : 0 ≤ b ∧ b < n) {H : Finset ℤ}
    (h0 : 0 ∈ H) : b ∈ modTranslate n b H := by
  apply mem_modTranslate.2 ⟨0, h0, ?_⟩
  rw [add_zero, Int.emod_eq_of_lt hb.1 hb.2]

/-! ### `H` is negation-closed modulo `n` -/

/-- A mod-`n`-closed residue set `H` containing `0` is negation-closed:
`(−h) % n ∈ H` for `h ∈ H`.  Proof: the iterates `(j·h) % n` all lie in
`H`; by pigeonhole `(j₂ − j₁)·h ≡ 0` for some `j₁ < j₂ ≤ |H|`, whence
`((j₂ − j₁ − 1)·h) % n = (−h) % n ∈ H`. -/
theorem neg_emod_mem_of_add_closed {n : ℤ} {H : Finset ℤ}
    (h0 : 0 ∈ H) (hHadd : ∀ x ∈ H, ∀ y ∈ H, (x + y) % n ∈ H)
    {h : ℤ} (hh : h ∈ H) : (-h) % n ∈ H := by
  classical
  -- `(j • h) % n ∈ H` for every `j : ℕ`.
  have hmul : ∀ j : ℕ, ((j : ℤ) * h) % n ∈ H := by
    intro j
    induction j with
    | zero => simpa using h0
    | succ j ih =>
      have e : (((j + 1 : ℕ) : ℤ) * h) % n = (((j : ℤ) * h) % n + h) % n := by
        push_cast
        rw [add_mul, one_mul]
        exact (Int.emod_add_emod _ _ _).symm
      rw [e]
      exact hHadd _ ih _ hh
  -- Pigeonhole on `j ↦ (j·h) % n : range (|H| + 1) → H`.
  obtain ⟨j₁, -, j₂, -, hne, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to
      (s := Finset.range (H.card + 1)) (t := H)
      (f := fun j : ℕ => ((j : ℤ) * h) % n)
      (by rw [Finset.card_range]; exact Nat.lt_succ_self _)
      (fun j _ => hmul j)
  -- Key step: if `i < j` and `(i·h) % n = (j·h) % n`, then `(−h) % n ∈ H`.
  have key : ∀ i j : ℕ, i < j →
      ((i : ℤ) * h) % n = ((j : ℤ) * h) % n → (-h) % n ∈ H := by
    intro i j hij heq
    -- `n ∣ (j − i)·h`.
    have hdvd : n ∣ ((j : ℤ) - (i : ℤ)) * h := by
      rw [Int.dvd_iff_emod_eq_zero]
      have e : (((j : ℤ) - (i : ℤ)) * h) % n =
          (((j : ℤ) * h) % n - ((i : ℤ) * h) % n) % n := by
        rw [sub_mul, Int.sub_emod]
      rw [e, heq, sub_self]
      simp
    -- `(−h) % n = ((j − i − 1)·h) % n ∈ H`.
    have hk : (((j - i - 1 : ℕ) : ℤ) * h) % n = (-h) % n := by
      rw [Int.emod_eq_emod_iff_emod_sub_eq_zero, ← Int.dvd_iff_emod_eq_zero]
      have hcast : ((j - i - 1 : ℕ) : ℤ) = (j : ℤ) - (i : ℤ) - 1 := by
        rw [show j - i - 1 = j - (i + 1) by omega,
          Nat.cast_sub (by omega : i + 1 ≤ j)]
        push_cast
        ring
      rw [hcast]
      have hsplit : ((j : ℤ) - (i : ℤ) - 1) * h - -h = ((j : ℤ) - (i : ℤ)) * h :=
        by ring
      rw [hsplit]
      exact hdvd
    rw [← hk]
    exact hmul (j - i - 1)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact key j₁ j₂ hlt heq
  · exact key j₂ j₁ hgt heq.symm

/-- Residues of differences of coset elements lie in the difference coset:
`(x − y) % n ∈ modTranslate n ((b − c) % n) H` for `x ∈ b + H`, `y ∈ c + H`. -/
theorem sub_mem_modTranslate {n b c : ℤ} {H : Finset ℤ}
    (h0 : 0 ∈ H) (hHadd : ∀ x ∈ H, ∀ y ∈ H, (x + y) % n ∈ H)
    {x y : ℤ} (hx : x ∈ modTranslate n b H) (hy : y ∈ modTranslate n c H) :
    (x - y) % n ∈ modTranslate n ((b - c) % n) H := by
  obtain ⟨h₁, hh₁, he₁⟩ := mem_modTranslate.1 hx
  obtain ⟨h₂, hh₂, he₂⟩ := mem_modTranslate.1 hy
  have hneg : (-h₂) % n ∈ H := neg_emod_mem_of_add_closed h0 hHadd hh₂
  have hsub : (h₁ - h₂) % n ∈ H := by
    have e : (h₁ - h₂) % n = (h₁ + (-h₂) % n) % n := by
      rw [Int.emod_eq_emod_iff_emod_sub_eq_zero, ← Int.dvd_iff_emod_eq_zero]
      convert (dvd_sub_emod_self (a := -h₂)) using 1
      ring
    rw [e]
    exact hHadd _ hh₁ _ hneg
  apply mem_modTranslate.2 ⟨(h₁ - h₂) % n, hsub, ?_⟩
  rw [← he₁, ← he₂]
  have e : ((b - c) % n + (h₁ - h₂) % n) % n =
      ((b + h₁) % n - (c + h₂) % n) % n := by
    rw [← Int.add_emod, ← Int.sub_emod]
    congr 1
    ring
  exact e

/-! ### Two-set Cauchy–Davenport for integer differences -/

/-- **Two-set Cauchy–Davenport on `ℤ`, difference form.**  For nonempty
`X Y ⊆ ℤ`, `|X − Y| ≥ |X| + |Y| − 1`: the sets `X − max Y` and
`min X − Y` lie in `X − Y` and overlap only in `min X − max Y`. -/
theorem card_image₂_sub_ge {X Y : Finset ℤ} (hX : X.Nonempty) (hY : Y.Nonempty) :
    (X.card : ℤ) + Y.card - 1 ≤ (X.image₂ (· - ·) Y).card := by
  classical
  set xmax := X.max' hX
  set ymin := Y.min' hY
  have hxmax : xmax ∈ X := X.max'_mem hX
  have hymin : ymin ∈ Y := Y.min'_mem hY
  have hsub : X.image (· - ymin) ∪ Y.image (xmax - ·) ⊆
      X.image₂ (· - ·) Y := by
    intro z hz
    rcases Finset.mem_union.1 hz with h | h
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 h
      exact Finset.mem_image₂.2 ⟨x, hx, ymin, hymin, rfl⟩
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 h
      exact Finset.mem_image₂.2 ⟨xmax, hxmax, y, hy, rfl⟩
  have hcard1 : (X.image (· - ymin)).card = X.card :=
    Finset.card_image_of_injective _ (fun a b h => by omega)
  have hcard2 : (Y.image (xmax - ·)).card = Y.card :=
    Finset.card_image_of_injective _ (fun a b h => by omega)
  have hinter : X.image (· - ymin) ∩ Y.image (xmax - ·) ⊆ {xmax - ymin} := by
    intro z hz
    obtain ⟨h1, h2⟩ := Finset.mem_inter.1 hz
    obtain ⟨x, hx, hzx⟩ := Finset.mem_image.1 h1
    obtain ⟨y, hy, hzy⟩ := Finset.mem_image.1 h2
    have hxle := X.le_max' x hx
    have hyge := Y.min'_le y hy
    have hzz : z = xmax - ymin := by omega
    exact Finset.mem_singleton.2 hzz
  have hcardle := Finset.card_le_card hsub
  have hcap : (X.image (· - ymin) ∩ Y.image (xmax - ·)).card ≤ 1 :=
    (Finset.card_le_card hinter).trans (by simp)
  have hunion := Finset.card_union_add_card_inter
    (X.image (· - ymin)) (Y.image (xmax - ·))
  omega

/-! ### The charge lemma -/

/-- **The coset-charge lemma for difference sets.**  For `H ⊆ [0, n)`
closed under `(· + ·) % n` with `0 ∈ H`, and `b, c ∈ A ∩ [0, n)` lying in
*distinct* `H`-cosets (`(b − c) % n ∉ H`),

  `|H| ≤ 1 + |K ∩ posDiff A ∩ (n − posDiff A)| + |R ∖ A| + |S ∖ A|`

where `R, S, K` are the residue sets in `[0, n)` of the `H`-cosets through
`b`, `c` and `b − c`.  The charged set `K ∩ posDiff A ∩ (n − posDiff A)`
is a set of *both-direction* fibres: each of its elements is realised as
a difference of `A` in both directions. -/
theorem zk_cosDiff_charge {n : ℤ} (hn : 0 < n)
    {A H : Finset ℤ}
    (hH : ∀ x ∈ H, 0 ≤ x ∧ x < n)
    (h0 : 0 ∈ H)
    (hHadd : ∀ x ∈ H, ∀ y ∈ H, (x + y) % n ∈ H)
    {b c : ℤ} (hbA : b ∈ A) (hbn : 0 ≤ b ∧ b < n)
    (hcA : c ∈ A) (hcn : 0 ≤ c ∧ c < n)
    (hbc : (b - c) % n ∉ H) :
    (H.card : ℤ) ≤ 1 +
      ((modTranslate n ((b - c) % n) H ∩ posDiff A ∩
        (posDiff A).image (n - ·)).card : ℤ) +
      ((modTranslate n b H) \ A).card +
      ((modTranslate n c H) \ A).card := by
  classical
  set R := modTranslate n b H with hRdef
  set S := modTranslate n c H with hSdef
  set K := modTranslate n ((b - c) % n) H with hKdef
  set X := A ∩ R with hXdef
  set Y := A ∩ S with hYdef
  set D := X.image₂ (· - ·) Y with hDdef
  have hcardR : R.card = H.card := card_modTranslate hn hH
  have hcardS : S.card = H.card := card_modTranslate hn hH
  have hcardK : K.card = H.card := card_modTranslate hn hH
  have hbR : b ∈ R := mem_modTranslate_self hbn h0
  have hcS : c ∈ S := mem_modTranslate_self hcn h0
  have hXne : X.Nonempty := ⟨b, Finset.mem_inter.2 ⟨hbA, hbR⟩⟩
  have hYne : Y.Nonempty := ⟨c, Finset.mem_inter.2 ⟨hcA, hcS⟩⟩
  -- Distinct cosets: `R ∩ S = ∅`.
  have hRS : R ∩ S = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.2
    intro z hz
    obtain ⟨hzR, hzS⟩ := Finset.mem_inter.1 hz
    obtain ⟨h₁, hh₁, he₁⟩ := mem_modTranslate.1 hzR
    obtain ⟨h₂, hh₂, he₂⟩ := mem_modTranslate.1 hzS
    have hneg : (-h₁) % n ∈ H := neg_emod_mem_of_add_closed h0 hHadd hh₁
    have hsub : (h₂ - h₁) % n ∈ H := by
      have e : (h₂ - h₁) % n = (h₂ + (-h₁) % n) % n := by
        rw [Int.emod_eq_emod_iff_emod_sub_eq_zero, ← Int.dvd_iff_emod_eq_zero]
        convert (dvd_sub_emod_self (a := -h₁)) using 1
        ring
      rw [e]
      exact hHadd _ hh₂ _ hneg
    have hbcH : (b - c) % n ∈ H := by
      have e : (b - c) % n = (h₂ - h₁) % n := by
        rw [Int.emod_eq_emod_iff_emod_sub_eq_zero, ← Int.dvd_iff_emod_eq_zero]
        have hz : (b + h₁) % n = (c + h₂) % n := by rw [he₁, he₂]
        rw [Int.emod_eq_emod_iff_emod_sub_eq_zero,
          ← Int.dvd_iff_emod_eq_zero] at hz
        convert hz using 1
        ring
      rw [e]
      exact hsub
    exact hbc hbcH
  -- Hence `X ∩ Y = ∅` and `0 ∉ D`.
  have hXY : X ∩ Y = ∅ := by
    have hsub : X ∩ Y ⊆ R ∩ S := Finset.inter_subset_inter
      Finset.inter_subset_right Finset.inter_subset_right
    rw [hRS] at hsub
    exact Finset.subset_empty.1 hsub
  have h0D : (0 : ℤ) ∉ D := by
    intro hd
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.mem_image₂.1 hd
    have hxy' : x = y := by omega
    subst hxy'
    have hmem : x ∈ X ∩ Y := Finset.mem_inter.2 ⟨hx, hy⟩
    rw [hXY] at hmem
    exact Finset.notMem_empty _ hmem
  -- Bounds on `D`: elements lie in `(−n, n)`.
  have hDbnd : ∀ d ∈ D, -n < d ∧ d < n := by
    intro d hd
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.mem_image₂.1 hd
    have hxb := modTranslate_mem_bounds hn (Finset.mem_inter.1 hx).2
    have hyb := modTranslate_mem_bounds hn (Finset.mem_inter.1 hy).2
    omega
  -- The positive and negative parts of `D`.
  set Dpos := D.filter (0 < ·) with hDposdef
  set Dneg := D.filter (· < 0) with hDnegdef
  set Up := Dneg.image (n + ·) with hUpdef
  have hDsplit : D = Dpos ∪ Dneg := by
    ext d
    simp only [hDposdef, hDnegdef, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hd
      rcases lt_trichotomy d 0 with h | h | h
      · exact Or.inr ⟨hd, h⟩
      · subst h; exact absurd hd h0D
      · exact Or.inl ⟨hd, h⟩
    · rintro (⟨hd, -⟩ | ⟨hd, -⟩) <;> exact hd
  have hDdisj : Disjoint Dpos Dneg := by
    rw [Finset.disjoint_left]
    intro d hd hdneg
    obtain ⟨-, hpos⟩ := Finset.mem_filter.1 hd
    obtain ⟨-, hneg⟩ := Finset.mem_filter.1 hdneg
    omega
  have hDcard : D.card = Dpos.card + Dneg.card := by
    conv_lhs => rw [hDsplit]
    exact Finset.card_union_of_disjoint hDdisj
  have hUpcard : Up.card = Dneg.card :=
    Finset.card_image_of_injective _ (fun a b h => by omega)
  -- `D⁺ ⊆ K ∩ posDiff A`.
  have hDposK : Dpos ⊆ K := by
    intro z hz
    obtain ⟨hzD, hzpos⟩ := Finset.mem_filter.1 hz
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.mem_image₂.1 hzD
    have hKmem : (x - y) % n ∈ K := sub_mem_modTranslate h0 hHadd
      (Finset.mem_inter.1 hx).2 (Finset.mem_inter.1 hy).2
    have hzb : 0 ≤ z ∧ z < n := by
      have := hDbnd z hzD
      omega
    rw [← Int.emod_eq_of_lt hzb.1 hzb.2, ← hxy]
    exact hKmem
  have hDposP : Dpos ⊆ posDiff A := by
    intro z hz
    obtain ⟨hzD, hzpos⟩ := Finset.mem_filter.1 hz
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.mem_image₂.1 hzD
    exact mem_posDiff.2 ⟨⟨x, (Finset.mem_inter.1 hx).1, y,
      (Finset.mem_inter.1 hy).1, hxy⟩, by omega⟩
  -- `Up = n + D⁻ ⊆ K ∩ (n − posDiff A)`.
  have hUpK : Up ⊆ K := by
    intro z hz
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.1 hz
    obtain ⟨hdD, hdneg⟩ := Finset.mem_filter.1 hd
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.mem_image₂.1 hdD
    have hxb := modTranslate_mem_bounds hn (Finset.mem_inter.1 hx).2
    have hyb := modTranslate_mem_bounds hn (Finset.mem_inter.1 hy).2
    have hKmem : (x - y) % n ∈ K := sub_mem_modTranslate h0 hHadd
      (Finset.mem_inter.1 hx).2 (Finset.mem_inter.1 hy).2
    have hzb : 0 ≤ n + d ∧ n + d < n := by
      have := hDbnd d hdD
      omega
    rw [← Int.emod_eq_of_lt hzb.1 hzb.2]
    have e : (n + d) % n = (x - y) % n := by
      rw [show n + d = (x - y) + n by omega, Int.add_emod_right]
    rw [e]
    exact hKmem
  have hUpP : Up ⊆ (posDiff A).image (n - ·) := by
    intro z hz
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.1 hz
    obtain ⟨hdD, hdneg⟩ := Finset.mem_filter.1 hd
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.mem_image₂.1 hdD
    refine Finset.mem_image.2 ⟨y - x, ?_, by omega⟩
    exact mem_posDiff.2 ⟨⟨y, (Finset.mem_inter.1 hy).1, x,
      (Finset.mem_inter.1 hx).1, rfl⟩, by omega⟩
  -- The intersection `D⁺ ∩ Up` lands in the both-direction set `I`.
  set Iset := K ∩ posDiff A ∩ (posDiff A).image (n - ·) with hIsetdef
  have hI : Dpos ∩ Up ⊆ Iset := by
    intro z hz
    obtain ⟨hz1, hz2⟩ := Finset.mem_inter.1 hz
    exact Finset.mem_inter.2
      ⟨Finset.mem_inter.2 ⟨hDposK hz1, hDposP hz1⟩, hUpP hz2⟩
  have hUnionK : Dpos ∪ Up ⊆ K := Finset.union_subset hDposK hUpK
  -- Cardinality bookkeeping.
  have hcount : (Dpos.card : ℤ) + Up.card ≤ K.card + Iset.card := by
    have h1 := Finset.card_union_add_card_inter Dpos Up
    have h2 := Finset.card_le_card hUnionK
    have h3 := Finset.card_le_card hI
    omega
  have hCD := card_image₂_sub_ge hXne hYne
  have hXcard : X.card + (R \ A).card = R.card := by
    have hdisj : Disjoint X (R \ A) := by
      rw [Finset.disjoint_left]
      intro z hz hzsd
      obtain ⟨hzA, -⟩ := Finset.mem_inter.1 hz
      obtain ⟨-, hzA'⟩ := Finset.mem_sdiff.1 hzsd
      exact hzA' hzA
    have hunion : X ∪ (R \ A) = R := by
      ext z
      simp only [hXdef, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
      constructor
      · rintro (⟨hzA, hzR⟩ | ⟨hzR, -⟩) <;> exact hzR
      · intro hzR
        by_cases hzA : z ∈ A
        · exact Or.inl ⟨hzA, hzR⟩
        · exact Or.inr ⟨hzR, hzA⟩
    calc X.card + (R \ A).card = (X ∪ (R \ A)).card :=
          (Finset.card_union_of_disjoint hdisj).symm
      _ = R.card := by rw [hunion]
  have hYcard : Y.card + (S \ A).card = S.card := by
    have hdisj : Disjoint Y (S \ A) := by
      rw [Finset.disjoint_left]
      intro z hz hzsd
      obtain ⟨hzA, -⟩ := Finset.mem_inter.1 hz
      obtain ⟨-, hzA'⟩ := Finset.mem_sdiff.1 hzsd
      exact hzA' hzA
    have hunion : Y ∪ (S \ A) = S := by
      ext z
      simp only [hYdef, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
      constructor
      · rintro (⟨hzA, hzS⟩ | ⟨hzS, -⟩) <;> exact hzS
      · intro hzS
        by_cases hzA : z ∈ A
        · exact Or.inl ⟨hzA, hzS⟩
        · exact Or.inr ⟨hzS, hzA⟩
    calc Y.card + (S \ A).card = (Y ∪ (S \ A)).card :=
          (Finset.card_union_of_disjoint hdisj).symm
      _ = S.card := by rw [hunion]
  -- Assemble: `|X| + |Y| − 1 ≤ |D| = |D⁺| + |Up| ≤ |K| + |I|`.
  omega

/-! ### The fibre form of the charge lemma -/

/-- **Charge lemma, fibre form.**  Writing `f_b, f_c` for the number of
`A`-points in the `b`- and `c`-cosets, the number of both-direction
`posDiff` fibres in the `(b − c)`-coset `K` is at least `f_b + f_c − h − 1`. -/
theorem zk_cosDiff_charge_fiber {n : ℤ} (hn : 0 < n)
    {A H : Finset ℤ}
    (hH : ∀ x ∈ H, 0 ≤ x ∧ x < n)
    (h0 : 0 ∈ H)
    (hHadd : ∀ x ∈ H, ∀ y ∈ H, (x + y) % n ∈ H)
    {b c : ℤ} (hbA : b ∈ A) (hbn : 0 ≤ b ∧ b < n)
    (hcA : c ∈ A) (hcn : 0 ≤ c ∧ c < n)
    (hbc : (b - c) % n ∉ H) :
    ((A ∩ modTranslate n b H).card : ℤ) +
    ((A ∩ modTranslate n c H).card : ℤ) - H.card - 1 ≤
      ((modTranslate n ((b - c) % n) H ∩ posDiff A ∩
        (posDiff A).image (n - ·)).card : ℤ) := by
  classical
  set R := modTranslate n b H with hRdef
  set S := modTranslate n c H with hSdef
  set X := A ∩ R with hXdef
  set Y := A ∩ S with hYdef
  have hcharge := zk_cosDiff_charge hn hH h0 hHadd hbA hbn hcA hcn hbc
  have hcardR : R.card = H.card := card_modTranslate hn hH
  have hcardS : S.card = H.card := card_modTranslate hn hH
  have hXcard : X.card + (R \ A).card = R.card := by
    have hdisj : Disjoint X (R \ A) := by
      rw [Finset.disjoint_left]
      intro z hz hzsd
      obtain ⟨hzA, -⟩ := Finset.mem_inter.1 hz
      obtain ⟨-, hzA'⟩ := Finset.mem_sdiff.1 hzsd
      exact hzA' hzA
    have hunion : X ∪ (R \ A) = R := by
      ext z
      simp only [hXdef, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
      constructor
      · rintro (⟨hzA, hzR⟩ | ⟨hzR, -⟩) <;> exact hzR
      · intro hzR
        by_cases hzA : z ∈ A
        · exact Or.inl ⟨hzA, hzR⟩
        · exact Or.inr ⟨hzR, hzA⟩
    calc X.card + (R \ A).card = (X ∪ (R \ A)).card :=
          (Finset.card_union_of_disjoint hdisj).symm
      _ = R.card := by rw [hunion]
  have hYcard : Y.card + (S \ A).card = S.card := by
    have hdisj : Disjoint Y (S \ A) := by
      rw [Finset.disjoint_left]
      intro z hz hzsd
      obtain ⟨hzA, -⟩ := Finset.mem_inter.1 hz
      obtain ⟨-, hzA'⟩ := Finset.mem_sdiff.1 hzsd
      exact hzA' hzA
    have hunion : Y ∪ (S \ A) = S := by
      ext z
      simp only [hYdef, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
      constructor
      · rintro (⟨hzA, hzS⟩ | ⟨hzS, -⟩) <;> exact hzS
      · intro hzS
        by_cases hzA : z ∈ A
        · exact Or.inl ⟨hzA, hzS⟩
        · exact Or.inr ⟨hzS, hzA⟩
    calc Y.card + (S \ A).card = (Y ∪ (S \ A)).card :=
          (Finset.card_union_of_disjoint hdisj).symm
      _ = S.card := by rw [hunion]
  omega

/-- The charged fibres land in the both-direction set `T = P ∩ (l − P)`:
any `r ∈ K ∩ posDiff A₀ ∩ (l − posDiff A₀)` satisfies `r ∈ P` (via the
`posDiff` summand) and `r ∈ l − P` (as `r = l − p` for `p ∈ posDiff`). -/
theorem charge_land_subset_zkT {l : ℤ} {A₀ H : Finset ℤ} {k : ℤ} :
    modTranslate l k H ∩ posDiff A₀ ∩ (posDiff A₀).image (l - ·) ⊆
      (posDiff A₀ ∪ (A₀.erase 0).image (l - ·)) ∩
        ((posDiff A₀ ∪ (A₀.erase 0).image (l - ·)).image (l - ·)) := by
  intro r hr
  obtain ⟨hrKP, hrI⟩ := Finset.mem_inter.1 hr
  obtain ⟨-, hrpd⟩ := Finset.mem_inter.1 hrKP
  refine Finset.mem_inter.2 ⟨?_, ?_⟩
  · exact Finset.mem_union.2 (Or.inl hrpd)
  · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hrI
    exact Finset.mem_image.2
      ⟨p, Finset.mem_union.2 (Or.inl hp), rfl⟩

end JSP000728
