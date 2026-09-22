/-
The **Lev–Smeliansky two-set route** to `Freiman3k4Residual`
(`JSPProblem/Freiman3k4.lean`).

For finite `X, Y ⊆ ℤ` with `min X = min Y = 0`, `max X = lX ≥ lY = max Y`,
writing `δ = 1` if `lX = lY` and `δ = 0` otherwise, and with the gcd of the
differences of `X ∪ Y` equal to `1`, the Lev–Smeliansky theorem
(Acta Arith. 70, 1995; Freiman, Astérisque 209, Thm. 3) states

  `|X + Y| ≥ min (lX + |Y|, |X| + 2|Y| − 2 − δ)`.

Applied to `X = A` and `Y = l − A` (both contained in `[0, l]`, both
containing `0` and `l`, both of diameter `l`, so `δ = 1`), the hypothesis
`2|A| − 2 ≤ l` of `Freiman3k4Residual` gives `|A + (l − A)| ≥ 3|A| − 3`;
since `A + (l − A) = l + (A − A)`, this is exactly the conclusion
`3|A| − 3 ≤ |A − A|` (the `minFac` hypothesis is unused).

The remove-max argument for two sets is *one-sided*: writing `X' = X ∖ {lX}`
one has `X + Y = (X' + Y) ∪ (lX + Y)`, hence

  `|X + Y| = |X' + Y| + r`,   `r = #{y ∈ Y : lX + y ∉ X' + Y}`.

Always `r ≥ 1` (`lX + lY` exceeds every element of `X' + Y`).  If the
differences of `X' ∪ Y` share a common divisor `d ≥ 2`, coprimality of
`X ∪ Y` forces `d ∤ lX`, every `lX + y` is new, `r = |Y|` and
`|X + Y| ≥ |X| + 2|Y| − 2` — the easy case.

Otherwise the induction hypothesis applies to the pair `(X', Y)` (if
`l' = max X' ≥ lY`) or to the swapped pair `(Y, X')` (if `l' < lY`), and
closes the estimate except in the genuinely tight configurations, which are
isolated as the hypothesis `LSResidual` (the precise inverse-theoretic
content of the elementary remove-max proof, matching the `RemoveMaxResidual`
pattern of `JSPProblem/FreimanResidualB.lean`).

* `lsNewX` — `r = #{y ∈ Y : lX + y ∉ X' + Y}`.
* `card_image₂_add_eq_erase_add_lsNewX` — the remove-max identity.
* `one_le_lsNewX` — `r ≥ 1`.
* `card_image₂_add_ge_of_dvd_erase` — the `gcd X' ∪ Y ≥ 2` easy case.
* `LSBound` — the Lev–Smeliansky bound, as a hypothesis.
* `LSResidual` — the residual tight configurations.
* `ls_min_bound`, `ls_of_lsResidual` — the induction `LSResidual → LSBound`.
* `freiman3k4Residual_of_ls` — `LSBound → Freiman3k4Residual`.
* `freiman3k4Residual_of_lsResidual` — the full reduction.
-/

import JSPProblem.FreimanResidualB

namespace JSP000728

open Finset
open scoped Pointwise

/-! ### The two-set remove-max identity -/

/-- The number of genuinely new sums contributed by `max X = lX`:
`lsNewX X lX Y = #{y ∈ Y : lX + y ∉ (X ∖ {lX}) + Y}`. -/
def lsNewX (X : Finset ℤ) (lX : ℤ) (Y : Finset ℤ) : ℕ :=
  (Y.filter (fun y => lX + y ∉ (X.erase lX).image₂ (· + ·) Y)).card

/-- Sumsets commute. -/
theorem image₂_add_comm (X Y : Finset ℤ) :
    X.image₂ (· + ·) Y = Y.image₂ (· + ·) X := by
  ext z
  simp only [Finset.mem_image₂]
  constructor <;> rintro ⟨a, ha, b, hb, rfl⟩ <;> exact ⟨b, hb, a, ha, by ring⟩

/-- **One-sided remove-max identity.**  For `lX ∈ X` and `X' = X ∖ {lX}`,

  `|X + Y| = |X' + Y| + r`,   `r = lsNewX X lX Y`.

Indeed `X + Y = (X' + Y) ∪ (lX + Y)`, and `(lX + Y) ∖ (X' + Y)` is the image
of the `lsNewX` filter under the injective map `lX + ·`. -/
theorem card_image₂_add_eq_erase_add_lsNewX {X Y : Finset ℤ} {lX : ℤ}
    (hlX : lX ∈ X) :
    (X.image₂ (· + ·) Y).card =
      ((X.erase lX).image₂ (· + ·) Y).card + lsNewX X lX Y := by
  classical
  have hdecomp : X.image₂ (· + ·) Y =
      (X.erase lX).image₂ (· + ·) Y ∪ Y.image (lX + ·) := by
    ext z
    simp only [Finset.mem_image₂, Finset.mem_union, Finset.mem_image]
    constructor
    · rintro ⟨x, hx, y, hy, rfl⟩
      by_cases hxl : x = lX
      · exact Or.inr ⟨y, hy, by rw [hxl]⟩
      · exact Or.inl ⟨x, Finset.mem_erase.2 ⟨hxl, hx⟩, y, hy, rfl⟩
    · intro h
      rcases h with ⟨x, hx, y, hy, rfl⟩ | ⟨y, hy, rfl⟩
      · exact ⟨x, (Finset.mem_erase.1 hx).2, y, hy, rfl⟩
      · exact ⟨lX, hlX, y, hy, rfl⟩
  have hsd : Y.image (lX + ·) \ (X.erase lX).image₂ (· + ·) Y =
      (Y.filter (fun y => lX + y ∉ (X.erase lX).image₂ (· + ·) Y)).image
        (lX + ·) := by
    ext z
    simp only [Finset.mem_sdiff, Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨⟨y, hy, rfl⟩, hz⟩
      exact ⟨y, ⟨hy, hz⟩, rfl⟩
    · rintro ⟨y, ⟨hy, hz⟩, rfl⟩
      exact ⟨⟨y, hy, rfl⟩, hz⟩
  have hinj : Function.Injective (fun y : ℤ => lX + y) := fun a b h => by
    simpa using h
  have hcard : (Y.image (lX + ·) \ (X.erase lX).image₂ (· + ·) Y).card =
      lsNewX X lX Y := by
    rw [hsd, Finset.card_image_of_injective _ hinj]
  rw [hdecomp, ← Finset.union_sdiff_self_eq_union,
    Finset.card_union_of_disjoint Finset.disjoint_sdiff, hcard]

/-- `lX + lY` is always new (it exceeds `max (X' + Y) ≤ l' + lY < lX + lY`),
so `r ≥ 1`. -/
theorem one_le_lsNewX {X Y : Finset ℤ} {lX lY : ℤ}
    (hlX : lX ∈ X) (hmaxX : ∀ x ∈ X, x ≤ lX)
    (hlY : lY ∈ Y) (hmaxY : ∀ y ∈ Y, y ≤ lY) :
    1 ≤ lsNewX X lX Y := by
  apply Finset.card_pos.2
  refine ⟨lY, Finset.mem_filter.2 ⟨hlY, ?_⟩⟩
  intro hmem
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.mem_image₂.1 hmem
  have hxlt : x < lX :=
    lt_of_le_of_ne (hmaxX x (Finset.mem_erase.1 hx).2)
      (Finset.mem_erase.1 hx).1
  have hyle : y ≤ lY := hmaxY y hy
  omega

/-! ### The easy case: `X' ∪ Y` has a common difference divisor -/

/-- If some `d ≥ 2` divides every difference of `X' ∪ Y` (where
`X' = X ∖ {lX}`), coprimality of `X ∪ Y` forces `d ∤ lX`; then every
`lX + y` (`y ∈ Y`) lies outside `X' + Y ⊆ dℤ`, so `r = |Y|` and

  `|X + Y| ≥ (|X'| + |Y| − 1) + |Y| = |X| + 2|Y| − 2`. -/
theorem card_image₂_add_ge_of_dvd_erase {X Y : Finset ℤ} {lX d : ℤ}
    (h0X' : (0 : ℤ) ∈ X.erase lX) (hlX : lX ∈ X) (h0Y : 0 ∈ Y)
    (hgcd : ∀ e : ℤ, 2 ≤ e → ∃ u ∈ X ∪ Y, ∃ v ∈ X ∪ Y, ¬ e ∣ u - v)
    (hd : 2 ≤ d)
    (hdvd : ∀ u ∈ X.erase lX ∪ Y, ∀ v ∈ X.erase lX ∪ Y, d ∣ u - v) :
    (X.card : ℤ) + 2 * (Y.card : ℤ) - 2 ≤
      ((X.image₂ (· + ·) Y).card : ℤ) := by
  classical
  have h0' : (0 : ℤ) ∈ X.erase lX ∪ Y := Finset.mem_union.2 (Or.inl h0X')
  have hdvd0 : ∀ z ∈ X.erase lX ∪ Y, d ∣ z := by
    intro z hz
    have h := hdvd z hz 0 h0'
    rwa [sub_zero] at h
  have hdlX : ¬ d ∣ lX := by
    intro h'
    obtain ⟨u, hu, v, hv, huv⟩ := hgcd d hd
    apply huv
    have huD : d ∣ u := by
      rcases Finset.mem_union.1 hu with huX | huY
      · rcases eq_or_ne u lX with rfl | hne
        · exact h'
        · exact hdvd0 u
            (Finset.mem_union.2 (Or.inl (Finset.mem_erase.2 ⟨hne, huX⟩)))
      · exact hdvd0 u (Finset.mem_union.2 (Or.inr huY))
    have hvD : d ∣ v := by
      rcases Finset.mem_union.1 hv with hvX | hvY
      · rcases eq_or_ne v lX with rfl | hne
        · exact h'
        · exact hdvd0 v
            (Finset.mem_union.2 (Or.inl (Finset.mem_erase.2 ⟨hne, hvX⟩)))
      · exact hdvd0 v (Finset.mem_union.2 (Or.inr hvY))
    exact dvd_sub huD hvD
  have hfilter : Y.filter (fun y => lX + y ∉ (X.erase lX).image₂ (· + ·) Y) =
      Y := by
    apply Finset.filter_true_of_mem
    intro y hy hmem
    obtain ⟨x', hx', y', hy', hxy⟩ := Finset.mem_image₂.1 hmem
    have hx0 : d ∣ x' := hdvd0 x' (Finset.mem_union.2 (Or.inl hx'))
    have hy0 : d ∣ y' := hdvd0 y' (Finset.mem_union.2 (Or.inr hy'))
    have hy0' : d ∣ y := hdvd0 y (Finset.mem_union.2 (Or.inr hy))
    apply hdlX
    have e : lX = (x' + y') - y := by omega
    rw [e]
    exact dvd_sub (dvd_add hx0 hy0) hy0'
  have hident := card_image₂_add_eq_erase_add_lsNewX hlX
  have hr : lsNewX X lX Y = Y.card := by
    unfold lsNewX; rw [hfilter]
  have hneX' : (X.erase lX).Nonempty := ⟨0, h0X'⟩
  have hneY : Y.Nonempty := ⟨0, h0Y⟩
  have hcd := cauchy_davenport_add_of_linearOrder_isCancelAdd hneX' hneY
  have h2 : X.erase lX + Y = (X.erase lX).image₂ (· + ·) Y := rfl
  rw [h2] at hcd
  have hm1 : 1 ≤ X.card := Finset.card_pos.2 ⟨lX, hlX⟩
  have hn1 : 1 ≤ Y.card := Finset.card_pos.2 hneY
  have hpos : 1 ≤ (X.erase lX).card + Y.card := by
    have h : 0 < (X.erase lX).card := Finset.card_pos.2 hneX'
    omega
  have hcdz : ((X.erase lX).card : ℤ) + (Y.card : ℤ) - 1 ≤
      ((X.erase lX).image₂ (· + ·) Y).card := by
    have hcast : (((X.erase lX).card + Y.card - 1 : ℕ) : ℤ) =
        ((X.erase lX).card : ℤ) + (Y.card : ℤ) - 1 := by
      rw [Nat.cast_sub hpos, Nat.cast_add]
    rw [← hcast]
    exact_mod_cast hcd
  have hcardX'z : ((X.erase lX).card : ℤ) = (X.card : ℤ) - 1 := by
    have h := Finset.card_erase_of_mem hlX
    omega
  have hident' : ((X.image₂ (· + ·) Y).card : ℤ) =
      ((X.erase lX).image₂ (· + ·) Y).card + (lsNewX X lX Y : ℤ) := by
    exact_mod_cast hident
  rw [hr] at hident'
  omega

/-! ### The Lev–Smeliansky bound and its residual configurations -/

/-- The **Lev–Smeliansky bound**, as a hypothesis: for `X, Y ⊆ ℤ` with
`min X = min Y = 0`, `max X = lX ≥ lY = max Y` and gcd of the differences of
`X ∪ Y` equal to `1`, writing `δ = [lX = lY]` one has

  `|X + Y| ≥ min (lX + |Y|, |X| + 2|Y| − 2 − δ)`. -/
def LSBound : Prop :=
  ∀ (X Y : Finset ℤ) (lX lY : ℤ),
    0 ∈ X → lX ∈ X → (∀ x ∈ X, 0 ≤ x ∧ x ≤ lX) →
    0 ∈ Y → lY ∈ Y → (∀ y ∈ Y, 0 ≤ y ∧ y ≤ lY) →
    lY ≤ lX →
    (∀ d : ℤ, 2 ≤ d → ∃ u ∈ X ∪ Y, ∃ v ∈ X ∪ Y, ¬ d ∣ u - v) →
    min (lX + (Y.card : ℤ))
        ((X.card : ℤ) + 2 * (Y.card : ℤ) - 2 -
          (if lX = lY then (1 : ℤ) else 0))
      ≤ ((X.image₂ (· + ·) Y).card : ℤ)

/-- The **residual tight configurations** of the remove-max proof of the
Lev–Smeliansky bound.

For `X, Y ⊆ ℤ` satisfying the `LSBound` hypotheses, let `X' = X ∖ {lX}`,
`l' = max X'` (witnessed by `l' ∈ X'` and `∀ x' ∈ X', x' ≤ l'`) and
`r = lsNewX X lX Y`.  The remove-max identity gives
`|X + Y| = |X' + Y| + r`; the induction closes this estimate unless
`X' ∪ Y` is still coprime and the induction bound applied to the smaller
pair does not reach the target, i.e. either

* `l' ≥ lY` (`X'` remains the wider set) but
  `min (l' + |Y|, |X'| + 2|Y| − 2 − δ') + r` is below the target, or
* `l' < lY` (the roles swap) but
  `min (lY + |X'|, |Y| + 2|X'| − 2) + r` is below the target.

`LSResidual` asserts that the bound nevertheless holds in those
configurations; it is the precise inverse-theoretic content of the
elementary remove-max proof of the Lev–Smeliansky bound (the two-set
analogue of `RemoveMaxResidual` in `JSPProblem/FreimanResidualB.lean`). -/
def LSResidual : Prop :=
  ∀ (X Y : Finset ℤ) (lX lY l' : ℤ),
    0 ∈ X → lX ∈ X → (∀ x ∈ X, 0 ≤ x ∧ x ≤ lX) →
    0 ∈ Y → lY ∈ Y → (∀ y ∈ Y, 0 ≤ y ∧ y ≤ lY) →
    lY ≤ lX →
    (∀ d : ℤ, 2 ≤ d → ∃ u ∈ X ∪ Y, ∃ v ∈ X ∪ Y, ¬ d ∣ u - v) →
    l' ∈ X.erase lX → (∀ x' ∈ X.erase lX, x' ≤ l') →
    (∀ d : ℤ, 2 ≤ d → ∃ u ∈ X.erase lX ∪ Y, ∃ v ∈ X.erase lX ∪ Y,
      ¬ d ∣ u - v) →
    ((lY ≤ l' ∧
        min (l' + (Y.card : ℤ))
            (((X.erase lX).card : ℤ) + 2 * (Y.card : ℤ) - 2 -
              (if l' = lY then (1 : ℤ) else 0)) +
          (lsNewX X lX Y : ℤ) <
          min (lX + (Y.card : ℤ))
            ((X.card : ℤ) + 2 * (Y.card : ℤ) - 2 -
              (if lX = lY then (1 : ℤ) else 0))) ∨
     (l' < lY ∧
        min (lY + ((X.erase lX).card : ℤ))
            ((Y.card : ℤ) + 2 * ((X.erase lX).card : ℤ) - 2) +
          (lsNewX X lX Y : ℤ) <
          min (lX + (Y.card : ℤ))
            ((X.card : ℤ) + 2 * (Y.card : ℤ) - 2 -
              (if lX = lY then (1 : ℤ) else 0)))) →
    min (lX + (Y.card : ℤ))
        ((X.card : ℤ) + 2 * (Y.card : ℤ) - 2 -
          (if lX = lY then (1 : ℤ) else 0))
      ≤ ((X.image₂ (· + ·) Y).card : ℤ)

/-- **The two-set remove-max induction.**  Under the residual hypothesis
`LSResidual`, every pair `(X, Y)` with `min X = min Y = 0`, `max X = lX`,
`max Y = lY ≤ lX` and coprime differences satisfies the Lev–Smeliansky
bound `|X + Y| ≥ min (lX + |Y|, |X| + 2|Y| − 2 − δ)`.

The proof is by strong induction on `|X| + |Y|`.  With `X' = X ∖ {lX}`,
`l' = max X'` and `r = lsNewX X lX Y`:

* if `X' ∪ Y` has a common difference divisor `d ≥ 2`, the easy case
  `card_image₂_add_ge_of_dvd_erase` applies (`r = |Y|`);
* if `X' ∪ Y` is coprime and `l' ≥ lY`, the induction hypothesis applied to
  `(X', Y)` gives `|X' + Y| ≥ min (l' + |Y|, |X'| + 2|Y| − 2 − δ')`; the
  step closes when this plus `r` reaches the target, and its failure is the
  first disjunct of `LSResidual`;
* if `X' ∪ Y` is coprime and `l' < lY`, the induction hypothesis applied to
  the swapped pair `(Y, X')` gives
  `|X' + Y| ≥ min (lY + |X'|, |Y| + 2|X'| − 2)`; its failure to reach the
  target is the second disjunct of `LSResidual`. -/
theorem ls_min_bound (hres : LSResidual) :
    ∀ s : ℕ, ∀ X Y : Finset ℤ, ∀ lX lY : ℤ, X.card + Y.card = s →
      0 ∈ X → lX ∈ X → (∀ x ∈ X, 0 ≤ x ∧ x ≤ lX) →
      0 ∈ Y → lY ∈ Y → (∀ y ∈ Y, 0 ≤ y ∧ y ≤ lY) →
      lY ≤ lX →
      (∀ d : ℤ, 2 ≤ d → ∃ u ∈ X ∪ Y, ∃ v ∈ X ∪ Y, ¬ d ∣ u - v) →
      min (lX + (Y.card : ℤ))
          ((X.card : ℤ) + 2 * (Y.card : ℤ) - 2 -
            (if lX = lY then (1 : ℤ) else 0))
        ≤ ((X.image₂ (· + ·) Y).card : ℤ) := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro X Y lX lY hs h0X hlX hX h0Y hlY hY hlYX hgcd
    classical
    have hminX : ∀ x ∈ X, 0 ≤ x := fun x hx => (hX x hx).1
    have hmaxX : ∀ x ∈ X, x ≤ lX := fun x hx => (hX x hx).2
    have hminY : ∀ y ∈ Y, 0 ≤ y := fun y hy => (hY y hy).1
    have hmaxY : ∀ y ∈ Y, y ≤ lY := fun y hy => (hY y hy).2
    have hmpos : 0 < X.card := Finset.card_pos.2 ⟨0, h0X⟩
    have hnpos : 0 < Y.card := Finset.card_pos.2 ⟨0, h0Y⟩
    by_cases hY1 : Y.card ≤ 1
    · -- `Y = {0}`: the sumset is `X` itself.
      have hlY0 : lY = 0 := by
        by_contra hne
        have hsub : ({0, lY} : Finset ℤ) ⊆ Y := by
          intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl
          · exact h0Y
          · exact hlY
        have h := Finset.card_le_card hsub
        rw [Finset.card_pair hne] at h
        omega
      subst hlY0
      have hYeq : Y = {0} :=
        Finset.eq_of_subset_of_card_le
          (fun y hy => by
            have h1 := hminY y hy
            have h2 := hmaxY y hy
            simp only [Finset.mem_singleton]
            omega)
          (by rw [Finset.card_singleton]; exact hnpos)
      have hsum0 : X.image₂ (· + ·) ({0} : Finset ℤ) = X := by
        ext z
        simp only [Finset.mem_image₂, Finset.mem_singleton]
        constructor
        · rintro ⟨x, hx, y, hy, rfl⟩
          rw [hy]; simpa using hx
        · intro hx
          exact ⟨x, hx, 0, rfl, by ring⟩
      rw [hYeq, Finset.card_singleton, Nat.cast_one, hsum0]
      apply min_le_iff.2
      right
      split_ifs <;> omega
    · have hn2 : 2 ≤ Y.card := by omega
      have hlY0 : 0 < lY := by
        have h0lY : (0 : ℤ) ≤ lY := hminY lY hlY
        rcases eq_or_ne lY 0 with h | h
        · subst h
          exfalso
          have hsub : Y ⊆ ({0} : Finset ℤ) := by
            intro y hy
            have h1 := hminY y hy
            have h2 := hmaxY y hy
            simp only [Finset.mem_singleton]
            omega
          have h := Finset.card_le_card hsub
          rw [Finset.card_singleton] at h
          omega
        · omega
      have hlX0 : 0 < lX := lt_of_lt_of_le hlY0 hlYX
      have h0X' : (0 : ℤ) ∈ X.erase lX :=
        Finset.mem_erase.2 ⟨ne_of_lt hlX0, h0X⟩
      have hneX' : (X.erase lX).Nonempty := ⟨0, h0X'⟩
      have hm2 : 2 ≤ X.card := by
        have hsub : ({0, lX} : Finset ℤ) ⊆ X := by
          intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl
          · exact h0X
          · exact hlX
        have h := Finset.card_le_card hsub
        rwa [Finset.card_pair (ne_of_lt hlX0)] at h
      set l' := (X.erase lX).max' hneX' with hl'def
      have hl'mem : l' ∈ X.erase lX := (X.erase lX).max'_mem hneX'
      have hl'max : ∀ x' ∈ X.erase lX, x' ≤ l' :=
        fun x' hx' => (X.erase lX).le_max' x' hx'
      have hcardX'z : ((X.erase lX).card : ℤ) = (X.card : ℤ) - 1 := by
        have h := Finset.card_erase_of_mem hlX
        omega
      have hident : ((X.image₂ (· + ·) Y).card : ℤ) =
          ((X.erase lX).image₂ (· + ·) Y).card + (lsNewX X lX Y : ℤ) := by
        exact_mod_cast card_image₂_add_eq_erase_add_lsNewX hlX
      have hr1 : (1 : ℤ) ≤ (lsNewX X lX Y : ℤ) := by
        exact_mod_cast one_le_lsNewX hlX hmaxX hlY hmaxY
      by_cases hgcd' : ∃ d : ℤ, 2 ≤ d ∧
          ∀ u ∈ X.erase lX ∪ Y, ∀ v ∈ X.erase lX ∪ Y, d ∣ u - v
      · -- **Easy case**: `X' ∪ Y ⊆ dℤ` forces `r = |Y|`.
        obtain ⟨d, hd, hdvd⟩ := hgcd'
        have hb := card_image₂_add_ge_of_dvd_erase h0X' hlX h0Y hgcd hd hdvd
        apply (min_le_iff.2 (Or.inr ?_)).trans hb
        split_ifs <;> omega
      · push Not at hgcd'
        by_cases hl'ge : lY ≤ l'
        · -- `X'` is still the wider set: IH on `(X', Y)`.
          have hslt : (X.erase lX).card + Y.card < s := by
            have h := Finset.card_erase_of_mem hlX
            omega
          have hbX' : ∀ x' ∈ X.erase lX, 0 ≤ x' ∧ x' ≤ l' :=
            fun x' hx' =>
              ⟨hminX x' (Finset.mem_erase.1 hx').2, hl'max x' hx'⟩
          have hpair := ih ((X.erase lX).card + Y.card) hslt (X.erase lX) Y
            l' lY rfl h0X' hl'mem hbX' h0Y hlY hY hl'ge hgcd'
          by_cases htrig :
              min (l' + (Y.card : ℤ))
                  (((X.erase lX).card : ℤ) + 2 * (Y.card : ℤ) - 2 -
                    (if l' = lY then (1 : ℤ) else 0)) +
                (lsNewX X lX Y : ℤ) <
                min (lX + (Y.card : ℤ))
                  ((X.card : ℤ) + 2 * (Y.card : ℤ) - 2 -
                    (if lX = lY then (1 : ℤ) else 0))
          · exact hres X Y lX lY l' h0X hlX hX h0Y hlY hY hlYX hgcd
              hl'mem hl'max hgcd' (Or.inl ⟨hl'ge, htrig⟩)
          · push Not at htrig
            calc min (lX + (Y.card : ℤ))
                  ((X.card : ℤ) + 2 * (Y.card : ℤ) - 2 -
                    (if lX = lY then (1 : ℤ) else 0))
                ≤ min (l' + (Y.card : ℤ))
                    (((X.erase lX).card : ℤ) + 2 * (Y.card : ℤ) - 2 -
                      (if l' = lY then (1 : ℤ) else 0)) +
                  (lsNewX X lX Y : ℤ) := htrig
              _ ≤ ((X.erase lX).image₂ (· + ·) Y).card +
                  (lsNewX X lX Y : ℤ) := add_le_add_right hpair _
              _ = ((X.image₂ (· + ·) Y).card : ℤ) := hident.symm
        · -- The roles swap: IH on `(Y, X')`.
          push Not at hl'ge
          have hslt : Y.card + (X.erase lX).card < s := by
            have h := Finset.card_erase_of_mem hlX
            omega
          have hbX' : ∀ x' ∈ X.erase lX, 0 ≤ x' ∧ x' ≤ l' :=
            fun x' hx' =>
              ⟨hminX x' (Finset.mem_erase.1 hx').2, hl'max x' hx'⟩
          have hgcd'' : ∀ d : ℤ, 2 ≤ d →
              ∃ u ∈ Y ∪ X.erase lX, ∃ v ∈ Y ∪ X.erase lX, ¬ d ∣ u - v := by
            intro d hd
            obtain ⟨u, hu, v, hv, h⟩ := hgcd' d hd
            exact ⟨u, Finset.mem_union.2 (Finset.mem_union.1 hu).symm, v,
              Finset.mem_union.2 (Finset.mem_union.1 hv).symm, h⟩
          have hpair := ih (Y.card + (X.erase lX).card) hslt Y (X.erase lX)
            lY l' rfl h0Y hlY hY h0X' hl'mem hbX' (le_of_lt hl'ge) hgcd''
          rw [if_neg (ne_of_gt hl'ge), sub_zero] at hpair
          have hpair' : min (lY + ((X.erase lX).card : ℤ))
              ((Y.card : ℤ) + 2 * ((X.erase lX).card : ℤ) - 2) ≤
              ((X.erase lX).image₂ (· + ·) Y).card := by
            rw [image₂_add_comm]
            exact hpair
          by_cases htrig : min (lY + ((X.erase lX).card : ℤ))
              ((Y.card : ℤ) + 2 * ((X.erase lX).card : ℤ) - 2) +
              (lsNewX X lX Y : ℤ) <
              min (lX + (Y.card : ℤ))
                ((X.card : ℤ) + 2 * (Y.card : ℤ) - 2 -
                  (if lX = lY then (1 : ℤ) else 0))
          · exact hres X Y lX lY l' h0X hlX hX h0Y hlY hY hlYX hgcd
              hl'mem hl'max hgcd' (Or.inr ⟨hl'ge, htrig⟩)
          · push Not at htrig
            calc min (lX + (Y.card : ℤ))
                  ((X.card : ℤ) + 2 * (Y.card : ℤ) - 2 -
                    (if lX = lY then (1 : ℤ) else 0))
                ≤ min (lY + ((X.erase lX).card : ℤ))
                    ((Y.card : ℤ) + 2 * ((X.erase lX).card : ℤ) - 2) +
                  (lsNewX X lX Y : ℤ) := htrig
              _ ≤ ((X.erase lX).image₂ (· + ·) Y).card +
                  (lsNewX X lX Y : ℤ) := add_le_add_right hpair' _
              _ = ((X.image₂ (· + ·) Y).card : ℤ) := hident.symm

/-- **The remove-max reduction of the Lev–Smeliansky bound.**
`LSBound` follows from the residual inverse analysis `LSResidual`. -/
theorem ls_of_lsResidual (hres : LSResidual) : LSBound := by
  intro X Y lX lY h0X hlX hX h0Y hlY hY hlYX hgcd
  exact ls_min_bound hres (X.card + Y.card) X Y lX lY rfl
    h0X hlX hX h0Y hlY hY hlYX hgcd

/-- **Lev–Smeliansky implies the Freiman residual case.**  Applied to
`X = A`, `Y = l − A`: both contain `0` and `l`, both lie in `[0, l]`, both
have cardinality `|A|`, the union's differences contain those of `A` (hence
the coprimality hypothesis), and `A + (l − A) = l + (A − A)`.  With
`l ≥ 2|A| − 2` the bound `min (l + |A|, 3|A| − 3) = 3|A| − 3` results. -/
theorem freiman3k4Residual_of_ls (h : LSBound) : Freiman3k4Residual := by
  intro A l h0 hl hmem hgcd hlarge _hmf
  classical
  have hmin : ∀ x ∈ A, 0 ≤ x := fun x hx => (hmem x hx).1
  have hmax : ∀ x ∈ A, x ≤ l := fun x hx => (hmem x hx).2
  set B := A.image (l - ·) with hBdef
  have hBcard : B.card = A.card :=
    Finset.card_image_of_injective _ (fun a b h => by omega)
  have h0B : (0 : ℤ) ∈ B := Finset.mem_image.2 ⟨l, hl, by ring⟩
  have hlB : l ∈ B := Finset.mem_image.2 ⟨0, h0, by ring⟩
  have hBB : ∀ b ∈ B, 0 ≤ b ∧ b ≤ l := by
    intro b hb
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hb
    refine ⟨?_, ?_⟩
    · have h2 := hmax a ha; omega
    · have h1 := hmin a ha; omega
  have hgcdB : ∀ d : ℤ, 2 ≤ d → ∃ u ∈ A ∪ B, ∃ v ∈ A ∪ B, ¬ d ∣ u - v := by
    intro d hd
    obtain ⟨x, hx, y, hy, hxy⟩ := hgcd d hd
    exact ⟨x, Finset.mem_union.2 (Or.inl hx), y,
      Finset.mem_union.2 (Or.inl hy), hxy⟩
  have hb := h A B l l h0 hl hmem h0B hlB hBB (le_refl l) hgcdB
  rw [if_pos rfl, hBcard] at hb
  have hsum : A.image₂ (· + ·) B = (A.image₂ (· - ·) A).image (l + ·) := by
    ext x
    simp only [hBdef, Finset.mem_image₂, Finset.mem_image]
    constructor
    · rintro ⟨a, ha, b, ⟨a', ha', rfl⟩, rfl⟩
      exact ⟨a - a', ⟨a, ha, a', ha', rfl⟩, by ring⟩
    · rintro ⟨x', ⟨a, ha, a', ha', rfl⟩, rfl⟩
      exact ⟨a, ha, l - a', ⟨a', ha', rfl⟩, by ring⟩
  have hcard : (A.image₂ (· + ·) B).card = (A.image₂ (· - ·) A).card := by
    rw [hsum]
    exact Finset.card_image_of_injective _ (add_right_injective l)
  rw [hcard] at hb
  have hmineq : min (l + (A.card : ℤ))
      ((A.card : ℤ) + 2 * (A.card : ℤ) - 2 - 1) =
      (A.card : ℤ) + 2 * (A.card : ℤ) - 3 := by
    apply min_eq_right
    omega
  rw [hmineq] at hb
  omega

/-- **The full two-set reduction of the residual case.**
`Freiman3k4Residual` follows from the residual inverse analysis
`LSResidual` of the remove-max proof of the Lev–Smeliansky bound. -/
theorem freiman3k4Residual_of_lsResidual (hres : LSResidual) :
    Freiman3k4Residual :=
  freiman3k4Residual_of_ls (ls_of_lsResidual hres)

end JSP000728
