import JSPProblem.Supersaturation
import JSPProblem.DFSTBridge
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# JSP-000728 — Quadratic cross-supersaturation for band sets

For `C ⊆ [1, n]` write

* `midBand n C = C ∩ [2n/5, n/2]`  (the *middle band*),
* `topBand n C = C ∩ [4n/5, n]`    (the *top band*).

Sums of two middle-band elements lie in `[4n/5, n]`, so every element of
`(midBand + midBand) ∩ topBand` is the sum-coordinate of many Schur triples
of `C`.  Two elementary interval computations drive the argument:

* a **fiber bound** (`two_mul_card_le_card_filter_sub_mem_add`): for
  `B ⊆ [lo, hi]` the representation set `{x ∈ B : z − x ∈ B}` has size at
  least `2|B| − |K_z|`, where `K_z` is the interval
  `[min lo (z − hi), max hi (z − lo)]` containing both `B` and `z − B`;
* a **window bound** (`card_image₂_add_card_le_inter_add`):
  `|A + B| + |T| ≤ |(A + B) ∩ T| + |W|` for a common window `W`.

Combined with the integer Cauchy–Davenport bound `2|B| − 1 ≤ |B + B|`
(`two_mul_card_sub_one_le_card_image₂_add`, proved in `DFSTBridge`), this
yields the quadratic tradeoff (`mid_top_product_le`, `mid_top_tradeoff`):
writing `m = |midBand|` and `t = |topBand|`,

    `max 0 (2m − n/5 − 5) · (2m + t − n/5 − 5) ≤ schurTripleCount C`,

so if `schurTripleCount C ≤ δ·n²` then either `2m ≤ n/5 + 5 + √δ·n` or
`t ≤ n/5 + 5 − 2m + √δ·n`: a sparse set cannot have both a dense middle
band and a dense top band.

A symmetric cross-band statement (`low_high_window_bound`,
`low_high_card_bound`, `low_high_tradeoff`) for
`lowBand = C ∩ [1, n/4]`, `highBand = C ∩ (n/2, 3n/4]` and
`topHalf = C ∩ (n/2, n]` uses the cross-sumset bound
`|A + B| ≥ |A| + |B| − 1` (`card_add_card_sub_one_le_card_image₂_add`)
together with the one-representation-per-sum count
(`card_image₂_inter_le_schurTripleCount`).
-/

namespace JSP000728

/-! ## Band definitions -/

/-- The middle band of `C ⊆ [1, n]`: `C ∩ [2n/5, n/2]` (integer division). -/
def midBand (n : ℕ) (C : Finset ℤ) : Finset ℤ :=
  C ∩ Finset.Icc (2 * (n : ℤ) / 5) ((n : ℤ) / 2)

/-- The top band of `C ⊆ [1, n]`: `C ∩ [4n/5, n]` (integer division). -/
def topBand (n : ℕ) (C : Finset ℤ) : Finset ℤ :=
  C ∩ Finset.Icc (4 * (n : ℤ) / 5) (n : ℤ)

/-- The low band of `C ⊆ [1, n]`: `C ∩ [1, n/4]`. -/
def lowBand (n : ℕ) (C : Finset ℤ) : Finset ℤ :=
  C ∩ Finset.Icc 1 ((n : ℤ) / 4)

/-- The high band of `C ⊆ [1, n]`: `C ∩ (n/2, 3n/4]`. -/
def highBand (n : ℕ) (C : Finset ℤ) : Finset ℤ :=
  C ∩ Finset.Icc ((n : ℤ) / 2 + 1) (3 * (n : ℤ) / 4)

/-- The upper half of `C ⊆ [1, n]`: `C ∩ (n/2, n]`; sums `low + high` land
here. -/
def topHalf (n : ℕ) (C : Finset ℤ) : Finset ℤ :=
  C ∩ Finset.Icc ((n : ℤ) / 2 + 1) (n : ℤ)

/-! ## Fiber bound: representations of `z` inside a band -/

/-- **Inclusion–exclusion on a band.**  For `B ⊆ [lo, hi]` and any `z`,
both `B` and its reflection `z − B` lie in the interval
`K = [min lo (z − hi), max hi (z − lo)]`, so

    `|{x ∈ B : z − x ∈ B}| ≥ |B ∩ (z − B)| ≥ 2|B| − |K|`.

This is the per-sum representation bound: each `z` has at least
`2|B| − |K_z|` ordered representations `z = x + y` with `x, y ∈ B`. -/
theorem two_mul_card_le_card_filter_sub_mem_add {B : Finset ℤ} {z lo hi : ℤ}
    (hB : B ⊆ Finset.Icc lo hi) :
    2 * (B.card : ℤ) ≤ ((B.filter fun x => z - x ∈ B).card : ℤ) +
      ((max hi (z - lo) + 1 - min lo (z - hi)).toNat : ℤ) := by
  classical
  have hBK : B ⊆ Finset.Icc (min lo (z - hi)) (max hi (z - lo)) := by
    intro x hx
    have hx' := Finset.mem_Icc.1 (hB hx)
    rw [Finset.mem_Icc]
    exact ⟨le_trans (min_le_left _ _) hx'.1, le_trans hx'.2 (le_max_left _ _)⟩
  have himg : B.image (fun x => z - x) ⊆
      Finset.Icc (min lo (z - hi)) (max hi (z - lo)) := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
    have hx' := Finset.mem_Icc.1 (hB hx)
    rw [Finset.mem_Icc]
    constructor
    · exact le_trans (min_le_right _ _) (by omega)
    · exact le_trans (by omega) (le_max_right _ _)
  have hcard : (B.image fun x => z - x).card = B.card :=
    Finset.card_image_of_injective _ (fun a b h => by omega)
  have hinter : B ∩ B.image (fun x => z - x) ⊆
      B.filter fun x => z - x ∈ B := by
    intro x hx
    obtain ⟨hxB, hxI⟩ := Finset.mem_inter.1 hx
    obtain ⟨a, ha, hax⟩ := Finset.mem_image.1 hxI
    rw [Finset.mem_filter]
    refine ⟨hxB, ?_⟩
    have hzx : z - x = a := by omega
    rw [hzx]; exact ha
  have h1 := Finset.card_le_card hinter
  have h2 := Finset.card_union_add_card_inter B (B.image fun x => z - x)
  have h3 := Finset.card_le_card (Finset.union_subset hBK himg)
  rw [Int.card_Icc] at h3
  have h4 : 2 * B.card ≤ (B.filter fun x => z - x ∈ B).card +
      (max hi (z - lo) + 1 - min lo (z - hi)).toNat := by omega
  exact_mod_cast h4

/-! ## Window bound: `|A + B| + |T| ≤ |(A + B) ∩ T| + |W|` -/

/-- If `A ⊆ [a₁, a₂]`, `B ⊆ [b₁, b₂]` and `T ⊆ [t₁, t₂]`, then `A + B` and
`T` both lie in the window `W = [min (a₁+b₁) t₁, max (a₂+b₂) t₂]`, hence
`|A + B| + |T| ≤ |(A + B) ∩ T| + |W|`. -/
theorem card_image₂_add_card_le_inter_add {A B T : Finset ℤ}
    {a₁ a₂ b₁ b₂ t₁ t₂ : ℤ}
    (hA : A ⊆ Finset.Icc a₁ a₂) (hB : B ⊆ Finset.Icc b₁ b₂)
    (hT : T ⊆ Finset.Icc t₁ t₂) :
    ((A.image₂ (· + ·) B).card : ℤ) + T.card ≤
      ((A.image₂ (· + ·) B ∩ T).card : ℤ) +
        ((max (a₂ + b₂) t₂ + 1 - min (a₁ + b₁) t₁).toNat : ℤ) := by
  classical
  have hX : A.image₂ (· + ·) B ⊆
      Finset.Icc (min (a₁ + b₁) t₁) (max (a₂ + b₂) t₂) := by
    intro z hz
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.mem_image₂.1 hz
    have hx' := Finset.mem_Icc.1 (hA hx)
    have hy' := Finset.mem_Icc.1 (hB hy)
    rw [Finset.mem_Icc]
    constructor
    · have h1 : min (a₁ + b₁) t₁ ≤ a₁ + b₁ := min_le_left _ _
      omega
    · have h2 : a₂ + b₂ ≤ max (a₂ + b₂) t₂ := le_max_left _ _
      omega
  have hTW : T ⊆ Finset.Icc (min (a₁ + b₁) t₁) (max (a₂ + b₂) t₂) := by
    intro z hz
    have hz' := Finset.mem_Icc.1 (hT hz)
    rw [Finset.mem_Icc]
    exact ⟨le_trans (min_le_right _ _) hz'.1, le_trans hz'.2 (le_max_right _ _)⟩
  have hU := Finset.card_le_card (Finset.union_subset hX hTW)
  rw [Int.card_Icc] at hU
  have h2 := Finset.card_union_add_card_inter (A.image₂ (· + ·) B) T
  have h3 : (A.image₂ (· + ·) B).card + T.card ≤
      ((A.image₂ (· + ·) B) ∩ T).card +
        (max (a₂ + b₂) t₂ + 1 - min (a₁ + b₁) t₁).toNat := by omega
  exact_mod_cast h3

/-! ## The master product bound -/

/-- **Quadratic supersaturation, band form.**  For bands
`B ⊆ [lo, hi]`, `T ⊆ [lo', hi']` inside `C`, if every `z ∈ T` has
container size `|K_z| ≤ w`, then

    `|(B + B) ∩ T| · (2|B| − w) ≤ schurTripleCount C`.

(Each `z ∈ (B + B) ∩ T` contributes `≥ 2|B| − w` triples `(x, z−x, z)`.)
The inequality holds unconditionally since the right factor is negative
when the bound is vacuous. -/
theorem card_image₂_inter_mul_le_schurTripleCount {C B T : Finset ℤ}
    {lo hi lo' hi' : ℤ} {w : ℤ}
    (hB : B ⊆ Finset.Icc lo hi) (hT : T ⊆ Finset.Icc lo' hi')
    (hBC : B ⊆ C) (hTC : T ⊆ C) (hw0 : 0 ≤ w)
    (hw : ∀ z ∈ T, max hi (z - lo) + 1 - min lo (z - hi) ≤ w) :
    (((B.image₂ (· + ·) B) ∩ T).card : ℤ) * (2 * B.card - w)
      ≤ schurTripleCount C := by
  classical
  have hsum : (schurTripleCount C : ℤ)
      = ∑ z ∈ C, ((C.filter fun x => z - x ∈ C).card : ℤ) := by
    rw [schurTripleCount_eq_sum_filter]
    exact Nat.cast_sum _ _
  have hsub : B.image₂ (· + ·) B ∩ T ⊆ C :=
    fun x hx => hTC (Finset.mem_inter.1 hx).2
  have h1 : ∑ z ∈ (B.image₂ (· + ·) B ∩ T),
        ((C.filter fun x => z - x ∈ C).card : ℤ) ≤ schurTripleCount C := by
    rw [hsum]
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro x _ _; positivity
  have h2 : ∀ z ∈ (B.image₂ (· + ·) B ∩ T), (2 * (B.card : ℤ) - w)
      ≤ (C.filter fun x => z - x ∈ C).card := by
    intro z hz
    obtain ⟨-, hzT⟩ := Finset.mem_inter.1 hz
    have hfiber := two_mul_card_le_card_filter_sub_mem_add (B := B) (z := z) hB
    have hK := hw z hzT
    have hmono : (B.filter fun x => z - x ∈ B).card
        ≤ (C.filter fun x => z - x ∈ C).card :=
      Finset.card_le_card (fun x hx => by
        rw [Finset.mem_filter] at hx ⊢
        exact ⟨hBC hx.1, hBC hx.2⟩)
    omega
  calc (((B.image₂ (· + ·) B) ∩ T).card : ℤ) * (2 * B.card - w)
      = ∑ z ∈ (B.image₂ (· + ·) B ∩ T), (2 * (B.card : ℤ) - w) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ z ∈ (B.image₂ (· + ·) B ∩ T),
          ((C.filter fun x => z - x ∈ C).card : ℤ) :=
        Finset.sum_le_sum h2
    _ ≤ schurTripleCount C := h1

/-! ## Specialisation to the middle and top bands -/

/-- **Middle/top product bound.**  Every `z ∈ (mid + mid) ∩ top`
contributes at least `2|mid| − n/5 − 5` Schur triples of `C`, so

    `|(mid + mid) ∩ top| · (2|mid| − n/5 − 5) ≤ schurTripleCount C`. -/
theorem mid_top_card_mul_le_schurTripleCount {n : ℕ} {C : Finset ℤ} :
    (((midBand n C).image₂ (· + ·) (midBand n C) ∩ topBand n C).card : ℤ) *
        (2 * (midBand n C).card - ((n : ℤ) / 5 + 5)) ≤ schurTripleCount C := by
  apply card_image₂_inter_mul_le_schurTripleCount
    (lo := 2 * (n : ℤ) / 5) (hi := (n : ℤ) / 2)
    (lo' := 4 * (n : ℤ) / 5) (hi' := (n : ℤ)) (w := (n : ℤ) / 5 + 5)
  · exact Finset.inter_subset_right
  · exact Finset.inter_subset_right
  · exact Finset.inter_subset_left
  · exact Finset.inter_subset_left
  · omega
  · intro z hz
    have hz' := Finset.mem_Icc.1 (Finset.mem_inter.1 hz).2
    omega

/-- **Middle/top window bound.**  `mid + mid ⊆ [4n/5 − 1, n]` and
`top ⊆ [4n/5, n]` share a window of size `≤ n/5 + 4`; together with
`|mid + mid| ≥ 2|mid| − 1` this gives

    `2|mid| + |top| ≤ |(mid + mid) ∩ top| + n/5 + 5`. -/
theorem mid_top_window_bound {n : ℕ} {C : Finset ℤ} :
    2 * ((midBand n C).card : ℤ) + (topBand n C).card ≤
      (((midBand n C).image₂ (· + ·) (midBand n C) ∩ topBand n C).card : ℤ) +
        ((n : ℤ) / 5 + 5) := by
  classical
  have h2 := card_image₂_add_card_le_inter_add
    (A := midBand n C) (B := midBand n C) (T := topBand n C)
    (a₁ := 2 * (n : ℤ) / 5) (a₂ := (n : ℤ) / 2)
    (b₁ := 2 * (n : ℤ) / 5) (b₂ := (n : ℤ) / 2)
    (t₁ := 4 * (n : ℤ) / 5) (t₂ := (n : ℤ))
    Finset.inter_subset_right Finset.inter_subset_right Finset.inter_subset_right
  have hW : ((max ((n : ℤ) / 2 + (n : ℤ) / 2) (n : ℤ) + 1
        - min (2 * (n : ℤ) / 5 + 2 * (n : ℤ) / 5) (4 * (n : ℤ) / 5)).toNat : ℤ)
      ≤ (n : ℤ) / 5 + 4 := by omega
  have hBB : 2 * ((midBand n C).card : ℤ)
      ≤ ((midBand n C).image₂ (· + ·) (midBand n C)).card + 1 := by
    rcases (midBand n C).eq_empty_or_nonempty with h | h
    · rw [h]; simp
    · exact two_mul_card_sub_one_le_card_image₂_add h
  omega

/-! ## The real-valued tradeoff -/

/-- **Product form of the band tradeoff.**  With `m = |midBand n C|`,
`t = |topBand n C|` and `w = n/5 + 5`,

    `max 0 (2m − w) · (2m + t − w) ≤ schurTripleCount C`. -/
theorem mid_top_product_le {n : ℕ} {C : Finset ℤ} {δ : ℝ}
    (hsparse : (schurTripleCount C : ℝ) ≤ δ * (n : ℝ) ^ 2) :
    max 0 (2 * ((midBand n C).card : ℝ) - (((n : ℤ) / 5 + 5 : ℤ) : ℝ)) *
        (2 * ((midBand n C).card : ℝ) + (topBand n C).card
          - (((n : ℤ) / 5 + 5 : ℤ) : ℝ))
      ≤ δ * (n : ℝ) ^ 2 := by
  have hA : (((midBand n C).image₂ (· + ·) (midBand n C) ∩ topBand n C).card : ℝ)
        * (2 * (midBand n C).card - (((n : ℤ) / 5 + 5 : ℤ) : ℝ))
      ≤ schurTripleCount C := by
    exact_mod_cast mid_top_card_mul_le_schurTripleCount
  have hB : 2 * ((midBand n C).card : ℝ) + (topBand n C).card
      ≤ (((midBand n C).image₂ (· + ·) (midBand n C) ∩ topBand n C).card : ℝ)
        + (((n : ℤ) / 5 + 5 : ℤ) : ℝ) := by
    exact_mod_cast mid_top_window_bound
  have hnn : (0 : ℝ) ≤ schurTripleCount C := by positivity
  rcases le_or_lt
      (2 * ((midBand n C).card : ℝ) - (((n : ℤ) / 5 + 5 : ℤ) : ℝ)) 0
      with hu | hu
  · rw [max_eq_left hu, zero_mul]
    exact le_trans hnn hsparse
  · rw [max_eq_right (le_of_lt hu)]
    have h1 : (2 * ((midBand n C).card : ℝ) - (((n : ℤ) / 5 + 5 : ℤ) : ℝ)
            + (topBand n C).card) *
          (2 * ((midBand n C).card : ℝ) - (((n : ℤ) / 5 + 5 : ℤ) : ℝ))
        ≤ (((midBand n C).image₂ (· + ·) (midBand n C) ∩ topBand n C).card : ℝ) *
          (2 * ((midBand n C).card : ℝ) - (((n : ℤ) / 5 + 5 : ℤ) : ℝ)) :=
      mul_le_mul_of_nonneg_right (by linarith) (le_of_lt hu)
    have h2 : (2 * ((midBand n C).card : ℝ) - (((n : ℤ) / 5 + 5 : ℤ) : ℝ)) *
          (2 * ((midBand n C).card : ℝ) + (topBand n C).card
            - (((n : ℤ) / 5 + 5 : ℤ) : ℝ))
        = (2 * ((midBand n C).card : ℝ) - (((n : ℤ) / 5 + 5 : ℤ) : ℝ)
            + (topBand n C).card) *
          (2 * ((midBand n C).card : ℝ) - (((n : ℤ) / 5 + 5 : ℤ) : ℝ)) := by
      ring
    rw [h2]
    exact le_trans h1 (le_trans hA hsparse)

/-- **The band tradeoff (disjunctive form).**  If `C` has at most `δ·n²`
Schur triples, then either the middle band is at most half-full

    `2·|mid| ≤ n/5 + 5 + √δ·n`,

or the top band is squeezed by the middle band:

    `|top| ≤ n/5 + 5 − 2·|mid| + √δ·n`. -/
theorem mid_top_tradeoff {n : ℕ} {C : Finset ℤ} (hC : C ⊆ interval n) {δ : ℝ}
    (hδ : 0 ≤ δ) (hsparse : (schurTripleCount C : ℝ) ≤ δ * (n : ℝ) ^ 2) :
    (2 * ((midBand n C).card : ℝ)) ≤ (n : ℝ) / 5 + 5 + Real.sqrt δ * n ∨
      ((topBand n C).card : ℝ)
        ≤ (n : ℝ) / 5 + 5 - 2 * (midBand n C).card + Real.sqrt δ * n := by
  have hw5 : (((n : ℤ) / 5 + 5 : ℤ) : ℝ) ≤ (n : ℝ) / 5 + 5 := by
    have h1 : (n : ℤ) / 5 * 5 ≤ (n : ℤ) := Int.ediv_mul_le _ (by norm_num)
    have h2 : (((n : ℤ) / 5 : ℤ) : ℝ) * 5 ≤ (n : ℝ) := by exact_mod_cast h1
    linarith
  have hA : (((midBand n C).image₂ (· + ·) (midBand n C) ∩ topBand n C).card : ℝ)
        * (2 * (midBand n C).card - (((n : ℤ) / 5 + 5 : ℤ) : ℝ))
      ≤ schurTripleCount C := by
    exact_mod_cast mid_top_card_mul_le_schurTripleCount
  have hB : 2 * ((midBand n C).card : ℝ) + (topBand n C).card
      ≤ (((midBand n C).image₂ (· + ·) (midBand n C) ∩ topBand n C).card : ℝ)
        + (((n : ℤ) / 5 + 5 : ℤ) : ℝ) := by
    exact_mod_cast mid_top_window_bound
  have hs : 0 ≤ Real.sqrt δ * (n : ℝ) :=
    mul_nonneg (Real.sqrt_nonneg _) (by positivity)
  have hsq : Real.sqrt δ * (n : ℝ) * (Real.sqrt δ * (n : ℝ))
      = δ * (n : ℝ) ^ 2 := by
    rw [mul_mul_mul_comm, Real.mul_self_sqrt hδ, pow_two]
  rcases le_or_lt
      (2 * ((midBand n C).card : ℝ) - (((n : ℤ) / 5 + 5 : ℤ) : ℝ))
      (Real.sqrt δ * (n : ℝ)) with hu | hu
  · left
    linarith
  · right
    by_contra hcon
    push_neg at hcon
    have hu0 : 0 < 2 * ((midBand n C).card : ℝ) - (((n : ℤ) / 5 + 5 : ℤ) : ℝ) :=
      lt_of_le_of_lt hs hu
    have hcut : Real.sqrt δ * (n : ℝ)
        < 2 * ((midBand n C).card : ℝ) - (((n : ℤ) / 5 + 5 : ℤ) : ℝ)
          + (topBand n C).card := by linarith
    have h1 : Real.sqrt δ * (n : ℝ) *
          (2 * ((midBand n C).card : ℝ) - (((n : ℤ) / 5 + 5 : ℤ) : ℝ))
        < (2 * ((midBand n C).card : ℝ) - (((n : ℤ) / 5 + 5 : ℤ) : ℝ)
            + (topBand n C).card) *
          (2 * ((midBand n C).card : ℝ) - (((n : ℤ) / 5 + 5 : ℤ) : ℝ)) :=
      mul_lt_mul_of_pos_right hcut hu0
    have h2 : Real.sqrt δ * (n : ℝ) * (Real.sqrt δ * (n : ℝ))
        ≤ Real.sqrt δ * (n : ℝ) *
          (2 * ((midBand n C).card : ℝ) - (((n : ℤ) / 5 + 5 : ℤ) : ℝ)) :=
      mul_le_mul_of_nonneg_left (le_of_lt hu) hs
    have h3 : (2 * ((midBand n C).card : ℝ) - (((n : ℤ) / 5 + 5 : ℤ) : ℝ)
            + (topBand n C).card) *
          (2 * ((midBand n C).card : ℝ) - (((n : ℤ) / 5 + 5 : ℤ) : ℝ))
        ≤ (((midBand n C).image₂ (· + ·) (midBand n C) ∩ topBand n C).card : ℝ) *
          (2 * ((midBand n C).card : ℝ) - (((n : ℤ) / 5 + 5 : ℤ) : ℝ)) :=
      mul_le_mul_of_nonneg_right (by linarith) (le_of_lt hu0)
    have h4 : Real.sqrt δ * (n : ℝ) * (Real.sqrt δ * (n : ℝ))
        < δ * (n : ℝ) ^ 2 :=
      lt_of_lt_of_le (lt_of_le_of_lt h2 (lt_of_lt_of_le h1 h3))
        (le_trans hA hsparse)
    rw [hsq] at h4
    exact lt_irrefl _ h4

/-! ## Cross-band version: low × high hits the upper half -/

/-- **Cross-sumset Cauchy–Davenport on `ℤ`.**  For nonempty `A B`,
`|A + B| ≥ |A| + |B| − 1`: the translates `min A + B` and `A + max B` lie
in `A + B` and overlap only in `min A + max B`. -/
theorem card_add_card_sub_one_le_card_image₂_add {A B : Finset ℤ}
    (hA : A.Nonempty) (hB : B.Nonempty) :
    (A.card : ℤ) + B.card - 1 ≤ (A.image₂ (· + ·) B).card := by
  classical
  set amin := A.min' hA with hamindef
  set bmax := B.max' hB with hbmaxdef
  have hamin : amin ∈ A := A.min'_mem hA
  have hbmax : bmax ∈ B := B.max'_mem hB
  have hsub : B.image (fun x => amin + x) ∪ A.image (fun x => x + bmax) ⊆
      A.image₂ (· + ·) B := by
    intro x hx
    rcases Finset.mem_union.1 hx with h | h
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 h
      exact Finset.mem_image₂.2 ⟨amin, hamin, y, hy, rfl⟩
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 h
      exact Finset.mem_image₂.2 ⟨y, hy, bmax, hbmax, rfl⟩
  have hcard1 : (B.image fun x => amin + x).card = B.card :=
    Finset.card_image_of_injective _ (add_right_injective amin)
  have hcard2 : (A.image fun x => x + bmax).card = A.card :=
    Finset.card_image_of_injective _ (add_left_injective bmax)
  have hinter : B.image (fun x => amin + x) ∩ A.image (fun x => x + bmax) ⊆
      {amin + bmax} := by
    intro z hz
    obtain ⟨h1, h2⟩ := Finset.mem_inter.1 hz
    obtain ⟨x, hx, hzx⟩ := Finset.mem_image.1 h1
    obtain ⟨y, hy, hzy⟩ := Finset.mem_image.1 h2
    have hxle := B.le_max' x hx
    have hyge := A.min'_le y hy
    have hz : z = amin + bmax := by omega
    exact Finset.mem_singleton.2 hz
  have hcardle := Finset.card_le_card hsub
  have hcap : (B.image (fun x => amin + x) ∩ A.image (fun x => x + bmax)).card
      ≤ 1 := (Finset.card_le_card hinter).trans (by simp)
  have hunion := Finset.card_union_add_card_inter
    (B.image fun x => amin + x) (A.image fun x => x + bmax)
  omega

/-- **One triple per represented sum.**  If `A, B, T ⊆ C`, every
`z ∈ (A + B) ∩ T` contributes at least one Schur triple `(x, z − x, z)`
of `C`, so `|(A + B) ∩ T| ≤ schurTripleCount C`. -/
theorem card_image₂_inter_le_schurTripleCount {A B T C : Finset ℤ}
    (hAC : A ⊆ C) (hBC : B ⊆ C) (hTC : T ⊆ C) :
    (((A.image₂ (· + ·) B) ∩ T).card : ℤ) ≤ schurTripleCount C := by
  classical
  have hsum : (schurTripleCount C : ℤ)
      = ∑ z ∈ C, ((C.filter fun x => z - x ∈ C).card : ℤ) := by
    rw [schurTripleCount_eq_sum_filter]
    exact Nat.cast_sum _ _
  have hsub : A.image₂ (· + ·) B ∩ T ⊆ C :=
    fun x hx => hTC (Finset.mem_inter.1 hx).2
  have hfiber : ∀ z ∈ (A.image₂ (· + ·) B ∩ T),
      (1 : ℤ) ≤ (C.filter fun x => z - x ∈ C).card := by
    intro z hz
    obtain ⟨hzAB, -⟩ := Finset.mem_inter.1 hz
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.mem_image₂.1 hzAB
    have hxmem : x ∈ C.filter fun x => z - x ∈ C := by
      rw [Finset.mem_filter]
      refine ⟨hAC hx, ?_⟩
      have : z - x = y := by omega
      rw [this]; exact hBC hy
    exact Finset.card_pos.2 ⟨x, hxmem⟩
  calc (((A.image₂ (· + ·) B) ∩ T).card : ℤ)
      = ∑ z ∈ (A.image₂ (· + ·) B ∩ T), (1 : ℤ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ ∑ z ∈ (A.image₂ (· + ·) B ∩ T),
          ((C.filter fun x => z - x ∈ C).card : ℤ) :=
        Finset.sum_le_sum hfiber
    _ ≤ schurTripleCount C := by
        rw [hsum]
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro x _ _; positivity

/-- **Low/high window bound.**  `low + high ⊆ (n/2, n]` shares a window of
size `≤ n/2 + 1` with `topHalf`, so

    `|low + high| + |topHalf| ≤ n/2 + 1 + schurTripleCount C`. -/
theorem low_high_window_bound {n : ℕ} {C : Finset ℤ} :
    (((lowBand n C).image₂ (· + ·) (highBand n C)).card : ℤ)
        + (topHalf n C).card
      ≤ (n : ℤ) / 2 + 1 + schurTripleCount C := by
  have h2 := card_image₂_add_card_le_inter_add
    (A := lowBand n C) (B := highBand n C) (T := topHalf n C)
    (a₁ := 1) (a₂ := (n : ℤ) / 4)
    (b₁ := (n : ℤ) / 2 + 1) (b₂ := 3 * (n : ℤ) / 4)
    (t₁ := (n : ℤ) / 2 + 1) (t₂ := (n : ℤ))
    Finset.inter_subset_right Finset.inter_subset_right Finset.inter_subset_right
  have hW : ((max ((n : ℤ) / 4 + 3 * (n : ℤ) / 4) (n : ℤ) + 1
        - min (1 + ((n : ℤ) / 2 + 1)) ((n : ℤ) / 2 + 1)).toNat : ℤ)
      ≤ (n : ℤ) / 2 + 1 := by omega
  have h3 := card_image₂_inter_le_schurTripleCount
    (A := lowBand n C) (B := highBand n C) (T := topHalf n C) (C := C)
    Finset.inter_subset_left Finset.inter_subset_left Finset.inter_subset_left
  omega

/-- **Low/high cardinality bound.**  When both bands are nonempty,
`|low + high| ≥ |low| + |high| − 1` upgrades the window bound to

    `|low| + |high| + |topHalf| ≤ n/2 + 2 + schurTripleCount C`. -/
theorem low_high_card_bound {n : ℕ} {C : Finset ℤ}
    (hlo : (lowBand n C).Nonempty) (hhi : (highBand n C).Nonempty) :
    ((lowBand n C).card + (highBand n C).card + (topHalf n C).card : ℤ)
      ≤ (n : ℤ) / 2 + 2 + schurTripleCount C := by
  have h1 := card_add_card_sub_one_le_card_image₂_add hlo hhi
  have h2 := low_high_window_bound (n := n) (C := C)
  omega

/-- **Low/high tradeoff (real form).**  If `C` has at most `δ·n²` Schur
triples then the cross sumset and the upper half cannot both be large:

    `|low + high| + |topHalf| ≤ n/2 + 1 + δ·n²`. -/
theorem low_high_tradeoff {n : ℕ} {C : Finset ℤ} (_hC : C ⊆ interval n) {δ : ℝ}
    (hsparse : (schurTripleCount C : ℝ) ≤ δ * (n : ℝ) ^ 2) :
    (((lowBand n C).image₂ (· + ·) (highBand n C)).card : ℝ)
        + (topHalf n C).card
      ≤ (n : ℝ) / 2 + 1 + δ * (n : ℝ) ^ 2 := by
  have h := low_high_window_bound (n := n) (C := C)
  have h' : (((lowBand n C).image₂ (· + ·) (highBand n C)).card : ℝ)
        + (topHalf n C).card
      ≤ (n : ℝ) / 2 + 1 + schurTripleCount C := by
    have hw : (((n : ℤ) / 2 + 1 : ℤ) : ℝ) ≤ (n : ℝ) / 2 + 1 := by
      have h1 : (n : ℤ) / 2 * 2 ≤ (n : ℤ) := Int.ediv_mul_le _ (by norm_num)
      have h2 : (((n : ℤ) / 2 : ℤ) : ℝ) * 2 ≤ (n : ℝ) := by exact_mod_cast h1
      linarith
    have h3 : (((lowBand n C).image₂ (· + ·) (highBand n C)).card : ℝ)
          + (topHalf n C).card
        ≤ (((n : ℤ) / 2 + 1 : ℤ) : ℝ) + schurTripleCount C := by
      exact_mod_cast h
    linarith
  linarith [h', hsparse]

/-- **Low/high cardinality tradeoff (real form).**  With both bands
nonempty: `|low| + |high| + |topHalf| ≤ n/2 + 2 + δ·n²`. -/
theorem low_high_card_tradeoff {n : ℕ} {C : Finset ℤ} (_hC : C ⊆ interval n)
    {δ : ℝ} (hsparse : (schurTripleCount C : ℝ) ≤ δ * (n : ℝ) ^ 2)
    (hlo : (lowBand n C).Nonempty) (hhi : (highBand n C).Nonempty) :
    ((lowBand n C).card + (highBand n C).card + (topHalf n C).card : ℝ)
      ≤ (n : ℝ) / 2 + 2 + δ * (n : ℝ) ^ 2 := by
  have h := low_high_card_bound (n := n) (C := C) hlo hhi
  have hw : (((n : ℤ) / 2 + 2 : ℤ) : ℝ) ≤ (n : ℝ) / 2 + 2 := by
    have h1 : (n : ℤ) / 2 * 2 ≤ (n : ℤ) := Int.ediv_mul_le _ (by norm_num)
    have h2 : (((n : ℤ) / 2 : ℤ) : ℝ) * 2 ≤ (n : ℝ) := by exact_mod_cast h1
    linarith
  have h3 : ((lowBand n C).card + (highBand n C).card + (topHalf n C).card : ℝ)
      ≤ (((n : ℤ) / 2 + 2 : ℤ) : ℝ) + schurTripleCount C := by
    exact_mod_cast h
  linarith [h3, hsparse, hw]

end JSP000728
