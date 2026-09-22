import JSPProblem.Supersaturation
import JSPProblem.DFSTBridge
import JSPProblem.LinkSumFree
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# JSP-000728 — Counting interval-type maximal sum-free sets

This file counts the *interval-type* maximal sum-free subsets of `{1,…,n}`
contained in a sparse container `C`: those `M` with `|M| > 2n/5` and
`M ⊆ [|M|, n]` (the interval branch of the DFST trichotomy, where
`min M ≥ |M|`, so `M ⊆ (2n/5, n]`).

**Note.**  `JSPProblem.BandTriple` does not compile under the current
toolchain/mathlib (`le_or_lt` was renamed, and some `linarith` calls break
on `Int.cast_add` atoms), so the needed band machinery is re-proved here
under `i`-prefixed names (`iMidBand`, `iTopBand`, `iTopHalf`, `iToeBand`,
`iMid_top_tradeoff`).  The proofs are the same cross-supersaturation
arguments: a fiber bound, a window bound, integer Cauchy–Davenport, and
the quadratic mid×top tradeoff.

## Counting architecture

For an interval-type `M` every element exceeds `2n/5`, so the fingerprint
`M ∩ [1, n/2]` lies in the middle band `iMidBand n C = C ∩ [2n/5, n/2]`
(`intervalType_subset`): at most `2^{|mid|}` fingerprints.  The trace
`M ∩ (n/2, n]` is a maximal link-independent subset of the upper half
`iTopHalf n C = C ∩ (n/2, n]` (`linkMaxIndepSet_inter_of_isMaxSumFree`),
and `L_S[iTopHalf]` is triangle-free for sum-free `S ⊆ [1,n]`
(`card_linkMaxSets_le_two_rpow`), giving `≤ 2^{|up|/2}` continuations.
Summing over *sum-free* fingerprints only (the trace `M ∩ B` is always
sum-free) yields the unconditional core bound

    `#intervalTypeSets n C ≤ 2^{|mid|} · 2^{|up|/2}`
    (`intervalTypeSets_card_le`).

## The exponent — key cancellation and the remaining wall

Writing `E = |mid| + |up|/2`:

* If the middle band is dense, `2|mid| > n/5 + 5 + √δ·n`, sparsity forces
  the top squeeze `|top| ≤ n/5 + 5 − 2|mid| + √δ·n` (`iMid_top_tradeoff`),
  and `|up| ≤ 3n/10 + |top|` (`iTopHalf_card_le_add_topBand`) gives
  `E ≤ n/4 + (5 + √δ·n)/2` — the exact `|mid|` cancellation
  (`interval_type_count_le_of_mid_dense`, unconditional given sparsity).

* If `2|mid| ≤ n/5 + 5 + √δ·n` (thin middle band), the unconditional
  bound `|up| ≤ n/2` only gives `E ≤ n/10 + n/4 + o(n)` — too big.
  The missing input is a bound on the *low* part of `C`: the hypothesis
  `LowBandBound n C ε` (`|C ∩ [1,n/2]| + |C| ≤ n/2 + ε·n`, the
  "`|low| + |C| ≤ n/2`" wall of the removal-bypass notes) implies
  `2|mid| + |up| ≤ n/2 + ε·n`, hence `E ≤ n/4 + ε·n/2`
  (`interval_type_count_le_of_lowBandBound`).

The main conditional theorem `interval_type_count_le` combines the two
routes: sparsity plus `LowBandBound` gives
`#intervalTypeSets ≤ 2^{n/4 + ε·n/2 + (5 + √δ·n)/2}`.
-/

namespace JSP000728

/-! ## Band definitions (local copies of the `BandTriple` bands) -/

/-- The middle band of `C ⊆ [1, n]`: `C ∩ [2n/5, n/2]` (integer division). -/
def iMidBand (n : ℕ) (C : Finset ℤ) : Finset ℤ :=
  C ∩ Finset.Icc (2 * (n : ℤ) / 5) ((n : ℤ) / 2)

/-- The top band of `C ⊆ [1, n]`: `C ∩ [4n/5, n]` (integer division). -/
def iTopBand (n : ℕ) (C : Finset ℤ) : Finset ℤ :=
  C ∩ Finset.Icc (4 * (n : ℤ) / 5) (n : ℤ)

/-- The upper half of `C ⊆ [1, n]`: `C ∩ (n/2, n]`. -/
def iTopHalf (n : ℕ) (C : Finset ℤ) : Finset ℤ :=
  C ∩ Finset.Icc ((n : ℤ) / 2 + 1) (n : ℤ)

/-- The *toe* band `C ∩ [1, 2n/5)`: the part of `C` lying below the
middle band. -/
def iToeBand (n : ℕ) (C : Finset ℤ) : Finset ℤ :=
  C ∩ Finset.Icc 1 (2 * (n : ℤ) / 5 - 1)

/-! ## Fiber and window bounds (from `BandTriple`, re-proved) -/

/-- **Inclusion–exclusion on a band.**  For `B ⊆ [lo, hi]` and any `z`,
both `B` and its reflection `z − B` lie in the interval
`K = [min lo (z − hi), max hi (z − lo)]`, so

    `|{x ∈ B : z − x ∈ B}| ≥ |B ∩ (z − B)| ≥ 2|B| − |K|`. -/
theorem iTwo_mul_card_le_card_filter_sub_mem_add {B : Finset ℤ} {z lo hi : ℤ}
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

/-- **Window bound.**  If `A ⊆ [a₁, a₂]`, `B ⊆ [b₁, b₂]` and
`T ⊆ [t₁, t₂]`, then `A + B` and `T` both lie in the window
`W = [min (a₁+b₁) t₁, max (a₂+b₂) t₂]`, hence
`|A + B| + |T| ≤ |(A + B) ∩ T| + |W|`. -/
theorem iCard_image₂_add_card_le_inter_add {A B T : Finset ℤ}
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

/-- **Quadratic supersaturation, band form.**  For bands
`B ⊆ [lo, hi]`, `T ⊆ [lo', hi']` inside `C`, if every `z ∈ T` has
container size `|K_z| ≤ w`, then

    `|(B + B) ∩ T| · (2|B| − w) ≤ schurTripleCount C`. -/
theorem iCard_image₂_inter_mul_le_schurTripleCount {C B T : Finset ℤ}
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
    have hfiber := iTwo_mul_card_le_card_filter_sub_mem_add (B := B) (z := z) hB
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

/-- **Middle/top product bound.**  Every `z ∈ (mid + mid) ∩ top`
contributes at least `2|mid| − n/5 − 5` Schur triples of `C`. -/
theorem iMid_top_card_mul_le_schurTripleCount {n : ℕ} {C : Finset ℤ} :
    (((iMidBand n C).image₂ (· + ·) (iMidBand n C) ∩ iTopBand n C).card : ℤ) *
        (2 * (iMidBand n C).card - ((n : ℤ) / 5 + 5)) ≤ schurTripleCount C := by
  apply iCard_image₂_inter_mul_le_schurTripleCount
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
theorem iMid_top_window_bound {n : ℕ} {C : Finset ℤ} :
    2 * ((iMidBand n C).card : ℤ) + (iTopBand n C).card ≤
      (((iMidBand n C).image₂ (· + ·) (iMidBand n C) ∩ iTopBand n C).card : ℤ) +
        ((n : ℤ) / 5 + 5) := by
  classical
  have h2 := iCard_image₂_add_card_le_inter_add
    (A := iMidBand n C) (B := iMidBand n C) (T := iTopBand n C)
    (a₁ := 2 * (n : ℤ) / 5) (a₂ := (n : ℤ) / 2)
    (b₁ := 2 * (n : ℤ) / 5) (b₂ := (n : ℤ) / 2)
    (t₁ := 4 * (n : ℤ) / 5) (t₂ := (n : ℤ))
    Finset.inter_subset_right Finset.inter_subset_right Finset.inter_subset_right
  have hW : ((max ((n : ℤ) / 2 + (n : ℤ) / 2) (n : ℤ) + 1
        - min (2 * (n : ℤ) / 5 + 2 * (n : ℤ) / 5) (4 * (n : ℤ) / 5)).toNat : ℤ)
      ≤ (n : ℤ) / 5 + 4 := by omega
  have hBB : 2 * ((iMidBand n C).card : ℤ)
      ≤ ((iMidBand n C).image₂ (· + ·) (iMidBand n C)).card + 1 := by
    rcases (iMidBand n C).eq_empty_or_nonempty with h | h
    · rw [h]; simp
    · exact two_mul_card_sub_one_le_card_image₂_add h
  omega

/-- **The band tradeoff (disjunctive form).**  If `C` has at most `δ·n²`
Schur triples, then either the middle band is at most half-full

    `2·|mid| ≤ n/5 + 5 + √δ·n`,

or the top band is squeezed by the middle band:

    `|top| ≤ n/5 + 5 − 2·|mid| + √δ·n`. -/
theorem iMid_top_tradeoff {n : ℕ} {C : Finset ℤ} (hC : C ⊆ interval n) {δ : ℝ}
    (hδ : 0 ≤ δ) (hsparse : (schurTripleCount C : ℝ) ≤ δ * (n : ℝ) ^ 2) :
    (2 * ((iMidBand n C).card : ℝ)) ≤ (n : ℝ) / 5 + 5 + Real.sqrt δ * n ∨
      ((iTopBand n C).card : ℝ)
        ≤ (n : ℝ) / 5 + 5 - 2 * (iMidBand n C).card + Real.sqrt δ * n := by
  have hw5 : (((n : ℤ) / 5 + 5 : ℤ) : ℝ) ≤ (n : ℝ) / 5 + 5 := by
    push_cast
    have h1 : (n : ℤ) / 5 * 5 ≤ (n : ℤ) := Int.ediv_mul_le _ (by norm_num)
    have h2 : (((n : ℤ) / 5 : ℤ) : ℝ) * 5 ≤ (n : ℝ) := by exact_mod_cast h1
    linarith
  have hA : (((iMidBand n C).image₂ (· + ·) (iMidBand n C)
          ∩ iTopBand n C).card : ℝ)
        * (2 * (iMidBand n C).card - (((n : ℤ) / 5 + 5 : ℤ) : ℝ))
      ≤ schurTripleCount C := by
    exact_mod_cast iMid_top_card_mul_le_schurTripleCount
  have hB : 2 * ((iMidBand n C).card : ℝ) + (iTopBand n C).card
      ≤ (((iMidBand n C).image₂ (· + ·) (iMidBand n C)
            ∩ iTopBand n C).card : ℝ)
        + (((n : ℤ) / 5 + 5 : ℤ) : ℝ) := by
    exact_mod_cast iMid_top_window_bound
  have hs : 0 ≤ Real.sqrt δ * (n : ℝ) :=
    mul_nonneg (Real.sqrt_nonneg _) (by positivity)
  have hsq : Real.sqrt δ * (n : ℝ) * (Real.sqrt δ * (n : ℝ))
      = δ * (n : ℝ) ^ 2 := by
    rw [mul_mul_mul_comm, Real.mul_self_sqrt hδ, pow_two]
  rcases lt_or_ge (Real.sqrt δ * (n : ℝ))
      (2 * ((iMidBand n C).card : ℝ) - (((n : ℤ) / 5 + 5 : ℤ) : ℝ))
      with hu | hu
  · -- `√δ·n < 2|mid| − w`: the squeeze disjunct.
    right
    by_contra hcon
    push_neg at hcon
    have hu0 : 0 < 2 * ((iMidBand n C).card : ℝ)
        - (((n : ℤ) / 5 + 5 : ℤ) : ℝ) :=
      lt_of_le_of_lt hs hu
    have hcut : Real.sqrt δ * (n : ℝ)
        < 2 * ((iMidBand n C).card : ℝ) - (((n : ℤ) / 5 + 5 : ℤ) : ℝ)
          + (iTopBand n C).card := by linarith
    have h1 : Real.sqrt δ * (n : ℝ) *
          (2 * ((iMidBand n C).card : ℝ) - (((n : ℤ) / 5 + 5 : ℤ) : ℝ))
        < (2 * ((iMidBand n C).card : ℝ) - (((n : ℤ) / 5 + 5 : ℤ) : ℝ)
            + (iTopBand n C).card) *
          (2 * ((iMidBand n C).card : ℝ) - (((n : ℤ) / 5 + 5 : ℤ) : ℝ)) :=
      mul_lt_mul_of_pos_right hcut hu0
    have h2 : Real.sqrt δ * (n : ℝ) * (Real.sqrt δ * (n : ℝ))
        ≤ Real.sqrt δ * (n : ℝ) *
          (2 * ((iMidBand n C).card : ℝ) - (((n : ℤ) / 5 + 5 : ℤ) : ℝ)) :=
      mul_le_mul_of_nonneg_left (le_of_lt hu) hs
    have h3 : (2 * ((iMidBand n C).card : ℝ) - (((n : ℤ) / 5 + 5 : ℤ) : ℝ)
            + (iTopBand n C).card) *
          (2 * ((iMidBand n C).card : ℝ) - (((n : ℤ) / 5 + 5 : ℤ) : ℝ))
        ≤ (((iMidBand n C).image₂ (· + ·) (iMidBand n C)
              ∩ iTopBand n C).card : ℝ) *
          (2 * ((iMidBand n C).card : ℝ) - (((n : ℤ) / 5 + 5 : ℤ) : ℝ)) :=
      mul_le_mul_of_nonneg_right (by linarith) (le_of_lt hu0)
    have h4 : Real.sqrt δ * (n : ℝ) * (Real.sqrt δ * (n : ℝ))
        < δ * (n : ℝ) ^ 2 :=
      lt_of_lt_of_le (lt_of_le_of_lt h2 (lt_of_lt_of_le h1 h3))
        (le_trans hA hsparse)
    rw [hsq] at h4
    exact lt_irrefl _ h4
  · -- `2|mid| − w ≤ √δ·n`: the thin-middle disjunct.
    left
    linarith

/-! ## The band partition -/

/-- `iToeBand` and `iMidBand` are disjoint (separated at `2n/5`). -/
theorem iToeBand_disjoint_iMidBand (n : ℕ) (C : Finset ℤ) :
    Disjoint (iToeBand n C) (iMidBand n C) := by
  rw [Finset.disjoint_left]
  intro x hx hxm
  rw [iToeBand, Finset.mem_inter, Finset.mem_Icc] at hx
  rw [iMidBand, Finset.mem_inter, Finset.mem_Icc] at hxm
  omega

/-- `iToeBand ∪ iMidBand` and `iTopHalf` are disjoint (separated at `n/2`). -/
theorem iToeBand_union_iMidBand_disjoint_iTopHalf (n : ℕ) (C : Finset ℤ) :
    Disjoint (iToeBand n C ∪ iMidBand n C) (iTopHalf n C) := by
  rw [Finset.disjoint_left]
  intro x hx hxm
  rw [iTopHalf, Finset.mem_inter, Finset.mem_Icc] at hxm
  rcases Finset.mem_union.1 hx with h | h
  · rw [iToeBand, Finset.mem_inter, Finset.mem_Icc] at h
    omega
  · rw [iMidBand, Finset.mem_inter, Finset.mem_Icc] at h
    omega

/-- The lower half of `C` splits at `2n/5` into toe and middle bands. -/
theorem low_Icc_eq_toe_union_mid {n : ℕ} {C : Finset ℤ}
    (hC : C ⊆ interval n) :
    C ∩ Finset.Icc 1 ((n : ℤ) / 2) = iToeBand n C ∪ iMidBand n C := by
  ext x
  constructor
  · intro hx
    obtain ⟨hxC, hxI⟩ := Finset.mem_inter.1 hx
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hxI
    rcases lt_or_ge x (2 * (n : ℤ) / 5) with h | h
    · exact Finset.mem_union.2 (Or.inl (Finset.mem_inter.2 ⟨hxC,
        Finset.mem_Icc.2 ⟨h1, by omega⟩⟩))
    · exact Finset.mem_union.2 (Or.inr (Finset.mem_inter.2 ⟨hxC,
        Finset.mem_Icc.2 ⟨h, h2⟩⟩))
  · intro hx
    rcases Finset.mem_union.1 hx with h | h
    · obtain ⟨hxC, hxI⟩ := Finset.mem_inter.1 h
      obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hxI
      exact Finset.mem_inter.2 ⟨hxC, Finset.mem_Icc.2 ⟨h1, by omega⟩⟩
    · obtain ⟨hxC, hxI⟩ := Finset.mem_inter.1 h
      obtain ⟨-, h2⟩ := Finset.mem_Icc.1 hxI
      exact Finset.mem_inter.2 ⟨hxC,
        Finset.mem_Icc.2 ⟨(Finset.mem_Icc.1 (hC hxC)).1, h2⟩⟩

/-- The band partition of `C ⊆ {1,…,n}`: `C = toe ∪ mid ∪ up`. -/
theorem C_eq_toe_union_mid_union_top {n : ℕ} {C : Finset ℤ}
    (hC : C ⊆ interval n) :
    C = iToeBand n C ∪ iMidBand n C ∪ iTopHalf n C := by
  ext x
  constructor
  · intro hxC
    obtain ⟨h1, hn⟩ := Finset.mem_Icc.1 (hC hxC)
    rcases lt_or_ge ((n : ℤ) / 2) x with h | h
    · -- `n/2 < x`: top half.
      exact Finset.mem_union.2 (Or.inr (Finset.mem_inter.2 ⟨hxC,
        Finset.mem_Icc.2 ⟨by omega, hn⟩⟩))
    · -- `x ≤ n/2`: toe or middle.
      refine Finset.mem_union.2 (Or.inl ?_)
      rcases lt_or_ge x (2 * (n : ℤ) / 5) with h2 | h2
      · exact Finset.mem_union.2 (Or.inl (Finset.mem_inter.2 ⟨hxC,
          Finset.mem_Icc.2 ⟨h1, by omega⟩⟩))
      · exact Finset.mem_union.2 (Or.inr (Finset.mem_inter.2 ⟨hxC,
          Finset.mem_Icc.2 ⟨h2, h⟩⟩))
  · intro hx
    rcases Finset.mem_union.1 hx with h | h
    · rcases Finset.mem_union.1 h with h | h <;>
        exact (Finset.mem_inter.1 h).1
    · exact (Finset.mem_inter.1 h).1

/-- Cardinality of the lower half of `C`. -/
theorem card_low_Icc {n : ℕ} {C : Finset ℤ} (hC : C ⊆ interval n) :
    (C ∩ Finset.Icc 1 ((n : ℤ) / 2)).card =
      (iToeBand n C).card + (iMidBand n C).card := by
  rw [low_Icc_eq_toe_union_mid hC,
    Finset.card_union_of_disjoint (iToeBand_disjoint_iMidBand n C)]

/-- Cardinality of `C` along the band partition. -/
theorem card_eq_toe_mid_top {n : ℕ} {C : Finset ℤ} (hC : C ⊆ interval n) :
    C.card = (iToeBand n C).card + (iMidBand n C).card +
      (iTopHalf n C).card := by
  conv_lhs => rw [C_eq_toe_union_mid_union_top hC]
  rw [Finset.card_union_of_disjoint
      (iToeBand_union_iMidBand_disjoint_iTopHalf n C),
    Finset.card_union_of_disjoint (iToeBand_disjoint_iMidBand n C)]

/-- The upper half `C ∩ (n/2, n]` is sum-free: two of its elements sum to
more than `n`. -/
theorem isSumFree_iTopHalf {n : ℕ} {C : Finset ℤ} (hC : C ⊆ interval n) :
    IsSumFree (iTopHalf n C) := by
  intro x hx y hy hxy
  have hx' := Finset.mem_Icc.1 (Finset.mem_inter.1 hx).2
  have hy' := Finset.mem_Icc.1 (Finset.mem_inter.1 hy).2
  have hz' := Finset.mem_Icc.1 (hC (Finset.mem_inter.1 hxy).1)
  omega

/-- The upper half splits at `4n/5`: `|up| ≤ 3n/10 + |top|`. -/
theorem iTopHalf_card_le_add_iTopBand {n : ℕ} {C : Finset ℤ} :
    ((iTopHalf n C).card : ℝ) ≤
      3 * (n : ℝ) / 10 + ((iTopBand n C).card : ℝ) := by
  classical
  have hsub : iTopHalf n C ⊆
      Finset.Icc ((n : ℤ) / 2 + 1) (4 * (n : ℤ) / 5 - 1) ∪ iTopBand n C := by
    intro x hx
    obtain ⟨hxC, hxI⟩ := Finset.mem_inter.1 hx
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hxI
    rcases lt_or_ge x (4 * (n : ℤ) / 5) with hlt | hge
    · exact Finset.mem_union.2 (Or.inl
        (Finset.mem_Icc.2 ⟨h1, by omega⟩))
    · exact Finset.mem_union.2 (Or.inr
        (Finset.mem_inter.2 ⟨hxC, Finset.mem_Icc.2 ⟨hge, h2⟩⟩))
  have hcard := Finset.card_le_card hsub
  have hunion : (Finset.Icc ((n : ℤ) / 2 + 1) (4 * (n : ℤ) / 5 - 1) ∪
        iTopBand n C).card ≤
      (Finset.Icc ((n : ℤ) / 2 + 1) (4 * (n : ℤ) / 5 - 1)).card +
        (iTopBand n C).card :=
    Finset.card_union_le _ _
  have hIcc : ((Finset.Icc ((n : ℤ) / 2 + 1) (4 * (n : ℤ) / 5 - 1)).card : ℝ)
      ≤ 3 * (n : ℝ) / 10 := by
    rw [Int.card_Icc]
    have htoNat : ∀ e : ℤ, ((e.toNat : ℕ) : ℝ) ≤ max (e : ℝ) 0 := by
      intro e
      rcases lt_or_ge e 0 with h | h
      · rw [Int.toNat_of_nonpos h.le]
        simp
      · rw [show ((e.toNat : ℕ) : ℝ) = ((e.toNat : ℤ) : ℝ) by norm_cast,
          Int.toNat_of_nonneg h]
        exact le_max_left _ _
    refine (htoNat _).trans (max_le_iff.mpr ⟨?_, by positivity⟩)
    push_cast
    have h1 : (((4 * (n : ℤ) / 5 : ℤ)) : ℝ) ≤ 4 * (n : ℝ) / 5 := by
      have h := Int.ediv_mul_le (4 * (n : ℤ)) (by norm_num : (5 : ℤ) ≠ 0)
      have h' : (((4 * (n : ℤ) / 5) * 5 : ℤ) : ℝ) ≤
          ((4 * (n : ℤ) : ℤ) : ℝ) := by exact_mod_cast h
      push_cast at h'
      linarith
    have h2 : ((n : ℝ) - 1) / 2 ≤ (((n : ℤ) / 2 : ℤ) : ℝ) := by
      have h : (n : ℤ) ≤ 2 * ((n : ℤ) / 2) + 1 := by omega
      have h' : ((n : ℤ) : ℝ) ≤ 2 * (((n : ℤ) / 2 : ℤ) : ℝ) + 1 := by
        exact_mod_cast h
      push_cast at h'
      linarith
    linarith
  have h3 : ((iTopHalf n C).card : ℝ) ≤
      ((Finset.Icc ((n : ℤ) / 2 + 1) (4 * (n : ℤ) / 5 - 1)).card : ℝ) +
        (iTopBand n C).card := by
    exact_mod_cast hcard.trans hunion
  linarith

/-! ## Interval-type sets -/

/-- The interval-type maximal sum-free sets housed by `C`: `M` is an
inclusion-maximal sum-free subset of `{1,…,n}`, `M ⊆ C`, `|M| > 2n/5`
(written `2n < 5|M|`), and `M` is pushed against the right endpoint,
`M ⊆ [|M|, n]` — the interval branch of the DFST trichotomy. -/
def intervalTypeSets (n : ℕ) (C : Finset ℤ) : Finset (Finset ℤ) :=
  (maxSumFreeSets n).filter fun M =>
    M ⊆ C ∧ 2 * n < 5 * M.card ∧ M ⊆ Finset.Icc (M.card : ℤ) (n : ℤ)

/-- Membership in `intervalTypeSets`. -/
theorem mem_intervalTypeSets {n : ℕ} {C M : Finset ℤ} :
    M ∈ intervalTypeSets n C ↔
      IsMaxSumFree n M ∧ (M ⊆ C ∧ 2 * n < 5 * M.card ∧
        M ⊆ Finset.Icc (M.card : ℤ) (n : ℤ)) := by
  rw [intervalTypeSets, Finset.mem_filter, mem_maxSumFreeSets]

/-- Every element of an interval-type `M` is at least `|M| > 2n/5`. -/
theorem intervalType_mem_ge {n : ℕ} {C M : Finset ℤ} {x : ℤ}
    (hM : M ∈ intervalTypeSets n C) (hx : x ∈ M) :
    2 * (n : ℤ) / 5 ≤ x := by
  obtain ⟨-, -, hcard, hsub⟩ := mem_intervalTypeSets.1 hM
  have h1 := Finset.mem_Icc.1 (hsub hx)
  omega

/-- An interval-type `M` lies in `[2n/5, n]`. -/
theorem intervalType_subset_Icc {n : ℕ} {C M : Finset ℤ}
    (hM : M ∈ intervalTypeSets n C) :
    M ⊆ Finset.Icc (2 * (n : ℤ) / 5) (n : ℤ) := by
  obtain ⟨-, -, hcard, hsub⟩ := mem_intervalTypeSets.1 hM
  intro x hx
  have h1 := Finset.mem_Icc.1 (hsub hx)
  rw [Finset.mem_Icc]
  omega

/-- An interval-type `M ⊆ C` lies in `iTopHalf ∪ iMidBand`: below `n/2`
it uses only the middle band (its elements exceed `2n/5`), above `n/2`
only the top half. -/
theorem intervalType_subset {n : ℕ} {C M : Finset ℤ}
    (hM : M ∈ intervalTypeSets n C) :
    M ⊆ iTopHalf n C ∪ iMidBand n C := by
  obtain ⟨-, hMC, hcard, hsub⟩ := mem_intervalTypeSets.1 hM
  intro x hx
  have hxge : 2 * (n : ℤ) / 5 ≤ x := by
    have h1 := Finset.mem_Icc.1 (hsub hx)
    omega
  have hxle : x ≤ (n : ℤ) := (Finset.mem_Icc.1 (hsub hx)).2
  rcases lt_or_ge ((n : ℤ) / 2) x with h | h
  · -- `n/2 < x`: top half.
    exact Finset.mem_union.2 (Or.inl (Finset.mem_inter.2 ⟨hMC hx,
      Finset.mem_Icc.2 ⟨by omega, hxle⟩⟩))
  · -- `x ≤ n/2`: middle band.
    exact Finset.mem_union.2 (Or.inr (Finset.mem_inter.2 ⟨hMC hx,
      Finset.mem_Icc.2 ⟨hxge, h⟩⟩))

/-- The interval-type family sits in the container filter. -/
theorem intervalTypeSets_subset_filter {n : ℕ} {C : Finset ℤ} :
    intervalTypeSets n C ⊆
      (maxSumFreeSets n).filter (· ⊆ iTopHalf n C ∪ iMidBand n C) := by
  intro M hM
  obtain ⟨hMax, -⟩ := mem_intervalTypeSets.1 hM
  exact Finset.mem_filter.2 ⟨mem_maxSumFreeSets.2 hMax,
    intervalType_subset hM⟩

/-! ## The fingerprint/link-graph count -/

/-- **Sum-free-fingerprint refinement** of the union counting bound: the
map `M ↦ (M ∩ B, M ∩ A)` injects the maximal sum-free sets housed by
`A ∪ B` into pairs `(S, t)` with `S ⊆ B` *sum-free* (traces of `M` are
always sum-free) and `t ∈ linkMaxSets S A`. -/
theorem card_maxSumFreeSets_filter_union_le_sum_linkMaxSets_filter_isSumFree
    {n : ℕ} {A B : Finset ℤ}
    (hAI : A ⊆ interval n) (hAsf : IsSumFree A) :
    ((maxSumFreeSets n).filter (· ⊆ A ∪ B)).card ≤
      ∑ S ∈ B.powerset.filter IsSumFree, (linkMaxSets S A).card := by
  classical
  have him : ∀ M ∈ (maxSumFreeSets n).filter (· ⊆ A ∪ B),
      (⟨M ∩ B, M ∩ A⟩ : Σ _ : Finset ℤ, Finset ℤ) ∈
        (B.powerset.filter IsSumFree).sigma fun S => linkMaxSets S A := by
    intro M hM
    obtain ⟨hMmem, hMC⟩ := Finset.mem_filter.mp hM
    have hMmax := mem_maxSumFreeSets.mp hMmem
    rw [Finset.mem_sigma]
    refine ⟨Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr Finset.inter_subset_right,
        hMmax.2.1.mono Finset.inter_subset_left⟩, ?_⟩
    rw [mem_linkMaxSets]
    exact ⟨Finset.inter_subset_right,
      linkMaxIndepSet_inter_of_isMaxSumFree hMmax hAI hAsf hMC⟩
  have hinj : Set.InjOn
      (fun M : Finset ℤ => (⟨M ∩ B, M ∩ A⟩ : Σ _ : Finset ℤ, Finset ℤ))
      ↑((maxSumFreeSets n).filter (· ⊆ A ∪ B)) := by
    intro M hM M' hM' heq
    obtain ⟨-, hMC⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hM)
    obtain ⟨-, hM'C⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hM')
    have h1 : M ∩ B = M' ∩ B := congrArg Sigma.fst heq
    have h2 : M ∩ A = M' ∩ A := congrArg Sigma.snd heq
    have e : M ∩ A ∪ M ∩ B = M := by
      ext y
      simp only [Finset.mem_union, Finset.mem_inter]
      constructor
      · rintro (⟨hy, -⟩ | ⟨hy, -⟩) <;> exact hy
      · intro hy
        rcases Finset.mem_union.mp (hMC hy) with h | h
        · exact Or.inl ⟨hy, h⟩
        · exact Or.inr ⟨hy, h⟩
    have e' : M' ∩ A ∪ M' ∩ B = M' := by
      ext y
      simp only [Finset.mem_union, Finset.mem_inter]
      constructor
      · rintro (⟨hy, -⟩ | ⟨hy, -⟩) <;> exact hy
      · intro hy
        rcases Finset.mem_union.mp (hM'C hy) with h | h
        · exact Or.inl ⟨hy, h⟩
        · exact Or.inr ⟨hy, h⟩
    calc M = M ∩ A ∪ M ∩ B := e.symm
      _ = M' ∩ A ∪ M' ∩ B := by rw [h1, h2]
      _ = M' := e'
  calc ((maxSumFreeSets n).filter (· ⊆ A ∪ B)).card
      ≤ ((B.powerset.filter IsSumFree).sigma
          fun S => linkMaxSets S A).card :=
        Finset.card_le_card_of_injOn _ him hinj
    _ = ∑ S ∈ B.powerset.filter IsSumFree, (linkMaxSets S A).card :=
        Finset.card_sigma _ _

/-- **Core count**: interval-type maximal sum-free sets in `C` number at
most `2^{|mid|} · 2^{|up|/2}` — `2^{|mid|}` middle-band fingerprints,
each with at most `2^{|up|/2}` maximal link-independent continuations in
the upper half (Hujter–Tuza on the sum-free ground `(n/2, n]`). -/
theorem intervalTypeSets_card_le {n : ℕ} {C : Finset ℤ}
    (hC : C ⊆ interval n) :
    ((intervalTypeSets n C).card : ℝ) ≤
      (2 : ℝ) ^ (iMidBand n C).card *
        (2 : ℝ) ^ (((iTopHalf n C).card : ℝ) / 2) := by
  classical
  have hAsf : IsSumFree (iTopHalf n C) := isSumFree_iTopHalf hC
  have hAI : iTopHalf n C ⊆ interval n := Finset.inter_subset_left.trans hC
  have hsub : intervalTypeSets n C ⊆
      (maxSumFreeSets n).filter (· ⊆ iTopHalf n C ∪ iMidBand n C) :=
    intervalTypeSets_subset_filter
  have hsigma :=
    card_maxSumFreeSets_filter_union_le_sum_linkMaxSets_filter_isSumFree
      (A := iTopHalf n C) (B := iMidBand n C) hAI hAsf
  have hcard : (intervalTypeSets n C).card ≤
      ∑ S ∈ (iMidBand n C).powerset.filter IsSumFree,
        (linkMaxSets S (iTopHalf n C)).card :=
    (Finset.card_le_card hsub).trans hsigma
  have hreal : ((intervalTypeSets n C).card : ℝ) ≤
      ∑ S ∈ (iMidBand n C).powerset.filter IsSumFree,
        ((linkMaxSets S (iTopHalf n C)).card : ℝ) := by
    exact_mod_cast hcard
  have hbound : ∀ S ∈ (iMidBand n C).powerset.filter IsSumFree,
      ((linkMaxSets S (iTopHalf n C)).card : ℝ) ≤
        (2 : ℝ) ^ (((iTopHalf n C).card : ℝ) / 2) := by
    intro S hS
    obtain ⟨hSpow, hSsf⟩ := Finset.mem_filter.1 hS
    have hSsub : S ⊆ interval n :=
      (Finset.mem_powerset.1 hSpow).trans
        (Finset.inter_subset_left.trans hC)
    refine card_linkMaxSets_le_two_rpow hSsub hSsf ?_
    intro x hx
    have hx' := Finset.mem_Icc.1 (Finset.mem_inter.1 hx).2
    omega
  calc ((intervalTypeSets n C).card : ℝ)
      ≤ _ := hreal
    _ ≤ ∑ _S ∈ (iMidBand n C).powerset.filter IsSumFree,
          (2 : ℝ) ^ (((iTopHalf n C).card : ℝ) / 2) :=
        Finset.sum_le_sum hbound
    _ = (((iMidBand n C).powerset.filter IsSumFree).card : ℝ) *
          (2 : ℝ) ^ (((iTopHalf n C).card : ℝ) / 2) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 : ℝ) ^ (iMidBand n C).card *
          (2 : ℝ) ^ (((iTopHalf n C).card : ℝ) / 2) := by
        refine mul_le_mul_of_nonneg_right ?_
          (Real.rpow_nonneg (by norm_num) _)
        have hle := Finset.card_le_card
          (Finset.filter_subset IsSumFree (iMidBand n C).powerset)
        rw [Finset.card_powerset] at hle
        exact_mod_cast hle

/-- Real-exponent form of the core count:
`#intervalTypeSets ≤ 2^{|mid| + |up|/2}`. -/
theorem intervalTypeSets_card_le_rpow {n : ℕ} {C : Finset ℤ}
    (hC : C ⊆ interval n) :
    ((intervalTypeSets n C).card : ℝ) ≤
      (2 : ℝ) ^ (((iMidBand n C).card : ℝ) +
        ((iTopHalf n C).card : ℝ) / 2) := by
  refine (intervalTypeSets_card_le hC).trans_eq ?_
  rw [← Real.rpow_natCast, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]

/-! ## The exponent bounds -/

/-- **The low-band hypothesis** — the remaining wall for the interval
count: `|C ∩ [1, n/2]| + |C| ≤ n/2 + ε·n`.  Since
`|C ∩ [1,n/2]| + |C| = 2|toe| + 2|mid| + |up|`, it yields
`2|mid| + |up| ≤ n/2 + ε·n`, exactly the exponent bound needed.  Note this
can fail for near-odd `C` (e.g. `C =` odds gives `3n/4`), so it is a
genuine hypothesis, not a consequence of sparsity. -/
def LowBandBound (n : ℕ) (C : Finset ℤ) (ε : ℝ) : Prop :=
  ((C ∩ Finset.Icc 1 ((n : ℤ) / 2)).card : ℝ) + (C.card : ℝ) ≤
    (n : ℝ) / 2 + ε * n

/-- Under `LowBandBound` the exponent `|mid| + |up|/2 ≤ n/4 + ε·n/2`. -/
theorem mid_add_topHalf_half_le_of_lowBandBound {n : ℕ} {C : Finset ℤ}
    (hC : C ⊆ interval n) {ε : ℝ} (hlow : LowBandBound n C ε) :
    ((iMidBand n C).card : ℝ) + ((iTopHalf n C).card : ℝ) / 2 ≤
      (n : ℝ) / 4 + ε * n / 2 := by
  have hlow' : ((C ∩ Finset.Icc 1 ((n : ℤ) / 2)).card : ℝ) +
      (C.card : ℝ) ≤ (n : ℝ) / 2 + ε * n := hlow
  have h1 : ((C ∩ Finset.Icc 1 ((n : ℤ) / 2)).card : ℝ) =
      (iToeBand n C).card + (iMidBand n C).card := by
    exact_mod_cast card_low_Icc hC
  have h2 : (C.card : ℝ) = (iToeBand n C).card + (iMidBand n C).card +
      (iTopHalf n C).card := by
    exact_mod_cast card_eq_toe_mid_top hC
  have htoe : (0 : ℝ) ≤ (iToeBand n C).card := by positivity
  linarith

/-- **The key cancellation**: if the top band is squeezed by the middle
band, `|top| ≤ n/5 + 5 − 2|mid| + √δ·n`, then
`|mid| + |up|/2 ≤ n/4 + (5 + √δ·n)/2` — the `|mid|` terms cancel. -/
theorem mid_add_topHalf_half_le_of_top_squeeze {n : ℕ} {C : Finset ℤ}
    {δ : ℝ}
    (hsqueeze : ((iTopBand n C).card : ℝ) ≤
      (n : ℝ) / 5 + 5 - 2 * (iMidBand n C).card + Real.sqrt δ * n) :
    ((iMidBand n C).card : ℝ) + ((iTopHalf n C).card : ℝ) / 2 ≤
      (n : ℝ) / 4 + (5 + Real.sqrt δ * n) / 2 := by
  have hup := iTopHalf_card_le_add_iTopBand (n := n) (C := C)
  linarith

/-! ## Final counting theorems -/

/-- **Interval-type count under the top squeeze.** -/
theorem interval_type_count_le_of_top_squeeze {n : ℕ} {C : Finset ℤ}
    (hC : C ⊆ interval n) {δ : ℝ}
    (hsqueeze : ((iTopBand n C).card : ℝ) ≤
      (n : ℝ) / 5 + 5 - 2 * (iMidBand n C).card + Real.sqrt δ * n) :
    ((intervalTypeSets n C).card : ℝ) ≤
      (2 : ℝ) ^ ((n : ℝ) / 4 + (5 + Real.sqrt δ * n) / 2) := by
  refine (intervalTypeSets_card_le_rpow hC).trans
    (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) ?_)
  exact mid_add_topHalf_half_le_of_top_squeeze hsqueeze

/-- **Unconditional count for dense middle band.**  If
`2|mid| > n/5 + 5 + √δ·n` then sparsity forces the top squeeze
(`iMid_top_tradeoff`), so the `1/4`-scale bound holds with no extra
hypothesis — the only gap is the thin-middle-band regime. -/
theorem interval_type_count_le_of_mid_dense {n : ℕ} {C : Finset ℤ}
    (hC : C ⊆ interval n) {δ : ℝ} (hδ : 0 ≤ δ)
    (hsparse : (schurTripleCount C : ℝ) ≤ δ * (n : ℝ) ^ 2)
    (hmid : (n : ℝ) / 5 + 5 + Real.sqrt δ * n <
      2 * ((iMidBand n C).card : ℝ)) :
    ((intervalTypeSets n C).card : ℝ) ≤
      (2 : ℝ) ^ ((n : ℝ) / 4 + (5 + Real.sqrt δ * n) / 2) := by
  rcases iMid_top_tradeoff hC hδ hsparse with hthin | hsqueeze
  · exfalso
    linarith
  · exact interval_type_count_le_of_top_squeeze hC hsqueeze

/-- **Interval-type count under the low-band hypothesis.** -/
theorem interval_type_count_le_of_lowBandBound {n : ℕ} {C : Finset ℤ}
    (hC : C ⊆ interval n) {ε : ℝ} (hlow : LowBandBound n C ε) :
    ((intervalTypeSets n C).card : ℝ) ≤
      (2 : ℝ) ^ ((n : ℝ) / 4 + ε * n / 2) := by
  refine (intervalTypeSets_card_le_rpow hC).trans
    (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) ?_)
  exact mid_add_topHalf_half_le_of_lowBandBound hC hlow

/-- **Main conditional interval-type count.**  For sparse
`C ⊆ {1,…,n}` (`schurTripleCount C ≤ δ·n²`) satisfying the low-band
hypothesis `LowBandBound n C ε`, the interval-type maximal sum-free sets
number at most `2^{n/4 + ε·n/2 + (5 + √δ·n)/2}` — the BLST `1/4` scale
up to `o(n)` slack. -/
theorem interval_type_count_le {n : ℕ} {C : Finset ℤ}
    (hC : C ⊆ interval n) {δ ε : ℝ} (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (hsparse : (schurTripleCount C : ℝ) ≤ δ * (n : ℝ) ^ 2)
    (hlow : LowBandBound n C ε) :
    ((intervalTypeSets n C).card : ℝ) ≤
      (2 : ℝ) ^ ((n : ℝ) / 4 + ε * n / 2 +
        (5 + Real.sqrt δ * n) / 2) := by
  refine (intervalTypeSets_card_le_rpow hC).trans
    (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) ?_)
  have hsqrt : (0 : ℝ) ≤ Real.sqrt δ * n :=
    mul_nonneg (Real.sqrt_nonneg _) (Nat.cast_nonneg _)
  have hεn : (0 : ℝ) ≤ ε * n := mul_nonneg hε (Nat.cast_nonneg _)
  rcases iMid_top_tradeoff hC hδ hsparse with hthin | hsqueeze
  · have h1 := mid_add_topHalf_half_le_of_lowBandBound hC hlow
    linarith
  · have h1 := mid_add_topHalf_half_le_of_top_squeeze hsqueeze
    linarith

end JSP000728
