import JSPProblem.SparseCard
import JSPProblem.Supersat3
import JSPProblem.DFSTBridge
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# JSP-000728 — fiber-walk bounds for sparse containers

This file extends the record-level (first-passage) analysis of
`SparseCard.lean` to the *band structure* needed by the removal-bypass
architecture.  For `C ⊆ {1,…,n}` write

* `lowHalf n C = C ∩ [1, n/2]`  (the *low half*),
* `upHalf  n C = C ∩ (n/2, n]`  (the *upper half*).

## What is proved

* **Master fiber inequality** (`schurTripleCount_ge_sum_pos_fiber`): summing
  the per-sum inclusion–exclusion bound `r(z) ≥ 2|C∩[1,z−1]| − (z−1)`
  (`card_filter_sub_mem_ge`) over all `z ∈ C` gives, *exactly* (no error
  term),

      `∑ z ∈ C, max 0 (2·|C ∩ [1, z−1]| − (z − 1)) ≤ schurTripleCount C`.

  This strictly strengthens `schurTripleCount_ge_sum` (positive part) and the
  record-level bound `two_mul_schurTripleCount_ge_of_card` (the record
  passage times are the elements where the summand is `j − 1`).

* **Restricted first passage** (`two_mul_card_inter_Icc_le`,
  `card_inter_Icc_le_half_add_of_schurTripleCount_le`): the record argument
  applies to `C ∩ [1, m]` for *every* `m`, giving the unconditional bound

      `2·|C ∩ [1, m]| ≤ m + 1 + √(2·schurTripleCount C)`,

  hence `|C ∩ [1, m]| ≤ m/2 + ε·n` for all `m` when
  `schurTripleCount C ≤ δ·n²` with `δ` small enough.

* **Low–high cross bounds**
  (`card_lowHalf_add_two_mul_card_upHalf_le`,
  `three_mul_card_lowHalf_add_card_upHalf_le`,
  `card_product_filter_add_mem_le_schurTripleCount`): inclusion–exclusion of
  the sumset `low + up` (resp. `low + low`) against `up` (resp.
  `C ∩ [2, n]`) inside the common window `(n/2, 3n/2]` (resp. `[2, n]`),
  together with `|A + B| ≥ |A| + |B| − 1`, yields

      `|low| + 2·|up| ≤ n + 1 + T`,     `3·|low| + |up| ≤ n + 1 + T`,

  where `T = schurTripleCount C`; and the pair count
  `|{(x,y) ∈ low × up : x + y ∈ C}| ≤ T`.

* **The `3n/4` bound**
  (`two_mul_card_lowHalf_add_card_upHalf_le`,
  `two_mul_card_lowHalf_add_card_upHalf_le_of_schurTripleCount_le`):
  combining the prefix bound at `m = n/2` with the global bound gives

      `2·|low| + |up| ≤ 3n/4 + 1 + √(2·T)`,

  hence `2·|low| + |up| ≤ (3/4 + ε)·n` for sparse `C`.  This constant is
  **sharp**: `C = odds n` has `T = 0` and `2|low| + |up| = 3n/4 + O(1)`.

* **Even elements** (`four_mul_card_even_le`): even Schur triples halve to
  Schur triples of `{e/2 : e ∈ C, e even} ⊆ [1, n/2]`, so

      `4·|C ∩ evens| ≤ n + 2 + 2·T`.

* **Profile disjunction** (`lowHalf_upHalf_disjunction`): for any `ε`, either

      `2|low| + |up| ≤ n/2 + ε·n + (1 + √(2T))`

  or `C` has the *near-extremal cardinality profile* `|C| > n/4 + εn + s`,
  `|low| > εn + s`, `|up| > εn` (with `s = (1 + √(2T))/2`).

## What is NOT proved — the honest wall

The target disjunction `2|low|+|up| ≤ n/2 + o(n) ∨ |C ∖ odds| ≤ o(n)` is
**false as stated**: the *parity-flip* family

    `C = odds ∩ [1, (1/4 + η)n] ∪ evens ∩ (n/2, n]`

has `schurTripleCount C = Θ(η²n²)` (only the `odd+odd = even` pairs landing
in `(n/2, n]` contribute), yet `2|low| + |up| = n/2 + η·n` and
`|C ∩ evens| = n/4`.  It satisfies `2|low|+|up| > n/2 + εn` while being
`n/4`-far from `odds`, so the second disjunct must be enlarged to cover
near-extremal *parity-structured* sets, not only near-odd ones.
Equivalently: `2|low|+|up| > n/2 + εn` with `T ≤ δn²` is possible at
`η ≍ √δ`, and any correct disjunction needs `δ = O(ε²)` (compatible with the
`δ = ε²` scale already used in
`SparseCard.card_le_half_add_of_schurTripleCount_le`).  The profile
disjunction proved here (`lowHalf_upHalf_disjunction`) isolates the provable
cardinality shadow of this characterization; the remaining content is
parity-resolved fiber analysis (even `z ∈ C` pair with odd/odd or even/even
summands; the `(n/2, 3n/4]` even elements have thin representations — the
"DANGER" case of `removal_bypass_notes.md`).
-/

namespace JSP000728

/-! ## The two halves of `C` -/

/-- The low half of `C ⊆ [1, n]`: `C ∩ [1, n/2]` (`ℤ` integer division). -/
def lowHalf (n : ℕ) (C : Finset ℤ) : Finset ℤ :=
  C ∩ Finset.Icc 1 ((n : ℤ) / 2)

/-- The upper half of `C ⊆ [1, n]`: `C ∩ (n/2, n]` (`ℤ` integer division). -/
def upHalf (n : ℕ) (C : Finset ℤ) : Finset ℤ :=
  C ∩ Finset.Icc ((n : ℤ) / 2 + 1) (n : ℤ)

/-- The halves partition `C ⊆ [1, n]`: `|lowHalf| + |upHalf| = |C|`. -/
theorem card_lowHalf_add_card_upHalf {n : ℕ} {C : Finset ℤ}
    (hsub : C ⊆ interval n) :
    (lowHalf n C).card + (upHalf n C).card = C.card := by
  classical
  have hsubU : C ⊆ Finset.Icc 1 ((n : ℤ) / 2)
      ∪ Finset.Icc ((n : ℤ) / 2 + 1) (n : ℤ) := by
    intro x hx
    obtain ⟨hx1, hxn⟩ := Finset.mem_Icc.mp (hsub hx)
    rcases le_or_gt x ((n : ℤ) / 2) with h | h
    · exact Finset.mem_union_left _ (Finset.mem_Icc.mpr ⟨hx1, h⟩)
    · exact Finset.mem_union_right _
        (Finset.mem_Icc.mpr ⟨by omega, hxn⟩)
  have hunion : lowHalf n C ∪ upHalf n C = C := by
    rw [lowHalf, upHalf, ← Finset.inter_union_distrib_left,
      Finset.inter_eq_left.mpr hsubU]
  have hdisj : Disjoint (lowHalf n C) (upHalf n C) := by
    rw [Finset.disjoint_left]
    intro x hxl hxh
    obtain ⟨-, hxI⟩ := Finset.mem_inter.mp hxl
    obtain ⟨-, hxI'⟩ := Finset.mem_inter.mp hxh
    have h1 := (Finset.mem_Icc.mp hxI).2
    have h2 := (Finset.mem_Icc.mp hxI').1
    omega
  have hcard := Finset.card_union_of_disjoint hdisj
  rw [hunion] at hcard
  exact hcard.symm

/-! ## The master fiber inequality -/

/-- **Master fiber inequality.**  For `C ⊆ [1, n]`, each `z ∈ C` contributes
at least `max 0 (2·|C ∩ [1, z−1]| − (z − 1))` ordered representations
`z = x + (z − x)` with both summands in `C` (the fiber of the Schur triples
over `z`), so

    `∑ z ∈ C, max 0 (2·|C ∩ [1, z−1]| − (z − 1)) ≤ schurTripleCount C`.

This is the positive-part strengthening of `schurTripleCount_ge_sum`; on the
record passage times `t_j` of the walk `2|C∩[1,t]| − t` the summand equals
`j − 1`, recovering `two_mul_schurTripleCount_ge_of_card`. -/
theorem schurTripleCount_ge_sum_pos_fiber {n : ℕ} {C : Finset ℤ}
    (hsub : C ⊆ interval n) :
    (∑ z ∈ C, max 0 (2 * ((C ∩ Finset.Icc 1 (z - 1)).card : ℤ) - (z - 1)))
      ≤ schurTripleCount C := by
  classical
  have hsum : (schurTripleCount C : ℤ)
      = ∑ z ∈ C, ((C.filter fun x => z - x ∈ C).card : ℤ) := by
    rw [schurTripleCount_eq_sum_filter]
    exact Nat.cast_sum _ _
  rw [hsum]
  apply Finset.sum_le_sum
  intro z hz
  have hz1 : (1 : ℤ) ≤ z := (Finset.mem_Icc.mp (hsub hz)).1
  have hf := card_filter_sub_mem_ge C z
  rw [max_le_iff]
  refine ⟨Nat.cast_nonneg _, ?_⟩
  have htoNat : ((z - 1).toNat : ℤ) = z - 1 := Int.toNat_of_nonneg (by omega)
  have h2 : (2 : ℤ) * ((C ∩ Finset.Icc 1 (z - 1)).card : ℤ)
      ≤ (z - 1) + ((C.filter fun x => z - x ∈ C).card : ℤ) := by
    have hc : ((2 * (C ∩ Finset.Icc 1 (z - 1)).card : ℕ) : ℤ)
        ≤ (((z - 1).toNat + (C.filter fun x => z - x ∈ C).card : ℕ) : ℤ) := by
      exact_mod_cast hf
    rwa [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, htoNat] at hc
  omega

/-! ## Restricted first passage: bounds on every prefix -/

/-- Cutting `C` at `m` can only decrease the triple count. -/
theorem schurTripleCount_inter_Icc_le (C : Finset ℤ) (m : ℕ) :
    schurTripleCount (C ∩ Finset.Icc 1 (m : ℤ)) ≤ schurTripleCount C :=
  schurTripleCount_mono Finset.inter_subset_left

/-- **Restricted first passage, unconditional form.**  For every `m` and
every `C : Finset ℤ`,

    `2·|C ∩ [1, m]| ≤ m + 1 + √(2·schurTripleCount C)`.

Proof: apply the record bound `two_mul_schurTripleCount_ge_of_card` to
`C ∩ [1, m] ⊆ interval m` with `J = 2|C∩[1,m]| − m`; the fiber count
`J(J−1)/2` is controlled by `schurTripleCount (C ∩ [1,m]) ≤
schurTripleCount C`. -/
theorem two_mul_card_inter_Icc_le (C : Finset ℤ) (m : ℕ) :
    2 * ((C ∩ Finset.Icc 1 (m : ℤ)).card : ℝ)
      ≤ (m : ℝ) + 1 + Real.sqrt (2 * schurTripleCount C) := by
  set C' : Finset ℤ := C ∩ Finset.Icc 1 (m : ℤ) with hC'
  rcases le_or_gt (2 * C'.card) m with hle | hgt
  · have hle' : (2 * (C'.card : ℝ)) ≤ (m : ℝ) := by exact_mod_cast hle
    have hnn : (0 : ℝ) ≤ Real.sqrt (2 * schurTripleCount C) :=
      Real.sqrt_nonneg _
    linarith
  · have hsub' : C' ⊆ interval m := Finset.inter_subset_right
    set J : ℕ := 2 * C'.card - m with hJ
    have hJpos : 1 ≤ J := by omega
    have hJJ : m + J ≤ 2 * C'.card := by omega
    have hT := two_mul_schurTripleCount_ge_of_card hsub' hJJ
    have hT' : J * (J - 1) ≤ 2 * schurTripleCount C :=
      hT.trans (Nat.mul_le_mul (le_refl 2)
        (schurTripleCount_mono Finset.inter_subset_left))
    have hTR : (J : ℝ) * ((J : ℝ) - 1) ≤ 2 * (schurTripleCount C : ℝ) := by
      have hc : ((J * (J - 1) : ℕ) : ℝ)
          ≤ ((2 * schurTripleCount C : ℕ) : ℝ) := by
        exact_mod_cast hT'
      rwa [Nat.cast_mul, Nat.cast_sub hJpos, Nat.cast_one, Nat.cast_mul,
        Nat.cast_ofNat] at hc
    have hsq : ((J : ℝ) - 1) ^ 2 ≤ 2 * (schurTripleCount C : ℝ) := by
      have hJ1 : (1 : ℝ) ≤ (J : ℝ) := by exact_mod_cast hJpos
      nlinarith [hTR]
    have hle2 : (J : ℝ) - 1 ≤ Real.sqrt (2 * schurTripleCount C) :=
      Real.le_sqrt_of_sq_le hsq
    have hcast : (2 * (C'.card : ℝ)) = (m : ℝ) + (J : ℝ) := by
      rw [hJ, Nat.cast_sub hgt.le]
      push_cast
      ring
    linarith

/-- **Restricted first passage, asymptotic form.**  For every `ε > 0` there
is `δ > 0` such that eventually every `C ⊆ {1,…,n}` with at most `δ·n²`
Schur triples satisfies `|C ∩ [1, m]| ≤ m/2 + ε·n` for *every* `m`.  This is
`card_le_half_add_of_schurTripleCount_le` restricted to all prefixes at
once. -/
theorem card_inter_Icc_le_half_add_of_schurTripleCount_le {ε : ℝ}
    (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n : ℕ in Filter.atTop,
      ∀ C : Finset ℤ, C ⊆ interval n →
        (schurTripleCount C : ℝ) ≤ δ * (n : ℝ) ^ 2 →
        ∀ m : ℕ, ((C ∩ Finset.Icc 1 (m : ℤ)).card : ℝ)
          ≤ (m : ℝ) / 2 + ε * (n : ℝ) := by
  refine ⟨ε ^ 2 / 2, by positivity, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop ⌈1 / ε⌉₊] with n hn
  intro C _hsub htri m
  have hb := two_mul_card_inter_Icc_le C m
  have hsq : Real.sqrt (2 * (schurTripleCount C : ℝ)) ≤ ε * (n : ℝ) := by
    have h1 : (2 : ℝ) * schurTripleCount C ≤ (ε * (n : ℝ)) ^ 2 := by
      calc 2 * (schurTripleCount C : ℝ)
          ≤ 2 * (ε ^ 2 / 2) * (n : ℝ) ^ 2 := by nlinarith [htri]
        _ = (ε * (n : ℝ)) ^ 2 := by ring
    calc Real.sqrt (2 * (schurTripleCount C : ℝ))
        ≤ Real.sqrt ((ε * (n : ℝ)) ^ 2) := Real.sqrt_le_sqrt h1
      _ = ε * (n : ℝ) :=
          Real.sqrt_sq (mul_nonneg hε.le (Nat.cast_nonneg _))
  have hen : (1 : ℝ) ≤ ε * (n : ℝ) := by
    have h1 : (1 / ε : ℝ) ≤ ⌈1 / ε⌉₊ := Nat.le_ceil _
    have h2 : ((⌈(1 / ε : ℝ)⌉₊ : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have h3 := (div_le_iff₀ hε).mp (h1.trans h2)
    linarith
  linarith

/-! ## Window and cross-sumset bounds

The following two lemmas are the fiber/window ingredients (local analogues
of the band-triple bounds): a sumset and a target sharing an interval
window satisfy `|A + B| + |T| ≤ |(A+B) ∩ T| + |W|`, and every
`z ∈ (A + B) ∩ T` with `A, B, T ⊆ C` contributes at least one Schur triple
of `C`. -/

/-- **Window bound.**  If `A ⊆ [a₁, a₂]`, `B ⊆ [b₁, b₂]` and
`T ⊆ [t₁, t₂]`, then `A + B` and `T` lie in the common window
`W = [min (a₁+b₁) t₁, max (a₂+b₂) t₂]`, hence
`|A + B| + |T| ≤ |(A + B) ∩ T| + |W|`. -/
theorem card_image₂_add_card_le_inter_add_window {A B T : Finset ℤ}
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
    exact ⟨le_trans (min_le_right _ _) hz'.1,
      le_trans hz'.2 (le_max_right _ _)⟩
  have hU := Finset.card_le_card (Finset.union_subset hX hTW)
  rw [Int.card_Icc] at hU
  have h2 := Finset.card_union_add_card_inter (A.image₂ (· + ·) B) T
  have h3 : (A.image₂ (· + ·) B).card + T.card ≤
      ((A.image₂ (· + ·) B) ∩ T).card +
        (max (a₂ + b₂) t₂ + 1 - min (a₁ + b₁) t₁).toNat := by omega
  exact_mod_cast h3

/-- **One triple per represented sum.**  If `A, B, T ⊆ C`, every
`z ∈ (A + B) ∩ T` contributes at least one Schur triple `(x, z − x, z)` of
`C`, so `|(A + B) ∩ T| ≤ schurTripleCount C`. -/
theorem card_image₂_inter_le_schurTripleCount_of_subset {A B T C : Finset ℤ}
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
    have hpos : 0 < (C.filter fun x => z - x ∈ C).card :=
      Finset.card_pos.2 ⟨x, hxmem⟩
    exact_mod_cast hpos
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

/-- **Cross-sumset Cauchy–Davenport on `ℤ`.**  For nonempty `A B`,
`|A + B| ≥ |A| + |B| − 1`: the translates `min A + B` and `A + max B` lie
in `A + B` and overlap only in `min A + max B`. -/
theorem card_add_card_sub_one_le_card_image₂_add' {A B : Finset ℤ}
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
  have hcap : (B.image (fun x => amin + x)
      ∩ A.image (fun x => x + bmax)).card ≤ 1 :=
    (Finset.card_le_card hinter).trans (by simp)
  have hunion := Finset.card_union_add_card_inter
    (B.image fun x => amin + x) (A.image fun x => x + bmax)
  omega

/-! ## Low–high cross bounds -/

/-- **Low–up cross bound.**  `low + up ⊆ (n/2, 3n/2]` shares a window of
size `n` with `up ⊆ (n/2, n]`, so inclusion–exclusion plus
`|low + up| ≥ |low| + |up| − 1` and one triple per represented sum give

    `|low| + 2·|up| ≤ n + 1 + schurTripleCount C`. -/
theorem card_lowHalf_add_two_mul_card_upHalf_le {n : ℕ} {C : Finset ℤ}
    (_hsub : C ⊆ interval n) :
    ((lowHalf n C).card + 2 * (upHalf n C).card : ℤ)
      ≤ (n : ℤ) + 1 + schurTripleCount C := by
  classical
  have hwin := card_image₂_add_card_le_inter_add_window
    (A := lowHalf n C) (B := upHalf n C) (T := upHalf n C)
    (a₁ := 1) (a₂ := (n : ℤ) / 2) (b₁ := (n : ℤ) / 2 + 1) (b₂ := (n : ℤ))
    (t₁ := (n : ℤ) / 2 + 1) (t₂ := (n : ℤ))
    Finset.inter_subset_right Finset.inter_subset_right Finset.inter_subset_right
  have hW : ((max ((n : ℤ) / 2 + (n : ℤ)) (n : ℤ) + 1
      - min (1 + ((n : ℤ) / 2 + 1)) ((n : ℤ) / 2 + 1)).toNat : ℤ)
        ≤ (n : ℤ) := by omega
  have hhit := card_image₂_inter_le_schurTripleCount_of_subset
    (A := lowHalf n C) (B := upHalf n C) (T := upHalf n C) (C := C)
    Finset.inter_subset_left Finset.inter_subset_left Finset.inter_subset_left
  rcases (lowHalf n C).eq_empty_or_nonempty with hlo | hlo
  · -- `low = ∅`: bound `|up|` by the size of `(n/2, n]`.
    have h1 := Finset.card_le_card
      (Finset.inter_subset_right : upHalf n C ⊆ Finset.Icc _ _)
    rw [Int.card_Icc] at h1
    have hU : ((upHalf n C).card : ℤ) ≤ (n : ℤ) - (n : ℤ) / 2 := by
      have hU' : ((upHalf n C).card : ℤ)
          ≤ (((n : ℤ) + 1 - ((n : ℤ) / 2 + 1)).toNat : ℤ) := by
        exact_mod_cast h1
      have : (((n : ℤ) + 1 - ((n : ℤ) / 2 + 1)).toNat : ℤ)
          = (n : ℤ) - (n : ℤ) / 2 := by omega
      rwa [this] at hU'
    have hL0 : ((lowHalf n C).card : ℤ) = 0 := by rw [hlo]; simp
    omega
  rcases (upHalf n C).eq_empty_or_nonempty with hhi | hhi
  · -- `up = ∅`: bound `|low|` by the size of `[1, n/2]`.
    have h1 := Finset.card_le_card
      (Finset.inter_subset_right : lowHalf n C ⊆ Finset.Icc _ _)
    rw [Int.card_Icc] at h1
    have hL : ((lowHalf n C).card : ℤ) ≤ (n : ℤ) / 2 := by
      have hL' : ((lowHalf n C).card : ℤ)
          ≤ (((n : ℤ) / 2 + 1 - 1).toNat : ℤ) := by exact_mod_cast h1
      have : (((n : ℤ) / 2 + 1 - 1).toNat : ℤ) = (n : ℤ) / 2 := by omega
      rwa [this] at hL'
    have hU0 : ((upHalf n C).card : ℤ) = 0 := by rw [hhi]; simp
    omega
  · have hCD := card_add_card_sub_one_le_card_image₂_add' hlo hhi
    omega

/-- **Low–low bound.**  `low + low ⊆ [2, n]` shares the window `[2, n]`
(size `n − 1`) with `C ∩ [2, n]`; `|low + low| ≥ 2|low| − 1` and
`|C ∩ [2, n]| ≥ |C| − 1` give `2|low| + |C| ≤ n + 1 + schurTripleCount C`,
i.e.

    `3·|low| + |up| ≤ n + 1 + schurTripleCount C`. -/
theorem three_mul_card_lowHalf_add_card_upHalf_le {n : ℕ} {C : Finset ℤ}
    (hsub : C ⊆ interval n) :
    (3 * (lowHalf n C).card + (upHalf n C).card : ℤ)
      ≤ (n : ℤ) + 1 + schurTripleCount C := by
  classical
  set D : Finset ℤ := C ∩ Finset.Icc 2 (n : ℤ) with hDdef
  have hD : D = C.erase 1 := by
    ext x
    simp only [hDdef, Finset.mem_inter, Finset.mem_Icc, Finset.mem_erase]
    constructor
    · rintro ⟨hxC, hx2, -⟩
      exact ⟨by omega, hxC⟩
    · rintro ⟨hx1, hxC⟩
      obtain ⟨hx1', hxn⟩ := Finset.mem_Icc.mp (hsub hxC)
      exact ⟨hxC, by omega, hxn⟩
  have hDcard : (C.card : ℤ) ≤ D.card + 1 := by
    rw [hD]
    by_cases h1 : (1 : ℤ) ∈ C
    · have h2 := Finset.card_erase_add_one h1
      omega
    · have h2 : C.erase 1 = C := Finset.erase_eq_self.mpr h1
      rw [h2]
      omega
  have hwin := card_image₂_add_card_le_inter_add_window
    (A := lowHalf n C) (B := lowHalf n C) (T := D)
    (a₁ := 1) (a₂ := (n : ℤ) / 2) (b₁ := 1) (b₂ := (n : ℤ) / 2)
    (t₁ := 2) (t₂ := (n : ℤ))
    Finset.inter_subset_right Finset.inter_subset_right Finset.inter_subset_right
  have hW : ((max ((n : ℤ) / 2 + (n : ℤ) / 2) (n : ℤ) + 1 - min (1 + 1) 2).toNat
      : ℤ) ≤ ((n - 1 : ℕ) : ℤ) := by omega
  have hhit := card_image₂_inter_le_schurTripleCount_of_subset
    (A := lowHalf n C) (B := lowHalf n C) (T := D) (C := C)
    Finset.inter_subset_left Finset.inter_subset_left Finset.inter_subset_left
  have hsplit : ((lowHalf n C).card : ℤ) + (upHalf n C).card = C.card := by
    exact_mod_cast card_lowHalf_add_card_upHalf hsub
  rcases (lowHalf n C).eq_empty_or_nonempty with hlo | hlo
  · -- `low = ∅`: `|up| ≤ |C| ≤ n`.
    have hC : (C.card : ℤ) ≤ (n : ℤ) := by
      have h1 := Finset.card_le_card hsub
      rw [interval, Int.card_Icc] at h1
      have h2 : (((n : ℤ) + 1 - 1).toNat : ℤ) = (n : ℤ) := by omega
      have h3 : (C.card : ℤ) ≤ (((n : ℤ) + 1 - 1).toNat : ℤ) := by
        exact_mod_cast h1
      rwa [h2] at h3
    have hU : (upHalf n C).card ≤ C.card := by
      apply Finset.card_le_card
      intro x hx
      exact (Finset.mem_inter.mp hx).1
    have hL0 : ((lowHalf n C).card : ℤ) = 0 := by rw [hlo]; simp
    have hU' : ((upHalf n C).card : ℤ) ≤ C.card := by exact_mod_cast hU
    omega
  · -- A nonempty `lowHalf` forces `1 ≤ n/2` (its elements lie in
    -- `[1, n/2]`), which discharges the `n = 0, 1` degenerate cases.
    have hn2 : (1 : ℤ) ≤ (n : ℤ) / 2 := by
      obtain ⟨x, hx⟩ := hlo
      obtain ⟨hx1, hx2⟩ :=
        Finset.mem_Icc.mp (Finset.mem_inter.mp hx).2
      omega
    have hCD := two_mul_card_sub_one_le_card_image₂_add hlo
    omega

/-! ## The `3n/4` bound -/

/-- **The `3n/4` bound.**  `2·|low| + |up| = |low| + |C|`; the prefix bound
at `m = n/2` gives `|low| ≤ n/4 + (1 + √(2T))/2` and the global bound gives
`|C| ≤ n/2 + (1 + √(2T))/2`, hence

    `2·|low| + |up| ≤ 3n/4 + 1 + √(2·schurTripleCount C)`.

Sharp: `C = odds n` has `T = 0` and `2|low| + |up| = 3n/4 + O(1)`. -/
theorem two_mul_card_lowHalf_add_card_upHalf_le {n : ℕ} {C : Finset ℤ}
    (hsub : C ⊆ interval n) :
    2 * ((lowHalf n C).card : ℝ) + ((upHalf n C).card : ℝ)
      ≤ 3 * (n : ℝ) / 4 + 1 + Real.sqrt (2 * schurTripleCount C) := by
  have hdiv : ((n / 2 : ℕ) : ℤ) = (n : ℤ) / 2 := by omega
  have hL : lowHalf n C = C ∩ Finset.Icc 1 ((n / 2 : ℕ) : ℤ) := by
    rw [lowHalf, hdiv]
  have hb := two_mul_card_inter_Icc_le C (n / 2)
  rw [← hL] at hb
  have hCn : C ∩ Finset.Icc 1 (n : ℤ) = C := Finset.inter_eq_left.mpr hsub
  have hbC := two_mul_card_inter_Icc_le C n
  rw [hCn] at hbC
  have hsplit : ((lowHalf n C).card : ℝ) + (upHalf n C).card
      = (C.card : ℝ) := by
    exact_mod_cast card_lowHalf_add_card_upHalf hsub
  have hn2 : ((n / 2 : ℕ) : ℝ) ≤ (n : ℝ) / 2 := Nat.cast_div_le
  linarith

/-- **Sparse form of the `3n/4` bound.**  For every `ε > 0` there is
`δ > 0` such that eventually every `C ⊆ {1,…,n}` with at most `δ·n²` Schur
triples satisfies `2·|low| + |up| ≤ (3/4 + ε)·n`. -/
theorem two_mul_card_lowHalf_add_card_upHalf_le_of_schurTripleCount_le
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n : ℕ in Filter.atTop,
      ∀ C : Finset ℤ, C ⊆ interval n →
        (schurTripleCount C : ℝ) ≤ δ * (n : ℝ) ^ 2 →
        2 * ((lowHalf n C).card : ℝ) + (upHalf n C).card
          ≤ (3 / 4 + ε) * (n : ℝ) := by
  refine ⟨ε ^ 2 / 8, by positivity, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop ⌈4 / ε⌉₊] with n hn
  intro C hsub htri
  have h := two_mul_card_lowHalf_add_card_upHalf_le hsub
  have hsq : Real.sqrt (2 * (schurTripleCount C : ℝ))
      ≤ ε / 2 * (n : ℝ) := by
    have h1 : (2 : ℝ) * schurTripleCount C ≤ (ε / 2 * (n : ℝ)) ^ 2 := by
      calc 2 * (schurTripleCount C : ℝ)
          ≤ 2 * (ε ^ 2 / 8) * (n : ℝ) ^ 2 := by nlinarith [htri]
        _ = (ε / 2 * (n : ℝ)) ^ 2 := by ring
    calc Real.sqrt (2 * (schurTripleCount C : ℝ))
        ≤ Real.sqrt ((ε / 2 * (n : ℝ)) ^ 2) := Real.sqrt_le_sqrt h1
      _ = ε / 2 * (n : ℝ) :=
          Real.sqrt_sq (mul_nonneg (by positivity) (Nat.cast_nonneg _))
  have hen : (2 : ℝ) ≤ ε * (n : ℝ) := by
    have h1 : (4 / ε : ℝ) ≤ ⌈4 / ε⌉₊ := Nat.le_ceil _
    have h2 : ((⌈(4 / ε : ℝ)⌉₊ : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have h3 := (div_le_iff₀ hε).mp (h1.trans h2)
    linarith
  linarith

/-! ## Low–high pair count -/

/-- **Pair bound.**  For `A, B ⊆ C`, every ordered pair `(x, y) ∈ A × B`
with `x + y ∈ C` gives a distinct Schur triple `(x, y, x + y)`, so

    `|{(x, y) ∈ A ×ˢ B : x + y ∈ C}| ≤ schurTripleCount C`. -/
theorem card_product_filter_add_mem_le_schurTripleCount {C A B : Finset ℤ}
    (hA : A ⊆ C) (hB : B ⊆ C) :
    ((A ×ˢ B).filter fun p => p.1 + p.2 ∈ C).card ≤ schurTripleCount C := by
  classical
  apply Finset.card_le_card_of_injOn (fun p : ℤ × ℤ => (p.1, p.2, p.1 + p.2))
  · intro p hp
    rw [Finset.mem_coe] at hp
    obtain ⟨hpAB, hsum⟩ := Finset.mem_filter.mp hp
    rw [Finset.mem_product] at hpAB
    rw [Finset.mem_coe, schurTriples, Finset.mem_filter, Finset.mem_product,
      Finset.mem_product]
    exact ⟨⟨hA hpAB.1, hB hpAB.2, hsum⟩, rfl⟩
  · intro p _ q _ h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext_iff.mpr ⟨h.1, h.2.1⟩

/-- **Low–high pair bound.**  The cross representation count satisfies
`|{(x, y) ∈ low × up : x + y ∈ C}| ≤ schurTripleCount C`. -/
theorem card_lowHalf_upHalf_pair_le_schurTripleCount {n : ℕ}
    {C : Finset ℤ} :
    ((lowHalf n C ×ˢ upHalf n C).filter fun p => p.1 + p.2 ∈ C).card
      ≤ schurTripleCount C :=
  card_product_filter_add_mem_le_schurTripleCount
    Finset.inter_subset_left Finset.inter_subset_left

/-! ## Even elements via halving -/

/-- **Halving bound.**  Even Schur triples of `C` are the doubles of Schur
triples of `D = {e/2 : e ∈ C, e even} ⊆ [1, n/2]`, so
`2·|D| ≤ n/2 + 1 + schurTripleCount D ≤ n/2 + 1 + schurTripleCount C`,
giving

    `4·|C ∩ evens| ≤ n + 2 + 2·schurTripleCount C`,

i.e. a sparse `C` has at most `n/4 + o(n)` even elements. -/
theorem four_mul_card_even_le {n : ℕ} {C : Finset ℤ}
    (hsub : C ⊆ interval n) :
    4 * (C.filter fun x => x % 2 = 0).card
      ≤ n + 2 + 2 * schurTripleCount C := by
  classical
  set E : Finset ℤ := C.filter fun x => x % 2 = 0 with hE
  set D : Finset ℤ := E.image fun e => e / 2 with hD
  have hEven : ∀ e ∈ E, 2 * (e / 2) = e := by
    intro e he
    obtain ⟨-, he2⟩ := Finset.mem_filter.mp he
    omega
  have hinj : Set.InjOn (fun e : ℤ => e / 2) ↑E := by
    intro a ha b _hb hab
    have hab' : a / 2 = b / 2 := hab
    have h1 := hEven a (Finset.mem_coe.mp ha)
    have h2 := hEven b (Finset.mem_coe.mp _hb)
    omega
  have hDcard : D.card = E.card := Finset.card_image_of_injOn hinj
  have hDsub : D ⊆ interval (n / 2) := by
    intro d hd
    obtain ⟨e, he, hed⟩ := Finset.mem_image.mp hd
    obtain ⟨heC, he2⟩ := Finset.mem_filter.mp he
    obtain ⟨he1, hen⟩ := Finset.mem_Icc.mp (hsub heC)
    have hed' : e / 2 = d := hed
    rw [interval, Finset.mem_Icc]
    omega
  have hTD : schurTripleCount D ≤ schurTripleCount C := by
    have himg : (schurTriples D).image
        (fun t : ℤ × ℤ × ℤ => (2 * t.1, 2 * t.2.1, 2 * t.2.2))
        ⊆ schurTriples C := by
      intro t ht
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ht
      rw [schurTriples, Finset.mem_filter, Finset.mem_product,
        Finset.mem_product] at hu ⊢
      obtain ⟨⟨ha, hb, hc⟩, hab⟩ := hu
      have hC2 : ∀ d ∈ D, 2 * d ∈ C := by
        intro d hd
        obtain ⟨e, he, hed⟩ := Finset.mem_image.mp hd
        obtain ⟨heC, -⟩ := Finset.mem_filter.mp he
        have hed' : e / 2 = d := hed
        have h2e : 2 * d = e := by
          have := hEven e he
          omega
        rw [h2e]
        exact heC
      refine ⟨⟨hC2 _ ha, hC2 _ hb, hC2 _ hc⟩, ?_⟩
      show 2 * u.1 + 2 * u.2.1 = 2 * u.2.2
      omega
    have hinj2 : Function.Injective
        (fun t : ℤ × ℤ × ℤ => (2 * t.1, 2 * t.2.1, 2 * t.2.2)) := by
      intro x y h
      simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2, h3⟩ := h
      have e1 : x.1 = y.1 := by omega
      have e2 : x.2.1 = y.2.1 := by omega
      have e3 : x.2.2 = y.2.2 := by omega
      exact Prod.ext_iff.mpr ⟨e1, Prod.ext_iff.mpr ⟨e2, e3⟩⟩
    calc schurTripleCount D
        = (schurTriples D).card := rfl
      _ = ((schurTriples D).image
            fun t : ℤ × ℤ × ℤ => (2 * t.1, 2 * t.2.1, 2 * t.2.2)).card :=
          (Finset.card_image_of_injective _ hinj2).symm
      _ ≤ (schurTriples C).card := Finset.card_le_card himg
      _ = schurTripleCount C := rfl
  have hmain := two_mul_card_le_add_schurTripleCount hDsub
  omega

/-! ## The profile disjunction -/

/-- **Profile disjunction.**  With `s = (1 + √(2·T))/2` and `ε` arbitrary,
either the joint bound holds up to `o(n)` slack,

    `2·|low| + |up| ≤ n/2 + ε·n + 2s`,

or `C` has the near-extremal cardinality profile forced by
`2|low|+|up| = |low| + |C|`: `|C| > n/4 + εn + s`, `|low| > εn + s`, and
`|up| > εn`.

Note this is only the *cardinality* shadow of the extremal characterization:
the parity-flip family `odds ∩ [1,(1/4+η)n] ∪ evens ∩ (n/2,n]` shows that
sets with `|C ∩ evens| = n/4` can still reach `2|low|+|up| = n/2 + Θ(√T)`,
so a complete characterization must also resolve the parity structure of
`low` and `up`. -/
theorem lowHalf_upHalf_disjunction {n : ℕ} {C : Finset ℤ}
    (hsub : C ⊆ interval n) (ε : ℝ) :
    (2 * (lowHalf n C).card + (upHalf n C).card : ℝ)
        ≤ (n : ℝ) / 2 + ε * (n : ℝ)
          + (1 + Real.sqrt (2 * schurTripleCount C))
    ∨ ((n : ℝ) / 4 + ε * (n : ℝ)
          + (1 + Real.sqrt (2 * schurTripleCount C)) / 2 ≤ (C.card : ℝ)
        ∧ ε * (n : ℝ) + (1 + Real.sqrt (2 * schurTripleCount C)) / 2
          ≤ ((lowHalf n C).card : ℝ)
        ∧ ε * (n : ℝ) ≤ ((upHalf n C).card : ℝ)) := by
  set s : ℝ := (1 + Real.sqrt (2 * schurTripleCount C)) / 2 with hs
  have hdiv : ((n / 2 : ℕ) : ℤ) = (n : ℤ) / 2 := by omega
  have hL : lowHalf n C = C ∩ Finset.Icc 1 ((n / 2 : ℕ) : ℤ) := by
    rw [lowHalf, hdiv]
  have hb := two_mul_card_inter_Icc_le C (n / 2)
  rw [← hL] at hb
  have hCn : C ∩ Finset.Icc 1 (n : ℤ) = C := Finset.inter_eq_left.mpr hsub
  have hbC := two_mul_card_inter_Icc_le C n
  rw [hCn] at hbC
  have hsplit : ((lowHalf n C).card : ℝ) + (upHalf n C).card
      = (C.card : ℝ) := by
    exact_mod_cast card_lowHalf_add_card_upHalf hsub
  have hn2 : ((n / 2 : ℕ) : ℝ) ≤ (n : ℝ) / 2 := Nat.cast_div_le
  -- `2|low| ≤ n/2 + 2s` and `2|C| ≤ n + 2s`.
  have hb2 : 2 * ((lowHalf n C).card : ℝ)
      ≤ (n : ℝ) / 2 + 2 * s := by linarith
  have hbC2 : 2 * (C.card : ℝ) ≤ (n : ℝ) + 2 * s := by linarith
  rcases le_or_gt
      (2 * (lowHalf n C).card + (upHalf n C).card : ℝ)
      ((n : ℝ) / 2 + ε * (n : ℝ) + 2 * s) with h | h
  · left
    linarith
  · right
    refine ⟨?_, ?_, ?_⟩ <;> linarith

end JSP000728
