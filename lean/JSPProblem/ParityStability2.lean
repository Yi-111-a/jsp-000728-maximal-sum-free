import JSPProblem.OddBound

/-!
# JSP-000728 — parity stability, part 2: audit + generalisations

## Audit result: the "top evens" question is *not* a hole

`removal_bypass_notes.md` (lines 37–45) worried about a thin-representation
regime: that `even_card_le_of_large_odd_subset` (ParityStability.lean)
might only cover even `e ≤ n/2` (difference-blocked) and `e ≥ n/2`
(sum-blocked) separately, leaving `e > n/2` elements with a single
difference-rep unaccounted for.

**The landed argument already covers every even `e ∈ C`.**  Its
per-element bound (`hrep`, ParityStability.lean:150–317) is on the *sum*
`|DR e| + |SR e| ≥ 4|M₀| − 3n/2 − 7/2 ≥ n/10 − 4`; no `e ≤ n/2`/`e ≥ n/2`
split ever occurs, and the two representation families inject into
*disjoint* sets of Schur triples of `C` (difference triples start with the
even `e`, sum triples with the odd `x`), so the counted union covers all of
`C ∖ odds n`.  This file makes the two regimes separately explicit:
`diffReps_ge_of_low_even` and `sumReps_ge_of_top_even` show
`|DR e| ≥ n/20 − 3/2` for `e ≤ n/2` and `|SR e| ≥ n/20 − 2` for `e ≥ n/2`
whenever `|M₀| > 2n/5` — each top even is individually *sum-blocked*, so
the pair-counting mitigation of the notes is unnecessary.  The explicit
top-half bound `top_even_card_mul_le_of_large_odd` is also proved here.

(Note: `ParityStability.lean` currently does not compile on this toolchain —
`Finset.sigma` now produces `Finset (Σ _ : ℤ, ℤ)` rather than `ℤ × ℤ`, and
`linarith` no longer pushes `Int.cast` through integer subtraction inside
atoms — so this file imports `JSPProblem.OddBound` directly and re-proves
the representation bounds in a toolchain-robust form.)

## What this file adds

* `diffReps`, `sumReps` — the representation sets as public definitions.
* `diffReps_sumReps_bounds_of_even` — standalone per-element bounds for
  **every** even `e ∈ [1, n]` and **every** `M₀ ⊆ odds n` (no size
  hypothesis):
  `|DR e| ≥ 2|M₀| − n/2 − e/2 − 3/2`, `|SR e| ≥ 2|M₀| − n + e/2 − 2`.
* `repSum_ge_of_even` — the combined bound
  `|DR e| + |SR e| ≥ 4|M₀| − 3n/2 − 7/2`.
* `schurTripleCount_ge_repSum` — standalone: for `E ⊆ C` all-even and
  `M₀ ⊆ C` all-odd, `∑_{e∈E} (|DR e| + |SR e|) ≤ schurTripleCount C`.
* `even_card_mul_le_of_odd_subset` — the amplification with the size
  hypothesis *removed*:
  `|C ∖ odds n| · (4|M₀| − 3n/2 − 7/2) ≤ schurTripleCount C`.
* `even_card_le_of_odd_subset_margin`, `even_card_le_of_sparse_odd_margin`
  — graceful degradation: `|M₀| ≥ (3/8 + γ)·n` gives
  `|C ∖ odds n| ≤ (δ / 4γ)·n + 7 / 8γ` for `δn²`-sparse `C`.
* `even_card_le_of_odd_dense`, `even_card_le_of_odd_dense_sparse`,
  `even_card_le_of_exists_odd_dense_maximal` — `M₀` need not be contained
  in `odds n`; only a large odd part `|M₀ ∩ odds n| ≥ (3/8+γ)n` is used.
* `top_even_card_mul_le_of_large_odd` — the explicit top-half bound
  `|(C ∖ odds n) ∩ (n/2, n]| · n ≤ 10·schurTripleCount C + 40n`.
* `maxSumFreeSets_filter_card_le_of_odd_dense` — the assembled counting
  bound `≤ 2^{(1/4+ε)n}` for `δn²`-sparse `C` housing a maximal `M₀` with
  `|M₀ ∩ odds n| > (3/8 + γ)n`, generalising
  `maxSumFreeSets_filter_card_le_of_large_odd`.

### On the `|M₀| > n/5` threshold

The two-set pigeonhole on the `≈ (n−e)/2` odd slots forces a
representation only when the relevant densities exceed `1/2`; the combined
bound `4|M₀| − 3n/2` is positive exactly when `|M₀| > 3n/8`.  Below `3n/8`
the rep bound is vacuous for *every* even `e`, so `n/5` is not reachable
by this argument — the honest relaxation is `(3/8 + γ)n` with constants
linear in `1/γ`, which is what the margin lemmas record.
-/

namespace JSP000728

/-- Difference representations of `e` in `M₀`: the `y ∈ M₀` with
`y + e ∈ M₀`, i.e. Schur triples `(e, y, e + y)`. -/
def diffReps (M₀ : Finset ℤ) (e : ℤ) : Finset ℤ :=
  M₀.filter fun y => y + e ∈ M₀

/-- Sum representations of `e` in `M₀`: the `x ∈ M₀` with `e - x ∈ M₀`,
i.e. Schur triples `(x, e - x, e)`. -/
def sumReps (M₀ : Finset ℤ) (e : ℤ) : Finset ℤ :=
  M₀.filter fun x => e - x ∈ M₀

/-- The odd integers in the integer interval `[a, b]`. -/
private def oddIcc (a b : ℤ) : Finset ℤ :=
  (Finset.Icc a b).filter fun x => x % 2 = 1

private theorem mem_oddIcc {a b x : ℤ} :
    x ∈ oddIcc a b ↔ a ≤ x ∧ x ≤ b ∧ x % 2 = 1 := by
  rw [oddIcc, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨h, h2⟩; exact ⟨h.1, h.2, h2⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, h3⟩

/-- An interval `[a, b]` (with `a ≤ b`) contains at most `(b − a)/2 + 1`
odd integers: `x ↦ (x + 1)/2` injects them into
`Icc ((a+2)/2) ((b+1)/2)`. -/
private theorem card_oddIcc_le {a b : ℤ} (hab : a ≤ b) :
    ((oddIcc a b).card : ℝ) ≤ ((b - a : ℤ) : ℝ) / 2 + 1 := by
  classical
  have hinj : Set.InjOn (fun x : ℤ => (x + 1) / 2) (↑(oddIcc a b) : Set ℤ) := by
    intro x hx y hy hxy
    rw [Finset.mem_coe, mem_oddIcc] at hx hy
    obtain ⟨kx, hkx⟩ : ∃ k : ℤ, x = 2 * k + 1 := ⟨x / 2, by omega⟩
    obtain ⟨ky, hky⟩ : ∃ k : ℤ, y = 2 * k + 1 := ⟨y / 2, by omega⟩
    have hk1 : (x + 1) / 2 = kx + 1 := by omega
    have hk2 : (y + 1) / 2 = ky + 1 := by omega
    have hxy' : (x + 1) / 2 = (y + 1) / 2 := hxy
    have : kx = ky := by omega
    omega
  have himg : (oddIcc a b).image (fun x : ℤ => (x + 1) / 2) ⊆
      Finset.Icc ((a + 2) / 2) ((b + 1) / 2) := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hax, hxb, hodd⟩ := mem_oddIcc.mp hx
    rw [Finset.mem_Icc]
    constructor <;> omega
  have hcard : (oddIcc a b).card ≤ ((b + 1) / 2 - (a + 2) / 2 + 1).toNat := by
    calc (oddIcc a b).card
        = ((oddIcc a b).image fun x : ℤ => (x + 1) / 2).card :=
          (Finset.card_image_of_injOn hinj).symm
      _ ≤ (Finset.Icc ((a + 2) / 2) ((b + 1) / 2)).card :=
          Finset.card_le_card himg
      _ = ((b + 1) / 2 - (a + 2) / 2 + 1).toNat := by
          rw [Int.card_Icc]
          congr 1
          ring
  have hz : (b + 1) / 2 - (a + 2) / 2 + 1 ≤ (b - a) / 2 + 1 := by omega
  have hw : (0 : ℤ) ≤ (b - a) / 2 + 1 := by omega
  have hcard2 : (oddIcc a b).card ≤ ((b - a) / 2 + 1).toNat :=
    hcard.trans (Int.toNat_le_toNat hz)
  have hcast : ((oddIcc a b).card : ℝ) ≤ (((b - a) / 2 + 1 : ℤ) : ℝ) := by
    have h1 : ((oddIcc a b).card : ℝ) ≤ ((((b - a) / 2 + 1).toNat : ℕ) : ℝ) := by
      exact_mod_cast hcard2
    have h2 : ((((b - a) / 2 + 1).toNat : ℕ) : ℝ) =
        (((b - a) / 2 + 1 : ℤ) : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg hw
    rwa [h2] at h1
  refine hcast.trans ?_
  push_cast
  have h4 : (2 : ℤ) * ((b - a) / 2) ≤ b - a := by omega
  have h5 : (2 : ℝ) * (((b - a) / 2 : ℤ) : ℝ) ≤ (b - a : ℝ) := by
    exact_mod_cast h4
  linarith

/-- **Standalone representation bounds** (reusable).  For *every* even
`e ∈ [1, n]` and *every* `M₀ ⊆ odds n` — no size hypothesis on `M₀`:

* `|DR e| ≥ 2·|M₀| − n/2 − e/2 − 3/2` (difference representations), and
* `|SR e| ≥ 2·|M₀| − n + e/2 − 2` (sum representations).

Both `DR e` and `SR e` are intersections of two translates of `M₀` inside
the odd slots of an interval, and the bounds come from the odd-slot
pigeonhole; the two bounds are complementary in `e`, which is why their
sum `4|M₀| − 3n/2 − 7/2` is `e`-independent. -/
theorem diffReps_sumReps_bounds_of_even {n : ℕ} {M₀ : Finset ℤ}
    (hModd : M₀ ⊆ odds n) {e : ℤ}
    (he1 : 1 ≤ e) (hen : e ≤ (n : ℤ)) (hep : e % 2 = 0) :
    (2 * (M₀.card : ℝ) - (n : ℝ) / 2 - (e : ℝ) / 2 - 3 / 2 ≤
        ((diffReps M₀ e).card : ℝ)) ∧
      (2 * (M₀.card : ℝ) - (n : ℝ) + (e : ℝ) / 2 - 2 ≤
        ((sumReps M₀ e).card : ℝ)) := by
  classical
  have hMmem : ∀ x ∈ M₀, 1 ≤ x ∧ x ≤ (n : ℤ) ∧ x % 2 = 1 := by
    intro x hx
    obtain ⟨hxI, hodd⟩ := mem_odds.mp (hModd hx)
    obtain ⟨h1, hn⟩ := Finset.mem_Icc.mp hxI
    exact ⟨h1, hn, hodd⟩
  -- `M₀` split at `n − e`, at `e` and at `e − 1`.
  have hsplit1 : M₀ ⊆ (M₀ ∩ Finset.Icc 1 ((n : ℤ) - e)) ∪
      oddIcc ((n : ℤ) - e + 1) (n : ℤ) := by
    intro x hx
    obtain ⟨hx1, hxn, hodd⟩ := hMmem x hx
    rw [Finset.mem_union]
    rcases le_or_gt x ((n : ℤ) - e) with h | h
    · exact Or.inl (Finset.mem_inter.mpr ⟨hx, Finset.mem_Icc.mpr ⟨hx1, h⟩⟩)
    · exact Or.inr (mem_oddIcc.mpr ⟨by omega, hxn, hodd⟩)
  have hcard1 : M₀.card ≤ (M₀ ∩ Finset.Icc 1 ((n : ℤ) - e)).card +
      (oddIcc ((n : ℤ) - e + 1) (n : ℤ)).card :=
    (Finset.card_le_card hsplit1).trans (Finset.card_union_le _ _)
  have hsplit2 : M₀ ⊆ (M₀ ∩ Finset.Icc (e + 1) (n : ℤ)) ∪ oddIcc 1 e := by
    intro x hx
    obtain ⟨hx1, hxn, hodd⟩ := hMmem x hx
    rw [Finset.mem_union]
    rcases le_or_gt x e with h | h
    · exact Or.inr (mem_oddIcc.mpr ⟨hx1, h, hodd⟩)
    · exact Or.inl (Finset.mem_inter.mpr ⟨hx, Finset.mem_Icc.mpr ⟨by omega, hxn⟩⟩)
  have hcard2 : M₀.card ≤ (M₀ ∩ Finset.Icc (e + 1) (n : ℤ)).card +
      (oddIcc 1 e).card :=
    (Finset.card_le_card hsplit2).trans (Finset.card_union_le _ _)
  have hsplit3 : M₀ ⊆ (M₀ ∩ Finset.Icc 1 (e - 1)) ∪ oddIcc e (n : ℤ) := by
    intro x hx
    obtain ⟨hx1, hxn, hodd⟩ := hMmem x hx
    rw [Finset.mem_union]
    rcases le_or_gt x (e - 1) with h | h
    · exact Or.inl (Finset.mem_inter.mpr ⟨hx, Finset.mem_Icc.mpr ⟨hx1, h⟩⟩)
    · exact Or.inr (mem_oddIcc.mpr ⟨by omega, hxn, hodd⟩)
  have hcard3 : M₀.card ≤ (M₀ ∩ Finset.Icc 1 (e - 1)).card +
      (oddIcc e (n : ℤ)).card :=
    (Finset.card_le_card hsplit3).trans (Finset.card_union_le _ _)
  -- `|DR e| ≥ |M₀ ∩ [1, n−e]| + |M₀ ∩ [e+1, n]| − |oddIcc 1 (n−e)|`.
  set L : Finset ℤ := M₀ ∩ Finset.Icc 1 ((n : ℤ) - e) with hLdef
  set U' : Finset ℤ := (M₀ ∩ Finset.Icc (e + 1) (n : ℤ)).image (· - e) with hUdef
  have hUcard : U'.card = (M₀ ∩ Finset.Icc (e + 1) (n : ℤ)).card :=
    Finset.card_image_of_injective _ (fun a b h => by omega)
  have hLUsub : L ∪ U' ⊆ oddIcc 1 ((n : ℤ) - e) := by
    intro y hy
    rcases Finset.mem_union.mp hy with hy | hy
    · obtain ⟨hyM, hyI⟩ := Finset.mem_inter.mp hy
      obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hyI
      exact mem_oddIcc.mpr ⟨h1, h2, (hMmem y hyM).2.2⟩
    · obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
      obtain ⟨hzM, hzI⟩ := Finset.mem_inter.mp hz
      obtain ⟨hz1, hz2⟩ := Finset.mem_Icc.mp hzI
      refine mem_oddIcc.mpr ⟨by omega, by omega, ?_⟩
      have hodd := (hMmem z hzM).2.2
      omega
  have hLUin : L ∩ U' ⊆ diffReps M₀ e := by
    intro y hy
    obtain ⟨hyL, hyU⟩ := Finset.mem_inter.mp hy
    obtain ⟨z, hz, hzeq⟩ := Finset.mem_image.mp hyU
    obtain ⟨hzM, -⟩ := Finset.mem_inter.mp hz
    refine Finset.mem_filter.mpr ⟨(Finset.mem_inter.mp hyL).1, ?_⟩
    have hze : y + e = z := by omega
    rw [hze]
    exact hzM
  have hUunion : (L ∪ U').card ≤ (oddIcc 1 ((n : ℤ) - e)).card :=
    Finset.card_le_card hLUsub
  have hinter : (L ∩ U').card ≤ (diffReps M₀ e).card :=
    Finset.card_le_card hLUin
  have hUUI := Finset.card_union_add_card_inter L U'
  rw [hUcard] at hUUI
  have hDRnat : (diffReps M₀ e).card + (oddIcc 1 ((n : ℤ) - e)).card ≥
      L.card + (M₀ ∩ Finset.Icc (e + 1) (n : ℤ)).card := by omega
  -- `|SR e| ≥ 2·|M₀ ∩ [1, e−1]| − |oddIcc 1 (e−1)|`.
  set L1 : Finset ℤ := M₀ ∩ Finset.Icc 1 (e - 1) with hL1def
  set S' : Finset ℤ := L1.image (e - ·) with hSdef
  have hScard : S'.card = L1.card :=
    Finset.card_image_of_injective _ (fun a b h => by omega)
  have hLSsub : L1 ∪ S' ⊆ oddIcc 1 (e - 1) := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨hxM, hxI⟩ := Finset.mem_inter.mp hx
      obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hxI
      exact mem_oddIcc.mpr ⟨h1, h2, (hMmem x hxM).2.2⟩
    · obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨hzM, hzI⟩ := Finset.mem_inter.mp hz
      obtain ⟨hz1, hz2⟩ := Finset.mem_Icc.mp hzI
      refine mem_oddIcc.mpr ⟨by omega, by omega, ?_⟩
      have hodd := (hMmem z hzM).2.2
      omega
  have hLSin : L1 ∩ S' ⊆ sumReps M₀ e := by
    intro x hx
    obtain ⟨hxL, hxS⟩ := Finset.mem_inter.mp hx
    obtain ⟨z, hz, hzeq⟩ := Finset.mem_image.mp hxS
    obtain ⟨hzM, -⟩ := Finset.mem_inter.mp hz
    refine Finset.mem_filter.mpr ⟨(Finset.mem_inter.mp hxL).1, ?_⟩
    have hze : e - x = z := by omega
    rw [hze]
    exact hzM
  have hLSunion : (L1 ∪ S').card ≤ (oddIcc 1 (e - 1)).card :=
    Finset.card_le_card hLSsub
  have hinter2 : (L1 ∩ S').card ≤ (sumReps M₀ e).card :=
    Finset.card_le_card hLSin
  have hLSI := Finset.card_union_add_card_inter L1 S'
  rw [hScard] at hLSI
  have hSRnat : (sumReps M₀ e).card + (oddIcc 1 (e - 1)).card ≥
      2 * L1.card := by omega
  -- real-valued bounds on the odd-slot counts, stated in `↑n`, `↑e`-normal
  -- form so that `linarith` sees uniform atoms
  have ho1 : ((oddIcc ((n : ℤ) - e + 1) (n : ℤ)).card : ℝ) ≤
      ((e : ℝ) - 1) / 2 + 1 := by
    have h := card_oddIcc_le (a := (n : ℤ) - e + 1) (b := (n : ℤ)) (by omega)
    have heq : (((n : ℤ) - ((n : ℤ) - e + 1) : ℤ) : ℝ) = (e : ℝ) - 1 := by
      push_cast; ring
    rwa [heq] at h
  have ho2 : ((oddIcc 1 e).card : ℝ) ≤ ((e : ℝ) - 1) / 2 + 1 := by
    have h := card_oddIcc_le (a := (1 : ℤ)) (b := e) (by omega)
    have heq : (((e - 1 : ℤ)) : ℝ) = (e : ℝ) - 1 := by push_cast; ring
    rwa [heq] at h
  have ho3 : ((oddIcc 1 ((n : ℤ) - e)).card : ℝ) ≤
      ((n : ℝ) - (e : ℝ) - 1) / 2 + 1 := by
    rcases le_or_gt 1 ((n : ℤ) - e) with hle | hgt
    · have h := card_oddIcc_le (a := (1 : ℤ)) (b := (n : ℤ) - e) hle
      push_cast at h
      exact h
    · have hempty : oddIcc 1 ((n : ℤ) - e) = ∅ := by
        have h : Finset.Icc (1 : ℤ) ((n : ℤ) - e) = ∅ :=
          Finset.Icc_eq_empty_iff.mpr (by omega)
        rw [oddIcc, h, Finset.filter_empty]
      rw [hempty, Finset.card_empty]
      have hi : (0 : ℤ) ≤ (n : ℤ) - e := by omega
      have hr : (0 : ℝ) ≤ ((n : ℤ) - e : ℝ) := by exact_mod_cast hi
      push_cast at hr
      linarith
  have ho4 : ((oddIcc e (n : ℤ)).card : ℝ) ≤ ((n : ℝ) - (e : ℝ)) / 2 + 1 := by
    have h := card_oddIcc_le (a := e) (b := (n : ℤ)) (by omega)
    push_cast at h
    exact h
  have ho5 : ((oddIcc 1 (e - 1)).card : ℝ) ≤ (e : ℝ) / 2 := by
    have h := card_oddIcc_le (a := (1 : ℤ)) (b := e - 1) (by omega)
    have heq : (((e - 1 - 1 : ℤ)) : ℝ) / 2 + 1 = (e : ℝ) / 2 := by
      push_cast; ring
    rwa [heq] at h
  -- cast the nat inequalities; `L.card`, `L1.card` are kept as `set`
  -- variables so the atoms match `hDRr`/`hSRr`
  have hLr : (L.card : ℝ) ≥ (M₀.card : ℝ) - (((e : ℝ) - 1) / 2 + 1) := by
    have h' : (M₀.card : ℝ) ≤
        (L.card : ℝ) + ((oddIcc ((n : ℤ) - e + 1) (n : ℤ)).card : ℝ) := by
      exact_mod_cast hcard1
    linarith
  have hUr : ((M₀ ∩ Finset.Icc (e + 1) (n : ℤ)).card : ℝ) ≥
      (M₀.card : ℝ) - (((e : ℝ) - 1) / 2 + 1) := by
    have h' : (M₀.card : ℝ) ≤
        ((M₀ ∩ Finset.Icc (e + 1) (n : ℤ)).card : ℝ) +
          ((oddIcc 1 e).card : ℝ) := by
      exact_mod_cast hcard2
    linarith
  have hL1r : (L1.card : ℝ) ≥
      (M₀.card : ℝ) - (((n : ℝ) - (e : ℝ)) / 2 + 1) := by
    have h' : (M₀.card : ℝ) ≤
        (L1.card : ℝ) + ((oddIcc e (n : ℤ)).card : ℝ) := by
      exact_mod_cast hcard3
    linarith
  have hDRr : ((diffReps M₀ e).card : ℝ) +
      ((oddIcc 1 ((n : ℤ) - e)).card : ℝ) ≥
      (L.card : ℝ) + ((M₀ ∩ Finset.Icc (e + 1) (n : ℤ)).card : ℝ) := by
    exact_mod_cast hDRnat
  have hSRr : ((sumReps M₀ e).card : ℝ) + ((oddIcc 1 (e - 1)).card : ℝ) ≥
      2 * (L1.card : ℝ) := by
    exact_mod_cast hSRnat
  constructor <;> linarith

/-- **Combined representation bound**: for every even `e ∈ [1, n]` and
every `M₀ ⊆ odds n`,
`|DR e| + |SR e| ≥ 4·|M₀| − 3n/2 − 7/2` — positive exactly when
`|M₀| > 3n/8 + O(1)`, uniform in `e` (no `e ≤ n/2` split). -/
theorem repSum_ge_of_even {n : ℕ} {M₀ : Finset ℤ} (hModd : M₀ ⊆ odds n)
    {e : ℤ} (he1 : 1 ≤ e) (hen : e ≤ (n : ℤ)) (hep : e % 2 = 0) :
    4 * (M₀.card : ℝ) - 3 * (n : ℝ) / 2 - 7 / 2 ≤
      ((diffReps M₀ e).card : ℝ) + ((sumReps M₀ e).card : ℝ) := by
  obtain ⟨h1, h2⟩ := diffReps_sumReps_bounds_of_even hModd he1 hen hep
  linarith

/-- **Low evens are difference-blocked**: for even `e ∈ [1, n/2]` and
`|M₀| > 2n/5`, `|DR e| ≥ n/20 − 3/2`. -/
theorem diffReps_ge_of_low_even {n : ℕ} {M₀ : Finset ℤ}
    (hModd : M₀ ⊆ odds n) (hMbig : (2 / 5 : ℝ) * (n : ℝ) < (M₀.card : ℝ))
    {e : ℤ} (he1 : 1 ≤ e) (hen : e ≤ (n : ℤ)) (hep : e % 2 = 0)
    (he : (e : ℝ) ≤ (n : ℝ) / 2) :
    (n : ℝ) / 20 - 3 / 2 ≤ ((diffReps M₀ e).card : ℝ) := by
  obtain ⟨h1, -⟩ := diffReps_sumReps_bounds_of_even hModd he1 hen hep
  have hM := le_of_lt hMbig
  linarith

/-- **Top-half evens are sum-blocked** — the explicit check that the
`e > n/2` regime feared thin in the removal-bypass notes is in fact
covered by sum representations alone: for even `e ∈ [n/2, n]` and
`|M₀| > 2n/5`, `|SR e| ≥ e/2 − n/5 − 2 ≥ n/20 − 2`. -/
theorem sumReps_ge_of_top_even {n : ℕ} {M₀ : Finset ℤ}
    (hModd : M₀ ⊆ odds n) (hMbig : (2 / 5 : ℝ) * (n : ℝ) < (M₀.card : ℝ))
    {e : ℤ} (he1 : 1 ≤ e) (hen : e ≤ (n : ℤ)) (hep : e % 2 = 0)
    (he : (n : ℝ) / 2 ≤ (e : ℝ)) :
    (n : ℝ) / 20 - 2 ≤ ((sumReps M₀ e).card : ℝ) := by
  obtain ⟨-, h2⟩ := diffReps_sumReps_bounds_of_even hModd he1 hen hep
  have hM := le_of_lt hMbig
  linarith

/-- **Standalone: representations give distinct Schur triples**
(reusable).  If `M₀ ⊆ C` consists of odd numbers and `E ⊆ C` consists of
even numbers, then the difference triples `(e, y, e + y)` with
`y ∈ diffReps M₀ e` and the sum triples `(x, e − x, e)` with
`x ∈ sumReps M₀ e` are pairwise disjoint Schur triples of `C`:
`∑_{e ∈ E} (|DR e| + |SR e|) ≤ schurTripleCount C`. -/
theorem schurTripleCount_ge_repSum {C M₀ E : Finset ℤ}
    (hMC : M₀ ⊆ C) (hModd : ∀ x ∈ M₀, x % 2 = 1)
    (hEC : E ⊆ C) (hEeven : ∀ e ∈ E, e % 2 = 0) :
    (∑ e ∈ E, ((diffReps M₀ e).card + (sumReps M₀ e).card)) ≤
      schurTripleCount C := by
  classical
  have hinj1 : Function.Injective
      (fun p : (Σ _ : ℤ, ℤ) => ((p.1, p.2, p.1 + p.2) : ℤ × ℤ × ℤ)) := by
    rintro ⟨a, b⟩ ⟨c, d⟩ h
    obtain rfl : a = c := congrArg Prod.fst h
    obtain rfl : b = d := congrArg (fun t : ℤ × ℤ × ℤ => t.2.1) h
    rfl
  have hinj2 : Function.Injective
      (fun p : (Σ _ : ℤ, ℤ) => ((p.2, p.1 - p.2, p.1) : ℤ × ℤ × ℤ)) := by
    rintro ⟨a, b⟩ ⟨c, d⟩ h
    obtain rfl : b = d := congrArg Prod.fst h
    obtain rfl : a = c := congrArg (fun t : ℤ × ℤ × ℤ => t.2.2) h
    rfl
  have himg1 : (E.sigma fun e => diffReps M₀ e).image
      (fun p : (Σ _ : ℤ, ℤ) => ((p.1, p.2, p.1 + p.2) : ℤ × ℤ × ℤ)) ⊆
      schurTriples C := by
    intro t ht
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨he, hy⟩ := Finset.mem_sigma.mp hp
    obtain ⟨hyM, hye⟩ := Finset.mem_filter.mp hy
    have hye' : p.1 + p.2 ∈ M₀ := by rwa [add_comm] at hye
    rw [schurTriples, Finset.mem_filter]
    simp only [Finset.mem_product]
    exact ⟨⟨hEC he, hMC hyM, hMC hye'⟩, trivial⟩
  have himg2 : (E.sigma fun e => sumReps M₀ e).image
      (fun p : (Σ _ : ℤ, ℤ) => ((p.2, p.1 - p.2, p.1) : ℤ × ℤ × ℤ)) ⊆
      schurTriples C := by
    intro t ht
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨he, hx⟩ := Finset.mem_sigma.mp hp
    obtain ⟨hxM, hxe⟩ := Finset.mem_filter.mp hx
    rw [schurTriples, Finset.mem_filter]
    simp only [Finset.mem_product]
    exact ⟨⟨hMC hxM, hMC hxe, hEC he⟩, by ring⟩
  have hdisj : Disjoint
      ((E.sigma fun e => diffReps M₀ e).image
        (fun p : (Σ _ : ℤ, ℤ) => ((p.1, p.2, p.1 + p.2) : ℤ × ℤ × ℤ)))
      ((E.sigma fun e => sumReps M₀ e).image
        (fun p : (Σ _ : ℤ, ℤ) => ((p.2, p.1 - p.2, p.1) : ℤ × ℤ × ℤ))) := by
    rw [Finset.disjoint_left]
    intro t ht1 ht2
    obtain ⟨p1, hp1, rfl⟩ := Finset.mem_image.mp ht1
    obtain ⟨p2, hp2, htp2⟩ := Finset.mem_image.mp ht2
    obtain ⟨he1, hy1⟩ := Finset.mem_sigma.mp hp1
    obtain ⟨he2, hx2⟩ := Finset.mem_sigma.mp hp2
    obtain ⟨hx2M, -⟩ := Finset.mem_filter.mp hx2
    have h1 : p1.1 % 2 = 0 := hEeven p1.1 he1
    have h2 : p2.2 % 2 = 1 := hModd p2.2 hx2M
    have h3 : p2.2 = p1.1 := congrArg Prod.fst htp2
    omega
  have hcard1 : ((E.sigma fun e => diffReps M₀ e).image
      (fun p : (Σ _ : ℤ, ℤ) =>
        ((p.1, p.2, p.1 + p.2) : ℤ × ℤ × ℤ))).card =
      ∑ e ∈ E, (diffReps M₀ e).card := by
    rw [Finset.card_image_of_injective _ hinj1, Finset.card_sigma]
  have hcard2 : ((E.sigma fun e => sumReps M₀ e).image
      (fun p : (Σ _ : ℤ, ℤ) =>
        ((p.2, p.1 - p.2, p.1) : ℤ × ℤ × ℤ))).card =
      ∑ e ∈ E, (sumReps M₀ e).card := by
    rw [Finset.card_image_of_injective _ hinj2, Finset.card_sigma]
  calc (∑ e ∈ E, ((diffReps M₀ e).card + (sumReps M₀ e).card))
      = (∑ e ∈ E, (diffReps M₀ e).card) + (∑ e ∈ E, (sumReps M₀ e).card) :=
        Finset.sum_add_distrib
    _ = ((E.sigma fun e => diffReps M₀ e).image
          (fun p : (Σ _ : ℤ, ℤ) =>
            ((p.1, p.2, p.1 + p.2) : ℤ × ℤ × ℤ))).card +
        ((E.sigma fun e => sumReps M₀ e).image
          (fun p : (Σ _ : ℤ, ℤ) =>
            ((p.2, p.1 - p.2, p.1) : ℤ × ℤ × ℤ))).card := by
        rw [hcard1, hcard2]
    _ = (((E.sigma fun e => diffReps M₀ e).image
            (fun p : (Σ _ : ℤ, ℤ) =>
              ((p.1, p.2, p.1 + p.2) : ℤ × ℤ × ℤ))) ∪
          ((E.sigma fun e => sumReps M₀ e).image
            (fun p : (Σ _ : ℤ, ℤ) =>
              ((p.2, p.1 - p.2, p.1) : ℤ × ℤ × ℤ)))).card :=
        (Finset.card_union_of_disjoint hdisj).symm
    _ ≤ (schurTriples C).card :=
        Finset.card_le_card (Finset.union_subset himg1 himg2)
    _ = schurTripleCount C := rfl

/-- **Amplification, size-hypothesis-free form.**  For `C ⊆ {1,…,n}`
housing *any* `M₀ ⊆ odds n` (no size hypothesis),
`|C ∖ odds n| · (4|M₀| − 3n/2 − 7/2) ≤ schurTripleCount C`.
The bound is informative exactly when `|M₀| > 3n/8 + O(1)`; below that it
is vacuous but still true. -/
theorem even_card_mul_le_of_odd_subset {n : ℕ} {C M₀ : Finset ℤ}
    (hCI : C ⊆ interval n) (hMC : M₀ ⊆ C) (hModd : M₀ ⊆ odds n) :
    ((C \ odds n).card : ℝ) *
        (4 * (M₀.card : ℝ) - 3 * (n : ℝ) / 2 - 7 / 2) ≤
      (schurTripleCount C : ℝ) := by
  classical
  set E : Finset ℤ := C \ odds n with hE
  have hE_mem : ∀ e ∈ E, 1 ≤ e ∧ e ≤ (n : ℤ) ∧ e % 2 = 0 := by
    intro e he
    rw [hE, Finset.mem_sdiff] at he
    obtain ⟨heC, heno⟩ := he
    have heI := Finset.mem_Icc.mp (hCI heC)
    have hmod : e % 2 = 0 := by
      rcases Int.emod_two_eq_zero_or_one e with h | h
      · exact h
      · exact absurd (mem_odds.mpr ⟨Finset.mem_Icc.mpr heI, h⟩) heno
    exact ⟨heI.1, heI.2, hmod⟩
  have hrep : ∀ e ∈ E,
      4 * (M₀.card : ℝ) - 3 * (n : ℝ) / 2 - 7 / 2 ≤
        ((diffReps M₀ e).card : ℝ) + ((sumReps M₀ e).card : ℝ) := by
    intro e he
    obtain ⟨he1, hen, hep⟩ := hE_mem e he
    exact repSum_ge_of_even hModd he1 hen hep
  have hsumr : (E.card : ℝ) *
      (4 * (M₀.card : ℝ) - 3 * (n : ℝ) / 2 - 7 / 2) ≤
      ∑ e ∈ E, (((diffReps M₀ e).card : ℝ) + ((sumReps M₀ e).card : ℝ)) := by
    have h := Finset.sum_le_sum (fun e he => hrep e he)
    rwa [Finset.sum_const, nsmul_eq_mul] at h
  have hnat : (∑ e ∈ E, ((diffReps M₀ e).card + (sumReps M₀ e).card)) ≤
      schurTripleCount C :=
    schurTripleCount_ge_repSum hMC
      (fun x hx => (mem_odds.mp (hModd hx)).2)
      (fun e he => (Finset.mem_sdiff.mp (hE ▸ he)).1)
      (fun e he => (hE_mem e he).2.2)
  have hstc : (∑ e ∈ E, (((diffReps M₀ e).card : ℝ) +
      ((sumReps M₀ e).card : ℝ))) ≤ (schurTripleCount C : ℝ) := by
    have h' : ((∑ e ∈ E,
        ((diffReps M₀ e).card + (sumReps M₀ e).card) : ℕ) : ℝ) ≤
        (schurTripleCount C : ℝ) := by
      exact_mod_cast hnat
    push_cast at h'
    exact h'
  exact hsumr.trans hstc

/-- **Graceful degradation.**  With a margin `γ` over the critical density
`3/8` — `|M₀| ≥ (3/8 + γ)·n` — the amplification gives
`|C ∖ odds n| · (4γn − 7/2) ≤ schurTripleCount C`. -/
theorem even_card_le_of_odd_subset_margin {n : ℕ} {C M₀ : Finset ℤ} {γ : ℝ}
    (hCI : C ⊆ interval n) (hMC : M₀ ⊆ C) (hModd : M₀ ⊆ odds n)
    (hMbig : (3 / 8 + γ) * (n : ℝ) ≤ (M₀.card : ℝ)) :
    ((C \ odds n).card : ℝ) * (4 * γ * (n : ℝ) - 7 / 2) ≤
      (schurTripleCount C : ℝ) := by
  have h := even_card_mul_le_of_odd_subset hCI hMC hModd
  have h4 : 4 * γ * (n : ℝ) - 7 / 2 ≤
      4 * (M₀.card : ℝ) - 3 * (n : ℝ) / 2 - 7 / 2 := by linarith
  calc ((C \ odds n).card : ℝ) * (4 * γ * (n : ℝ) - 7 / 2)
      ≤ ((C \ odds n).card : ℝ) *
          (4 * (M₀.card : ℝ) - 3 * (n : ℝ) / 2 - 7 / 2) :=
        mul_le_mul_of_nonneg_left h4 (Nat.cast_nonneg _)
    _ ≤ (schurTripleCount C : ℝ) := h

/-- **Graceful degradation, sparse form.**  For `δn²`-sparse `C` housing
`M₀ ⊆ odds n` with `|M₀| ≥ (3/8 + γ)n`, `γ > 0`:
`|C ∖ odds n| ≤ (δ/4γ)·n + 7/(8γ)`.  At `γ = 1/40` this recovers the
`|M₀| ≥ 2n/5` bound `|C ∖ odds n| ≤ 10δn + 35`. -/
theorem even_card_le_of_sparse_odd_margin {n : ℕ} {C M₀ : Finset ℤ}
    {δ γ : ℝ}
    (hCI : C ⊆ interval n) (hMC : M₀ ⊆ C) (hModd : M₀ ⊆ odds n)
    (hMbig : (3 / 8 + γ) * (n : ℝ) ≤ (M₀.card : ℝ))
    (hsp : (schurTripleCount C : ℝ) ≤ δ * (n : ℝ) ^ 2)
    (hγ : 0 < γ) (hn : (0 : ℝ) < (n : ℝ)) :
    ((C \ odds n).card : ℝ) ≤ δ / (4 * γ) * (n : ℝ) + 7 / (8 * γ) := by
  have h := even_card_le_of_odd_subset_margin hCI hMC hModd hMbig
  have hEle : ((C \ odds n).card : ℝ) ≤ (n : ℝ) := by
    have hsub : (C \ odds n).card ≤ (interval n).card :=
      Finset.card_le_card (Finset.sdiff_subset.trans hCI)
    rw [interval, Int.card_Icc] at hsub
    have hnn : ((n : ℤ) + 1 - 1).toNat = n := by simp
    rw [hnn] at hsub
    exact_mod_cast hsub
  -- `|E|·4γn ≤ δn² + (7/2)·|E| ≤ δn² + (7/2)·n`.
  have hE : ((C \ odds n).card : ℝ) * (4 * γ * (n : ℝ)) ≤
      δ * (n : ℝ) ^ 2 + 7 / 2 * (n : ℝ) := by
    have h1 : ((C \ odds n).card : ℝ) * (4 * γ * (n : ℝ)) ≤
        (schurTripleCount C : ℝ) +
          7 / 2 * ((C \ odds n).card : ℝ) := by
      calc ((C \ odds n).card : ℝ) * (4 * γ * (n : ℝ))
          = ((C \ odds n).card : ℝ) * (4 * γ * (n : ℝ) - 7 / 2) +
              7 / 2 * ((C \ odds n).card : ℝ) := by ring
        _ ≤ (schurTripleCount C : ℝ) +
              7 / 2 * ((C \ odds n).card : ℝ) := add_le_add h le_rfl
    exact h1.trans
      (add_le_add hsp (mul_le_mul_of_nonneg_left hEle (by positivity)))
  have hγn : (0 : ℝ) < 4 * γ * (n : ℝ) := by positivity
  have hbound : ((C \ odds n).card : ℝ) ≤
      (δ * (n : ℝ) ^ 2 + 7 / 2 * (n : ℝ)) / (4 * γ * (n : ℝ)) :=
    (le_div_iff₀ hγn).mpr hE
  refine hbound.trans (le_of_eq ?_)
  have hγ' : γ ≠ 0 := hγ.ne'
  have hn' : (n : ℝ) ≠ 0 := hn.ne'
  field_simp
  ring

/-- **Odd-dense form**: `M₀` need not be contained in `odds n`; only a
large odd part drives the amplification.  If `C ⊆ {1,…,n}` houses `M₀`
with `|M₀ ∩ odds n| ≥ (3/8 + γ)n`, then
`|C ∖ odds n| · (4γn − 7/2) ≤ schurTripleCount C`.  This covers maximal
sum-free `M₀` that are merely *odd-type* (large odd intersection) rather
than literally all-odd. -/
theorem even_card_le_of_odd_dense {n : ℕ} {C M₀ : Finset ℤ} {γ : ℝ}
    (hCI : C ⊆ interval n) (hMC : M₀ ⊆ C)
    (hMbig : (3 / 8 + γ) * (n : ℝ) ≤ ((M₀ ∩ odds n).card : ℝ)) :
    ((C \ odds n).card : ℝ) * (4 * γ * (n : ℝ) - 7 / 2) ≤
      (schurTripleCount C : ℝ) :=
  even_card_le_of_odd_subset_margin hCI
    (Finset.inter_subset_left.trans hMC) Finset.inter_subset_right hMbig

/-- Odd-dense sparse form: `|C ∖ odds n| ≤ (δ/4γ)·n + 7/(8γ)`. -/
theorem even_card_le_of_odd_dense_sparse {n : ℕ} {C M₀ : Finset ℤ}
    {δ γ : ℝ}
    (hCI : C ⊆ interval n) (hMC : M₀ ⊆ C)
    (hMbig : (3 / 8 + γ) * (n : ℝ) ≤ ((M₀ ∩ odds n).card : ℝ))
    (hsp : (schurTripleCount C : ℝ) ≤ δ * (n : ℝ) ^ 2)
    (hγ : 0 < γ) (hn : (0 : ℝ) < (n : ℝ)) :
    ((C \ odds n).card : ℝ) ≤ δ / (4 * γ) * (n : ℝ) + 7 / (8 * γ) :=
  even_card_le_of_sparse_odd_margin hCI
    (Finset.inter_subset_left.trans hMC) Finset.inter_subset_right hMbig
    hsp hγ hn

/-- Maximal-set form of the odd-dense bound (maximality is unused; the
hypothesis is kept for drop-in compatibility with the
`even_card_le_of_exists_large_odd_maximal` API). -/
theorem even_card_le_of_exists_odd_dense_maximal {n : ℕ} {C M₀ : Finset ℤ}
    {δ γ : ℝ}
    (hCI : C ⊆ interval n) (_hM : M₀ ∈ maxSumFreeSets n) (hMC : M₀ ⊆ C)
    (hMbig : (3 / 8 + γ) * (n : ℝ) ≤ ((M₀ ∩ odds n).card : ℝ))
    (hsp : (schurTripleCount C : ℝ) ≤ δ * (n : ℝ) ^ 2)
    (hγ : 0 < γ) (hn : (0 : ℝ) < (n : ℝ)) :
    ((C \ odds n).card : ℝ) ≤ δ / (4 * γ) * (n : ℝ) + 7 / (8 * γ) :=
  even_card_le_of_odd_dense_sparse hCI hMC hMbig hsp hγ hn

/-- **Explicit top-half bound** (the audit conclusion, as a checkable
statement): the even elements of `C` lying above `n/2` satisfy the same
`· n ≤ 10·schurTripleCount C + 40n` estimate as the whole of
`C ∖ odds n` — they are covered by the amplification directly, not merely
by a linear pair count. -/
theorem top_even_card_mul_le_of_large_odd {n : ℕ} {C M₀ : Finset ℤ}
    (hCI : C ⊆ interval n) (hMC : M₀ ⊆ C) (hModd : M₀ ⊆ odds n)
    (hMbig : (2 / 5 : ℝ) * (n : ℝ) < (M₀.card : ℝ)) :
    (((C \ odds n).filter fun e => (n : ℤ) / 2 < e).card : ℝ) * (n : ℝ) ≤
      10 * (schurTripleCount C : ℝ) + 40 * (n : ℝ) := by
  classical
  have hkey := even_card_mul_le_of_odd_subset hCI hMC hModd
  set E : Finset ℤ := C \ odds n with hE
  set Et : Finset ℤ := E.filter fun e => (n : ℤ) / 2 < e with hEt
  have hsub : (Et.card : ℝ) ≤ (E.card : ℝ) := by
    have h : Et.card ≤ E.card := hEt ▸ Finset.card_filter_le _ _
    exact_mod_cast h
  have hEn : (Et.card : ℝ) ≤ (n : ℝ) := by
    refine hsub.trans ?_
    have hsub' : E.card ≤ (interval n).card := hE ▸
      Finset.card_le_card (Finset.sdiff_subset.trans hCI)
    rw [interval, Int.card_Icc] at hsub'
    have hnn : ((n : ℤ) + 1 - 1).toNat = n := by simp
    rw [hnn] at hsub'
    exact_mod_cast hsub'
  -- `|Et|·m ≤ |E|·m ≤ T` for `m = 4|M₀| − 3n/2 − 7/2 ≥ 0`; if `m < 0`
  -- the claim `|Et|·m ≤ 0 ≤ T` is immediate anyway.
  have hstep : (Et.card : ℝ) * (4 * (M₀.card : ℝ) - 3 * (n : ℝ) / 2 - 7 / 2) ≤
      (schurTripleCount C : ℝ) := by
    rcases le_or_gt (0 : ℝ)
        (4 * (M₀.card : ℝ) - 3 * (n : ℝ) / 2 - 7 / 2) with hm | hm
    · exact (mul_le_mul_of_nonneg_right hsub hm).trans hkey
    · exact (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _)
        hm.le).trans (Nat.cast_nonneg _)
  have hmge : (n : ℝ) / 10 - 7 / 2 ≤
      4 * (M₀.card : ℝ) - 3 * (n : ℝ) / 2 - 7 / 2 := by
    have hM := le_of_lt hMbig
    linarith
  have h2 : (Et.card : ℝ) * ((n : ℝ) / 10 - 7 / 2) ≤
      (schurTripleCount C : ℝ) :=
    (mul_le_mul_of_nonneg_left hmge (Nat.cast_nonneg _)).trans hstep
  have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
  -- `|Et|·n = 10·|Et|·(n/10 − 7/2) + 35·|Et| ≤ 10T + 35n ≤ 10T + 40n`.
  calc (Et.card : ℝ) * (n : ℝ)
      = 10 * ((Et.card : ℝ) * ((n : ℝ) / 10 - 7 / 2)) +
          35 * (Et.card : ℝ) := by ring
    _ ≤ 10 * (schurTripleCount C : ℝ) + 35 * (Et.card : ℝ) :=
        add_le_add
          (mul_le_mul_of_nonneg_left h2 (by norm_num : (0 : ℝ) ≤ 10)) le_rfl
    _ ≤ 10 * (schurTripleCount C : ℝ) + 35 * (n : ℝ) :=
        add_le_add_right
          (mul_le_mul_of_nonneg_left hEn (by norm_num : (0 : ℝ) ≤ 35)) _
    _ ≤ 10 * (schurTripleCount C : ℝ) + 40 * (n : ℝ) :=
        add_le_add_right
          (mul_le_mul_of_nonneg_right (by norm_num : (35 : ℝ) ≤ 40) hnn) _

/-- **Assembled counting bound, relaxed hypothesis.**  For `ε, γ > 0`
there is `δ > 0` such that eventually every `δn²`-sparse
`C ⊆ {1,…,n}` housing a maximal sum-free `M₀` whose *odd part* satisfies
`|M₀ ∩ odds n| > (3/8 + γ)n` contains at most `2^{(1/4+ε)n}` maximal
sum-free sets of `{1,…,n}`.

This generalises `maxSumFreeSets_filter_card_le_of_large_odd` in two
directions: `M₀ ⊆ odds n` is replaced by a large odd intersection (`M₀`
itself may contain evens), and the threshold `2n/5` is relaxed to any
`(3/8 + γ)n` at the price of `δ = εγ`. -/
theorem maxSumFreeSets_filter_card_le_of_odd_dense {ε γ : ℝ}
    (hε : 0 < ε) (hγ : 0 < γ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n : ℕ in Filter.atTop,
      ∀ C M₀ : Finset ℤ, C ⊆ interval n → M₀ ∈ maxSumFreeSets n →
        M₀ ⊆ C → (3 / 8 + γ) * (n : ℝ) < ((M₀ ∩ odds n).card : ℝ) →
        (schurTripleCount C : ℝ) ≤ δ * (n : ℝ) ^ 2 →
        (((maxSumFreeSets n).filter (· ⊆ C)).card : ℝ) ≤
          (2 : ℝ) ^ ((1 / 4 + ε) * (n : ℝ)) := by
  have hε2 : 0 < ε / 2 := by linarith
  have hOCB := oddContainerBound (ε / 2) hε2
  refine ⟨ε * γ, by positivity, ?_⟩
  filter_upwards [hOCB, Filter.eventually_ge_atTop ⌈7 / (4 * γ)⌉₊,
    Filter.eventually_ge_atTop 1] with n hOCBn hn7 hn1
  intro C M₀ hCI hM hMC hMbig hsp
  have hnn : (0 : ℝ) < (n : ℝ) := by
    have : (1 : ℕ) ≤ n := hn1
    exact_mod_cast this
  -- `|C ∖ odds n| ≤ εn/2`: the amplification gives
  -- `|E|·(4γn − 7/2) ≤ δn²` and `4γn − 7/2 ≥ 2γn` for `n ≥ 7/(4γ)`.
  have hkey := even_card_le_of_odd_dense hCI hMC (le_of_lt hMbig)
  have h7 : (7 : ℝ) / (4 * γ) ≤ (n : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hn7)
  have hγn4 : 2 * γ * (n : ℝ) ≤ 4 * γ * (n : ℝ) - 7 / 2 := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 4 * γ)] at h7
    linarith [h7]
  have hEε : ((C \ odds n).card : ℝ) ≤ (ε / 2) * (n : ℝ) := by
    have hsp' : (schurTripleCount C : ℝ) ≤ (ε * γ) * (n : ℝ) ^ 2 := hsp
    have h1 : ((C \ odds n).card : ℝ) * (2 * γ * (n : ℝ)) ≤
        (ε * γ) * (n : ℝ) ^ 2 :=
      (mul_le_mul_of_nonneg_left hγn4 (Nat.cast_nonneg _)).trans
        (hkey.trans hsp')
    have hγn : (0 : ℝ) < 2 * γ * (n : ℝ) := by positivity
    have h2 : ((C \ odds n).card : ℝ) ≤
        (ε * γ * (n : ℝ) ^ 2) / (2 * γ * (n : ℝ)) :=
      (le_div_iff₀ hγn).mpr h1
    have h3 : (ε * γ * (n : ℝ) ^ 2) / (2 * γ * (n : ℝ)) =
        (ε / 2) * (n : ℝ) := by
      rw [div_eq_iff (by positivity : (2 : ℝ) * γ * (n : ℝ) ≠ 0)]
      ring
    rwa [h3] at h2
  -- housed maximal sets via the fingerprint decomposition `odds ∪ (C∖odds)`
  have hcover : C ⊆ odds n ∪ (C \ odds n) := by
    intro x hx
    rw [Finset.mem_union]
    by_cases hxo : x ∈ odds n
    · exact Or.inl hxo
    · exact Or.inr (Finset.mem_sdiff.mpr ⟨hx, hxo⟩)
  have hmono : ((maxSumFreeSets n).filter (· ⊆ C)).card ≤
      ((maxSumFreeSets n).filter (· ⊆ odds n ∪ (C \ odds n))).card := by
    apply Finset.card_le_card
    intro M hM'
    rw [Finset.mem_filter] at hM' ⊢
    exact ⟨hM'.1, hM'.2.trans hcover⟩
  have hb : ∀ S : Finset ℤ, S ⊆ C \ odds n → IsSumFree S →
      ((linkMaxSets S (odds n)).card : ℝ) ≤
        (2 : ℝ) ^ ((1 / 4 + ε / 2) * (n : ℝ)) := by
    intro S hS hSsf
    refine hOCBn S (hS.trans (Finset.sdiff_subset.trans hCI)) hSsf ?_
    intro x hx
    obtain ⟨hxC, hxno⟩ := Finset.mem_sdiff.mp (hS hx)
    have hxI := Finset.mem_Icc.mp (hCI hxC)
    by_contra hne
    exact hxno (mem_odds.mpr ⟨Finset.mem_Icc.mpr hxI, by omega⟩)
  have hbound := card_maxSumFreeSets_filter_union_le_two_pow_mul
    (A := odds n) (B := C \ odds n) (odds_subset_interval n)
    (isSumFree_odds n)
    (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _).le hb
  have hcardB : (2 : ℝ) ^ ((C \ odds n).card : ℝ) ≤
      (2 : ℝ) ^ ((ε / 2) * (n : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hEε
  calc (((maxSumFreeSets n).filter (· ⊆ C)).card : ℝ)
      ≤ (((maxSumFreeSets n).filter
          (· ⊆ odds n ∪ (C \ odds n))).card : ℝ) := by
        exact_mod_cast hmono
    _ ≤ (2 : ℝ) ^ ((C \ odds n).card : ℝ) *
          (2 : ℝ) ^ ((1 / 4 + ε / 2) * (n : ℝ)) := hbound
    _ ≤ (2 : ℝ) ^ ((ε / 2) * (n : ℝ)) *
          (2 : ℝ) ^ ((1 / 4 + ε / 2) * (n : ℝ)) := by
        exact mul_le_mul_of_nonneg_right hcardB
          (Real.rpow_nonneg (by norm_num) _)
    _ = (2 : ℝ) ^ ((ε / 2) * (n : ℝ) + (1 / 4 + ε / 2) * (n : ℝ)) := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    _ = (2 : ℝ) ^ ((1 / 4 + ε) * (n : ℝ)) := by
        congr 1
        ring

end JSP000728
