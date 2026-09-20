import JSPProblem.Removal
import JSPProblem.Supersat3
import JSPProblem.SparseCard

/-!
# JSP-000728 — attacks on the Schur removal lemma

This file collects what can currently be proved about `SchurRemoval`
(the arithmetic removal lemma hypothesised in `Removal.lean`):

* **Equivalence glue.** `AlmostSumFreeDecomp` rephrases removal as a
  *decomposition*: a sparse `C ⊆ {1,…,n}` splits as `C ⊆ A ∪ D` with `A`
  sum-free and `|D| ≤ ε·n`.  Both directions
  (`almostSumFreeDecomp_of_schurRemoval`, `schurRemoval_of_almostSumFreeDecomp`)
  are fully proved, as is the *linear* fragment
  (`almostSumFreeDecomp_linear`: `ε·n` triples ⇒ `ε·n` deletions).
* **Trivial special cases** (`almostSumFreeDecomp_of_odd_type`,
  `almostSumFreeDecomp_of_upper`): if `C` is already contained in the
  odds (or the upper half) up to `ε·n` exceptions, decomposition is
  immediate — no sparsity hypothesis needed.
* **The upper-half intermediate case** (`exists_decomp_of_dense_upper`,
  `almostSumFreeDecomp_of_dense_upper`): if `C ⊆ (n/4, n]` has at most
  `δ·n²` Schur triples and its upper half `(n/2, n]` misses at most
  `γ·n` points of the interval, then the low band `C ∩ (n/4, n/2]` has
  at most `ε·n` elements (provided `δ/ε + γ < ε`), so deleting it
  leaves the sum-free upper part.  This is the first nontrivial
  stability case: `L² ≤ #triples + L·|(n/2,n] ∖ C|` from
  `schurTripleCount_ge_of_low_dense` is a quadratic in `L` whose only
  bounded solution is `|L| = o(n)`.
* **The odds-membrane intermediate case** (`exists_decomp_of_dense_odds`,
  `almostSumFreeDecomp_of_dense_odds`): if `C ⊆ {1,…,n}` contains all
  but `γ·n` of the odd numbers and has at most `δ·n²` triples, then `C`
  contains at most `ε·n` *even* numbers (provided `δ + 2γ < ε²/2`), so
  deleting them leaves the sum-free odd part.  The key inequality is
  `schurTripleCount_ge_of_even_membrane`: the triple count dominates
  `∑_{e ∈ C ∩ evens} r_O(e)`, where `r_O(e)` counts ordered pairs of
  odd elements of `C` summing to `e`; each `r_O(e) ≥ e/2 − 2·|odds ∖ C|`,
  and distinct positive even `e`'s satisfy `∑ e/2 ≥ |E|(|E|+1)/2`.

Together with `removal_of_small_low_part` (Supersat3), these cover the
two extremal structures of the stability theorem — sets that are
"upper-half-like" and sets that are "odds-like" — *when the dense part
is already aligned with the extremal set*.  The full removal lemma
additionally has to *find* this alignment (the hard Green /
Ruzsa–Szemerédi step), which remains hypothesised as `SchurRemoval`.
-/

namespace JSP000728

/-! ## The decomposition form of removal -/

/-- **Almost-sum-free decomposition** (decomposition form of the removal
lemma): for every `ε > 0` there is `δ > 0` such that, eventually, every
`C ⊆ {1,…,n}` with at most `δ·n²` Schur triples splits as
`C ⊆ A ∪ D` with `A` sum-free and `|D| ≤ ε·n`. -/
def AlmostSumFreeDecomp : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n : ℕ in Filter.atTop,
    ∀ C : Finset ℤ, C ⊆ interval n →
      (schurTripleCount C : ℝ) ≤ δ * (n : ℝ) ^ 2 →
        ∃ A D : Finset ℤ, C ⊆ A ∪ D ∧ IsSumFree A ∧
          (D.card : ℝ) ≤ ε * (n : ℝ)

/-- **Removal ⇒ decomposition**: take `A := t`, `D := C ∖ t`. -/
theorem almostSumFreeDecomp_of_schurRemoval (hSR : SchurRemoval) :
    AlmostSumFreeDecomp := by
  intro ε hε
  obtain ⟨δ, hδ, hrem⟩ := hSR ε hε
  refine ⟨δ, hδ, ?_⟩
  filter_upwards [hrem] with n hremn C hC htri
  obtain ⟨t, htC, htf, hsd⟩ := hremn C hC htri
  refine ⟨t, C \ t, ?_, htf, hsd⟩
  rw [Finset.union_sdiff_of_subset htC]

/-- **Decomposition ⇒ removal**: take `t := C ∩ A`; then `C ∖ t ⊆ D`. -/
theorem schurRemoval_of_almostSumFreeDecomp (hD : AlmostSumFreeDecomp) :
    SchurRemoval := by
  intro ε hε
  obtain ⟨δ, hδ, hdec⟩ := hD ε hε
  refine ⟨δ, hδ, ?_⟩
  filter_upwards [hdec] with n hdecn s hs htr
  obtain ⟨A, D, hsAD, hsfA, hDcard⟩ := hdecn s hs htr
  refine ⟨s ∩ A, Finset.inter_subset_left,
    hsfA.mono Finset.inter_subset_right, ?_⟩
  have hsub : s \ (s ∩ A) ⊆ D := by
    intro x hx
    rw [Finset.mem_sdiff, Finset.mem_inter] at hx
    obtain ⟨hxs, hxA⟩ := hx
    have hxA' : x ∉ A := fun h => hxA ⟨hxs, h⟩
    rcases Finset.mem_union.mp (hsAD hxs) with h | h
    · exact absurd h hxA'
    · exact h
  calc ((s \ (s ∩ A)).card : ℝ)
      ≤ (D.card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
    _ ≤ ε * (n : ℝ) := hDcard

/-- **Linear fragment of the decomposition**: `≤ ε·n` triples are
removed by `≤ ε·n` deletions (the greedy bound
`exists_isSumFree_sub_card_le`).  This is the easy `δ n² → ε n`
degeneration when `δ n² ≤ ε n`, i.e. `δ ≤ ε / n`. -/
theorem almostSumFreeDecomp_linear {n : ℕ} {C : Finset ℤ} {ε : ℝ}
    (htri : (schurTripleCount C : ℝ) ≤ ε * (n : ℝ)) :
    ∃ A D : Finset ℤ, C ⊆ A ∪ D ∧ IsSumFree A ∧
      (D.card : ℝ) ≤ ε * (n : ℝ) := by
  obtain ⟨t, htC, htf, hdel⟩ := exists_isSumFree_sub_card_le C
  refine ⟨t, C \ t, ?_, htf, ?_⟩
  · rw [Finset.union_sdiff_of_subset htC]
  · calc ((C \ t).card : ℝ)
        ≤ (schurTripleCount C : ℝ) := by exact_mod_cast hdel
      _ ≤ ε * (n : ℝ) := htri

/-! ## Trivial special cases -/

/-- **Odd-type decomposition.**  If `C` is contained in `odds n` up to a
small exceptional set `D`, decomposition is immediate: `A := C ∩ odds n`
is sum-free and `D' := C ∖ odds n ⊆ D`.  No sparsity hypothesis needed. -/
theorem almostSumFreeDecomp_of_odd_type {n : ℕ} {C D : Finset ℤ} {ε : ℝ}
    (hsub : C ⊆ odds n ∪ D) (hD : (D.card : ℝ) ≤ ε * (n : ℝ)) :
    ∃ A D' : Finset ℤ, C ⊆ A ∪ D' ∧ IsSumFree A ∧
      (D'.card : ℝ) ≤ ε * (n : ℝ) := by
  classical
  refine ⟨C ∩ odds n, C \ odds n, ?_, ?_, ?_⟩
  · intro x hx
    rw [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    rcases em (x ∈ odds n) with h | h
    · exact Or.inl ⟨hx, h⟩
    · exact Or.inr ⟨hx, h⟩
  · exact (isSumFree_odds n).mono Finset.inter_subset_right
  · have hsubD : C \ odds n ⊆ D := by
      intro x hx
      rw [Finset.mem_sdiff] at hx
      rcases Finset.mem_union.mp (hsub hx.1) with h | h
      · exact absurd h hx.2
      · exact h
    calc ((C \ odds n).card : ℝ)
        ≤ (D.card : ℝ) := by exact_mod_cast Finset.card_le_card hsubD
      _ ≤ ε * (n : ℝ) := hD

/-- **Upper-half decomposition.**  If `C ⊆ {1,…,n}` is contained in
`(n/2, n]` up to a small exceptional set `D`, then `A := C ∩ (n/2, n]`
is sum-free and `D' := C ∩ [1, n/2] ⊆ D`. -/
theorem almostSumFreeDecomp_of_upper {n : ℕ} {C D : Finset ℤ} {ε : ℝ}
    (hC : C ⊆ interval n)
    (hsub : C ⊆ (Finset.Icc ((n : ℤ) / 2 + 1) (n : ℤ)) ∪ D)
    (hD : (D.card : ℝ) ≤ ε * (n : ℝ)) :
    ∃ A D' : Finset ℤ, C ⊆ A ∪ D' ∧ IsSumFree A ∧
      (D'.card : ℝ) ≤ ε * (n : ℝ) := by
  classical
  refine ⟨C.filter fun x => 2 * x > (n : ℤ),
    C.filter fun x => 2 * x ≤ (n : ℤ), ?_, isSumFree_filter_upper hC, ?_⟩
  · intro x hx
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    rcases em (2 * x ≤ (n : ℤ)) with h | h
    · exact Or.inr ⟨hx, h⟩
    · exact Or.inl ⟨hx, not_le.mp h⟩
  · have hsubD : C.filter (fun x => 2 * x ≤ (n : ℤ)) ⊆ D := by
      intro x hx
      rw [Finset.mem_filter] at hx
      rcases Finset.mem_union.mp (hsub hx.1) with h | h
      · rw [Finset.mem_Icc] at h; omega
      · exact h
    calc ((C.filter fun x => 2 * x ≤ (n : ℤ)).card : ℝ)
        ≤ (D.card : ℝ) := by exact_mod_cast Finset.card_le_card hsubD
      _ ≤ ε * (n : ℝ) := hD

/-! ## Intermediate case I: dense upper part, no small elements -/

/-- **Low band stays small.**  Let `C ⊆ {1,…,n}` have all its elements
in `(n/4, n]`, at most `δ·n²` Schur triples, and suppose the upper half
`(n/2, n]` misses at most `γ·n` points of the interval.  Then the low
part `|C ∩ [1, n/2]| ≤ ε·n` whenever `δ/ε + γ < ε`.

Proof: `L := C ∩ (n/4, n/2]` satisfies
`L² ≤ #triples + L·|(n/2,n] ∖ C|` (`schurTripleCount_ge_of_low_dense`);
if `|L| > ε·n` then `ε·n < δ·n²/L + γ·n ≤ (δ/ε + γ)·n`, contradicting
`δ/ε + γ < ε`. -/
theorem card_lowBand_le_of_dense_upper {n : ℕ} {C : Finset ℤ}
    (_hC : C ⊆ interval n)
    (hCmin : ∀ x ∈ C, (n : ℤ) / 4 < x)
    {ε γ δ : ℝ} (hε : 0 < ε) (hn : 0 < n)
    (hmiss : ((Finset.Icc ((n : ℤ) / 2 + 1) (n : ℤ) \ C).card : ℝ)
      ≤ γ * (n : ℝ))
    (htri : (schurTripleCount C : ℝ) ≤ δ * (n : ℝ) ^ 2)
    (hδγ : δ / ε + γ < ε) :
    ((C.filter fun x => 2 * x ≤ (n : ℤ)).card : ℝ) ≤ ε * (n : ℝ) := by
  classical
  set L := C.filter fun x => 2 * x ≤ (n : ℤ) with hL
  by_contra hlt
  rw [not_le] at hlt
  have hLIcc : L ⊆ Finset.Icc ((n : ℤ) / 4 + 1) ((n : ℤ) / 2) := by
    intro x hx
    rw [hL, Finset.mem_filter] at hx
    obtain ⟨hxC, hx2⟩ := hx
    have hxmin := hCmin x hxC
    rw [Finset.mem_Icc]
    omega
  have hLC : L ⊆ C := Finset.filter_subset _ _
  have hband := schurTripleCount_ge_of_low_dense hLC hLIcc
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hLR : (0 : ℝ) < (L.card : ℝ) := by
    have hpos : (0 : ℝ) < ε * (n : ℝ) := mul_pos hε hnR
    linarith [hlt]
  have hδnn : (0 : ℝ) ≤ δ * (n : ℝ) ^ 2 :=
    (Nat.cast_nonneg (schurTripleCount C)).trans htri
  have hδ : (0 : ℝ) ≤ δ :=
    nonneg_of_mul_nonneg_left hδnn (sq_pos_of_pos hnR)
  -- `L² ≤ δn² + L·γn` in ℝ.
  have hquad : (L.card : ℝ) ^ 2
      ≤ δ * (n : ℝ) ^ 2 + (L.card : ℝ) * (γ * (n : ℝ)) := by
    have h1 : ((L.card * L.card : ℕ) : ℝ)
        ≤ (schurTripleCount C : ℝ)
          + (L.card : ℝ)
            * ((Finset.Icc ((n : ℤ) / 2 + 1) (n : ℤ) \ C).card : ℝ) := by
      exact_mod_cast hband
    push_cast at h1
    have h2 : (L.card : ℝ)
        * ((Finset.Icc ((n : ℤ) / 2 + 1) (n : ℤ) \ C).card : ℝ)
        ≤ (L.card : ℝ) * (γ * (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hmiss (Nat.cast_nonneg _)
    linarith [h1, h2, htri]
  -- `εn·L < L² ≤ δn² + L·γn`; dividing by `L > 0` gives
  -- `εn < δn²/L + γn ≤ (δ/ε + γ)·n`.
  have h3 : ε * (n : ℝ) < (δ / ε + γ) * (n : ℝ) := by
    have h4 : (L.card : ℝ) * (ε * (n : ℝ))
        < δ * (n : ℝ) ^ 2 + (L.card : ℝ) * (γ * (n : ℝ)) := by
      calc (L.card : ℝ) * (ε * (n : ℝ))
          < (L.card : ℝ) * (L.card : ℝ) :=
            mul_lt_mul_of_pos_left hlt hLR
        _ = (L.card : ℝ) ^ 2 := (sq _).symm
        _ ≤ _ := hquad
    have h5 : ε * (n : ℝ)
        < δ * (n : ℝ) ^ 2 / (L.card : ℝ) + γ * (n : ℝ) := by
      have h6 : ε * (n : ℝ)
          < (δ * (n : ℝ) ^ 2 + (L.card : ℝ) * (γ * (n : ℝ)))
            / (L.card : ℝ) :=
        (lt_div_iff₀ hLR).mpr (by nlinarith [h4])
      rwa [add_div, mul_div_cancel_left₀ _ hLR.ne'] at h6
    have h7 : δ * (n : ℝ) ^ 2 / (L.card : ℝ)
        ≤ δ * (n : ℝ) ^ 2 / (ε * (n : ℝ)) := by
      apply div_le_div_of_nonneg_left hδnn (mul_pos hε hnR) hlt.le
    have h8 : δ * (n : ℝ) ^ 2 / (ε * (n : ℝ)) = (δ / ε) * (n : ℝ) := by
      field_simp
    linarith [h5, h7, h8]
  have h9 : ε < δ / ε + γ :=
    lt_of_mul_lt_mul_right h3 (Nat.cast_nonneg n)
  linarith [h9, hδγ]

/-- **Removal for the dense-upper shape.**  Under the same hypotheses,
`C = (C ∩ (n/2, n]) ∪ (C ∩ [1, n/2])` is the required decomposition:
the first part is sum-free and the second has `≤ ε·n` elements. -/
theorem exists_decomp_of_dense_upper {n : ℕ} {C : Finset ℤ}
    (hC : C ⊆ interval n)
    (hCmin : ∀ x ∈ C, (n : ℤ) / 4 < x)
    {ε γ δ : ℝ} (hε : 0 < ε) (hn : 0 < n)
    (hmiss : ((Finset.Icc ((n : ℤ) / 2 + 1) (n : ℤ) \ C).card : ℝ)
      ≤ γ * (n : ℝ))
    (htri : (schurTripleCount C : ℝ) ≤ δ * (n : ℝ) ^ 2)
    (hδγ : δ / ε + γ < ε) :
    ∃ A D : Finset ℤ, C ⊆ A ∪ D ∧ IsSumFree A ∧
      (D.card : ℝ) ≤ ε * (n : ℝ) := by
  classical
  refine ⟨C.filter fun x => 2 * x > (n : ℤ),
    C.filter fun x => 2 * x ≤ (n : ℤ), ?_, isSumFree_filter_upper hC,
    card_lowBand_le_of_dense_upper hC hCmin hε hn hmiss htri hδγ⟩
  -- (hC is passed through; only the band bound needs `n/4 < x`)
  intro x hx
  rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
  rcases em (2 * x ≤ (n : ℤ)) with h | h
  · exact Or.inr ⟨hx, h⟩
  · exact Or.inl ⟨hx, not_le.mp h⟩

/-- **Eventual form**: for every `ε > 0`, choosing `δ = ε²/4`,
`γ = ε/2`, the dense-upper shape is decomposable for all `n ≥ 1`. -/
theorem almostSumFreeDecomp_of_dense_upper :
    ∀ ε : ℝ, 0 < ε → ∃ δ γ : ℝ, 0 < δ ∧ 0 < γ ∧
      ∀ᶠ n : ℕ in Filter.atTop,
        ∀ C : Finset ℤ, C ⊆ interval n → (∀ x ∈ C, (n : ℤ) / 4 < x) →
          ((Finset.Icc ((n : ℤ) / 2 + 1) (n : ℤ) \ C).card : ℝ)
            ≤ γ * (n : ℝ) →
          (schurTripleCount C : ℝ) ≤ δ * (n : ℝ) ^ 2 →
          ∃ A D : Finset ℤ, C ⊆ A ∪ D ∧ IsSumFree A ∧
            (D.card : ℝ) ≤ ε * (n : ℝ) := by
  intro ε hε
  have hε0 : ε ≠ 0 := hε.ne'
  refine ⟨ε ^ 2 / 4, ε / 2, by positivity, by positivity, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn C hC hCmin hmiss htri
  apply exists_decomp_of_dense_upper hC hCmin hε hn hmiss htri
  have e : ε ^ 2 / 4 / ε + ε / 2 = 3 * ε / 4 := by field_simp; ring
  rw [e]; linarith

/-! ## Intermediate case II: the odds membrane -/

/-- **Even-membrane inequality.**  The Schur-triple count dominates the
number of ordered pairs of odd elements of `C` whose (even) sum also
lies in `C`:

  `schurTripleCount C ≥ ∑_{e ∈ C, e even} |{a ∈ C odd : e − a ∈ C}|`.

Each summand is a lower bound on the top-fiber over `e`, since the
odd `a`'s with `e − a ∈ C` inject into `{x ∈ C : e − x ∈ C}`. -/
theorem schurTripleCount_ge_of_even_membrane (C : Finset ℤ) :
    (∑ e ∈ C.filter (fun x => x % 2 = 0),
        ((C.filter fun x => x % 2 = 1).filter fun a => e - a ∈ C).card)
      ≤ schurTripleCount C := by
  classical
  calc (∑ e ∈ C.filter (fun x => x % 2 = 0),
        ((C.filter fun x => x % 2 = 1).filter fun a => e - a ∈ C).card)
      ≤ ∑ e ∈ C.filter (fun x => x % 2 = 0),
          (C.filter fun x => e - x ∈ C).card := by
        apply Finset.sum_le_sum
        intro e _
        apply Finset.card_le_card
        intro a ha
        rw [Finset.mem_filter] at ha ⊢
        exact ⟨Finset.mem_of_mem_filter a ha.1, ha.2⟩
    _ ≤ ∑ z ∈ C, (C.filter fun x => z - x ∈ C).card :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun z _ _ => Nat.zero_le _
    _ = schurTripleCount C := (schurTripleCount_eq_sum_filter C).symm

/-- **Odd-fiber lower bound at an even top.**  For an even `e ∈ C` the
odd part of the top-fiber has at least `e/2 − 2·|(odds n) ∖ C|`
elements: the full interval contributes `e/2` pairs `(a, e − a)` of odd
numbers (a bijection `j ↦ 2j − 1` on `[1, e/2]`), and each of the
`m := |odds n ∖ C|` missing odds destroys at most two of them
(once as `a`, once as `e − a`). -/
theorem odd_fiber_ge {n : ℕ} {C : Finset ℤ} (hC : C ⊆ interval n)
    {e : ℤ} (he : e ∈ C) (heven : e % 2 = 0) :
    e / 2 ≤ (((C.filter fun x => x % 2 = 1).filter
        fun a => e - a ∈ C).card : ℤ)
      + 2 * ((odds n \ C).card : ℤ) := by
  classical
  have he1 : 1 ≤ e := (Finset.mem_Icc.mp (hC he)).1
  have hen : e ≤ (n : ℤ) := (Finset.mem_Icc.mp (hC he)).2
  set M := odds n \ C with hM
  set S := (odds n).filter fun a => e - a ∈ odds n with hS
  set T := (C.filter fun x => x % 2 = 1).filter fun a => e - a ∈ C with hT
  -- `S` is the image of `[1, e/2]` under `j ↦ 2j − 1`, hence `|S| = e/2`.
  have hSeq : S = (Finset.Icc (1 : ℤ) (e / 2)).image fun j => 2 * j - 1 := by
    ext a
    rw [hS, Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨haO, heaO⟩
      obtain ⟨haI, haodd⟩ := mem_odds.mp haO
      obtain ⟨heaI, heaodd⟩ := mem_odds.mp heaO
      obtain ⟨ha1, han⟩ := Finset.mem_Icc.mp haI
      obtain ⟨hea1, hean⟩ := Finset.mem_Icc.mp heaI
      exact ⟨(a + 1) / 2, Finset.mem_Icc.mpr ⟨by omega, by omega⟩,
        by omega⟩
    · rintro ⟨j, hjI, rfl⟩
      obtain ⟨hj1, hje⟩ := Finset.mem_Icc.mp hjI
      exact ⟨mem_odds.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩,
          by omega⟩,
        mem_odds.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩,
          by omega⟩⟩
  have hScard : (S.card : ℤ) = e / 2 := by
    have hinj : Function.Injective fun j : ℤ => 2 * j - 1 := by
      intro a b h
      have h' : 2 * a - 1 = 2 * b - 1 := h
      omega
    rw [hSeq, Finset.card_image_of_injective _ hinj, Int.card_Icc]
    have h2 : e / 2 + 1 - 1 = e / 2 := by omega
    rw [h2, Int.toNat_of_nonneg (show (0 : ℤ) ≤ e / 2 by omega)]
  -- `S ⊆ T ∪ M ∪ (e − M)`, so `e/2 = |S| ≤ |T| + 2m`.
  have hcover : S ⊆ T ∪ (M ∪ M.image fun b => e - b) := by
    intro a ha
    rw [hS, Finset.mem_filter] at ha
    obtain ⟨haO, heaO⟩ := ha
    obtain ⟨haI, haodd⟩ := mem_odds.mp haO
    obtain ⟨heaI, heaodd⟩ := mem_odds.mp heaO
    rw [Finset.mem_union, Finset.mem_union]
    rcases em (a ∈ C) with haC | haC
    · rcases em (e - a ∈ C) with heaC | heaC
      · left
        rw [hT, Finset.mem_filter, Finset.mem_filter]
        exact ⟨⟨haC, haodd⟩, heaC⟩
      · right; right
        rw [Finset.mem_image]
        refine ⟨e - a, ?_, by show e - (e - a) = a; omega⟩
        rw [hM, Finset.mem_sdiff, mem_odds]
        exact ⟨⟨heaI, heaodd⟩, heaC⟩
    · right; left
      rw [hM, Finset.mem_sdiff, mem_odds]
      exact ⟨⟨haI, haodd⟩, haC⟩
  have hcard : S.card ≤ T.card + 2 * M.card := by
    have h1 := Finset.card_le_card hcover
    have h2 := Finset.card_union_le T (M ∪ M.image fun b => e - b)
    have h3 := Finset.card_union_le M (M.image fun b => e - b)
    have h4 := Finset.card_image_le (s := M) (f := fun b => e - b)
    omega
  have hcardZ : (S.card : ℤ) ≤ (T.card : ℤ) + 2 * (M.card : ℤ) := by
    exact_mod_cast hcard
  linarith [hScard, hcardZ]

/-- **Summed odd-fiber bound.**  Summing `e/2 ≤ r_O(e) + 2m` over the
even elements of `C`:
`∑_{e ∈ C ∩ evens} e/2 ≤ schurTripleCount C + 2·|odds n ∖ C|·|C ∩ evens|`. -/
theorem sum_even_fiber_ge {n : ℕ} {C : Finset ℤ} (hC : C ⊆ interval n) :
    (∑ e ∈ C.filter (fun x => x % 2 = 0), (e / 2 : ℤ))
      ≤ (schurTripleCount C : ℤ)
        + 2 * ((odds n \ C).card : ℤ)
          * (C.filter (fun x => x % 2 = 0)).card := by
  classical
  have hstep : ∀ e ∈ C.filter (fun x => x % 2 = 0),
      (e / 2 : ℤ) ≤ (((C.filter fun x => x % 2 = 1).filter
          fun a => e - a ∈ C).card : ℤ)
        + 2 * ((odds n \ C).card : ℤ) := by
    intro e he
    rw [Finset.mem_filter] at he
    have h := odd_fiber_ge hC he.1 he.2
    linarith [h]
  calc (∑ e ∈ C.filter (fun x => x % 2 = 0), (e / 2 : ℤ))
      ≤ ∑ e ∈ C.filter (fun x => x % 2 = 0),
          ((((C.filter fun x => x % 2 = 1).filter
              fun a => e - a ∈ C).card : ℤ)
            + 2 * ((odds n \ C).card : ℤ)) :=
        Finset.sum_le_sum hstep
    _ = (∑ e ∈ C.filter (fun x => x % 2 = 0),
          (((C.filter fun x => x % 2 = 1).filter
            fun a => e - a ∈ C).card : ℤ))
        + 2 * ((odds n \ C).card : ℤ)
          * (C.filter (fun x => x % 2 = 0)).card := by
        rw [Finset.sum_add_distrib]
        congr 1
        rw [Finset.sum_const, nsmul_eq_mul]
        ring
    _ ≤ (schurTripleCount C : ℤ)
        + 2 * ((odds n \ C).card : ℤ)
          * (C.filter (fun x => x % 2 = 0)).card := by
        have h := schurTripleCount_ge_of_even_membrane C
        have h' : (∑ e ∈ C.filter (fun x => x % 2 = 0),
            (((C.filter fun x => x % 2 = 1).filter
              fun a => e - a ∈ C).card : ℤ))
            ≤ (schurTripleCount C : ℤ) := by exact_mod_cast h
        linarith [h']

/-- **Distinct positive integers have quadratic sum.**  Any finset `X`
of integers all `≥ 1` satisfies `C(|X|,2) + |X| ≤ ∑ X`: for each
`x ∈ X`, `|{y ∈ X : y ≤ x}| ≤ x` (the fiber is a subset of `[1, x]`),
and `∑_{x} |{y ≤ x}|` counts the `C(|X|,2) + |X|` pairs
`(y, x) ∈ X²` with `y ≤ x`. -/
theorem choose_two_add_card_le_sum {X : Finset ℤ}
    (hX : ∀ x ∈ X, 1 ≤ x) :
    ((X.card.choose 2 + X.card : ℕ) : ℤ) ≤ ∑ x ∈ X, x := by
  classical
  have hle : ∀ x ∈ X, ((X.filter fun y => y ≤ x).card : ℤ) ≤ x := by
    intro x hx
    have hsub : X.filter (fun y => y ≤ x) ⊆ Finset.Icc 1 x := by
      intro y hy
      rw [Finset.mem_filter] at hy
      rw [Finset.mem_Icc]
      exact ⟨hX y hy.1, hy.2⟩
    have h := Finset.card_le_card hsub
    rw [Int.card_Icc] at h
    have hx1 : (1 : ℤ) ≤ x := hX x hx
    have h9 : ((X.filter fun y => y ≤ x).card : ℤ) ≤ x := by omega
    exact h9
  -- `∑_{x ∈ X} |{y ∈ X : y ≤ x}| = #{(y,x) ∈ X² : y ≤ x}`.
  have hsum : ((X ×ˢ X).filter fun p => p.1 ≤ p.2).card
      = ∑ x ∈ X, (X.filter fun y => y ≤ x).card := by
    rw [Finset.card_filter, Finset.sum_product_right]
    exact Finset.sum_congr rfl fun x _ => (Finset.card_filter _ X).symm
  -- `#{(y,x) : y ≤ x} = #{(y,x) : y < x} + #{(y,x) : y = x}
  --  = C(|X|,2) + |X|`.
  have hcount : ((X ×ˢ X).filter fun p => p.1 ≤ p.2).card
      = X.card.choose 2 + X.card := by
    have hsplit : (X ×ˢ X).filter (fun p => p.1 ≤ p.2)
        = (X ×ˢ X).filter (fun p => p.1 < p.2)
          ∪ (X ×ˢ X).filter (fun p => p.1 = p.2) := by
      rw [← Finset.filter_or]
      apply Finset.filter_congr
      intro p _
      exact le_iff_lt_or_eq
    have hdisj : Disjoint ((X ×ˢ X).filter fun p => p.1 < p.2)
        ((X ×ˢ X).filter fun p => p.1 = p.2) := by
      rw [Finset.disjoint_left]
      intro p hp1 hp2
      rw [Finset.mem_filter] at hp1 hp2
      omega
    have hlt : ((X ×ˢ X).filter fun p => p.1 < p.2).card
        = X.card.choose 2 := Finset.card_product_filter_lt
    have heq : ((X ×ˢ X).filter fun p => p.1 = p.2).card = X.card := by
      have e : (X ×ˢ X).filter (fun p => p.1 = p.2)
          = X.image fun x => (x, x) := by
        ext p
        rw [Finset.mem_filter, Finset.mem_product, Finset.mem_image]
        constructor
        · rintro ⟨⟨h1, h2⟩, h12⟩
          exact ⟨p.1, h1, Prod.ext rfl h12⟩
        · rintro ⟨x, hx, rfl⟩
          exact ⟨⟨hx, hx⟩, rfl⟩
      rw [e, Finset.card_image_of_injective _
        (fun a b h => (Prod.mk_inj.mp h).1)]
    rw [hsplit, Finset.card_union_of_disjoint hdisj, hlt, heq]
  have key : ((X.card.choose 2 + X.card : ℕ) : ℤ)
      = ∑ x ∈ X, ((X.filter fun y => y ≤ x).card : ℤ) := by
    rw [← hcount, hsum, Nat.cast_sum]
  rw [key]
  exact Finset.sum_le_sum hle

/-- **Halving a set of positive evens.**  For `E` a finset of even
integers `≥ 2`, `e ↦ e/2` is injective into `{1, 2, …}`, so
`∑_{e ∈ E} e/2 ≥ C(|E|,2) + |E| = |E|(|E|+1)/2`. -/
theorem sum_half_even_ge {E : Finset ℤ}
    (hE : ∀ e ∈ E, 2 ≤ e ∧ e % 2 = 0) :
    ((E.card.choose 2 + E.card : ℕ) : ℤ) ≤ ∑ e ∈ E, (e / 2 : ℤ) := by
  classical
  have hinj : Set.InjOn (fun e : ℤ => e / 2) ↑E := by
    intro a ha b hb hab
    obtain ⟨ha2, haeven⟩ := hE a ha
    obtain ⟨hb2, hbeven⟩ := hE b hb
    have h' : a / 2 = b / 2 := hab
    omega
  have hX : ∀ x ∈ E.image (fun e => e / 2), 1 ≤ x := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨e, heE, rfl⟩ := hx
    obtain ⟨h2, heven⟩ := hE e heE
    omega
  have hsum : ∑ x ∈ E.image (fun e => e / 2), x
      = ∑ e ∈ E, (e / 2 : ℤ) :=
    Finset.sum_image (s := E) (f := fun x : ℤ => x) hinj
  have hcard : (E.image fun e => e / 2).card = E.card :=
    Finset.card_image_of_injOn hinj
  have h := choose_two_add_card_le_sum hX
  rw [hcard] at h
  linarith [h, hsum]

/-- **Few evens near the odds.**  If `C ⊆ {1,…,n}` contains all but
`γ·n` of the odd numbers and has at most `δ·n²` Schur triples, then `C`
contains at most `ε·n` even numbers, provided `δ + 2γ < ε²/2`.

Proof: the `k` distinct positive even elements `e` of `C` each carry an
odd fiber of size `≥ e/2 − 2m` (`m = |odds n ∖ C|`), so
`k(k+1)/2 ≤ ∑ e/2 ≤ #triples + 2mk ≤ δn² + 2γn²`.  If `k > ε·n` this
forces `ε²/2 < δ + 2γ`. -/
theorem card_evens_le_of_dense_odds {n : ℕ} {C : Finset ℤ}
    (hC : C ⊆ interval n) {ε γ δ : ℝ} (hε : 0 < ε) (hn : 0 < n)
    (hm : ((odds n \ C).card : ℝ) ≤ γ * (n : ℝ))
    (htri : (schurTripleCount C : ℝ) ≤ δ * (n : ℝ) ^ 2)
    (hδγ : δ + 2 * γ < ε ^ 2 / 2) :
    ((C.filter fun x => x % 2 = 0).card : ℝ) ≤ ε * (n : ℝ) := by
  classical
  set E := C.filter fun x => x % 2 = 0 with hEdef
  by_contra hlt
  rw [not_le] at hlt
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hEven : ∀ e ∈ E, 2 ≤ e ∧ e % 2 = 0 := by
    intro e he
    rw [hEdef, Finset.mem_filter] at he
    have he1 : 1 ≤ e := (Finset.mem_Icc.mp (hC he.1)).1
    exact ⟨by omega, he.2⟩
  -- The integral inequality `C(k,2) + k ≤ #triples + 2mk`.
  have hZ : ((E.card.choose 2 + E.card : ℕ) : ℤ)
      ≤ (schurTripleCount C : ℤ)
        + 2 * ((odds n \ C).card : ℤ) * E.card := by
    have h1 := sum_half_even_ge hEven
    have h2 := sum_even_fiber_ge hC
    rw [← hEdef] at h2
    linarith [h1, h2]
  have hR : ((E.card.choose 2 + E.card : ℕ) : ℝ)
      ≤ (schurTripleCount C : ℝ)
        + 2 * ((odds n \ C).card : ℝ) * E.card := by
    exact_mod_cast hZ
  -- `C(k,2) + k = k(k+1)/2` in ℤ.
  have hk2 : (2 : ℤ) * ((E.card.choose 2 : ℤ) + E.card)
      = (E.card : ℤ) * (E.card + 1) := by
    have h2N : 2 * E.card.choose 2 = E.card * (E.card - 1) := by
      rw [Nat.choose_two_right, Nat.mul_comm 2,
        Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self _)]
    have h2 : (2 : ℤ) * (E.card.choose 2 : ℤ)
        = (E.card : ℤ) * ((E.card : ℤ) - 1) := by
      rcases Nat.eq_zero_or_pos E.card with h0 | h0
      · simp [h0]
      · have hc : ((2 * E.card.choose 2 : ℕ) : ℤ)
            = ((E.card * (E.card - 1) : ℕ) : ℤ) := by
          exact_mod_cast h2N
        rwa [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_mul,
          Nat.cast_sub h0, Nat.cast_one] at hc
    linarith [h2]
  have hhalf : ((E.card.choose 2 + E.card : ℕ) : ℝ)
      = (E.card : ℝ) * ((E.card : ℝ) + 1) / 2 := by
    have h := congrArg (fun z : ℤ => (z : ℝ)) hk2
    push_cast at h ⊢
    linarith [h]
  -- Upper bounds on the right side.
  have hkn : (E.card : ℝ) ≤ (n : ℝ) := by
    have hsub : E ⊆ interval n := (Finset.filter_subset _ _).trans hC
    have h := Finset.card_le_card hsub
    rw [card_interval] at h
    exact_mod_cast h
  have hm0 : (0 : ℝ) ≤ (odds n \ C).card := Nat.cast_nonneg _
  have hγn : (0 : ℝ) ≤ γ * (n : ℝ) := hm0.trans hm
  have hmk : 2 * ((odds n \ C).card : ℝ) * E.card
      ≤ 2 * (γ * (n : ℝ)) * (n : ℝ) := by
    have h1 : 2 * ((odds n \ C).card : ℝ) ≤ 2 * (γ * (n : ℝ)) := by
      linarith [hm]
    exact mul_le_mul h1 hkn (Nat.cast_nonneg _) (by linarith [hγn])
  -- Chain: `k(k+1)/2 > ε²n²/2`, so `ε²/2 < δ + 2γ`.
  have hbig : (ε * (n : ℝ)) ^ 2 / 2
      < (E.card : ℝ) * ((E.card : ℝ) + 1) / 2 := by
    have hk0 : (0 : ℝ) ≤ (E.card : ℝ) := Nat.cast_nonneg _
    have hsq : (ε * (n : ℝ)) ^ 2 < (E.card : ℝ) ^ 2 := by
      have h := mul_lt_mul hlt hlt.le (mul_pos hε hnR) hk0
      nlinarith [h]
    nlinarith [hsq, hk0]
  have hfin : ε ^ 2 / 2 < δ + 2 * γ := by
    have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 := sq_pos_of_pos hnR
    have hchain : (ε * (n : ℝ)) ^ 2 / 2 < δ * (n : ℝ) ^ 2
        + 2 * (γ * (n : ℝ)) * (n : ℝ) := by
      linarith [hbig, hR, hhalf, hmk, htri]
    have e1 : (ε * (n : ℝ)) ^ 2 / 2 = (ε ^ 2 / 2) * (n : ℝ) ^ 2 := by ring
    have e2 : δ * (n : ℝ) ^ 2 + 2 * (γ * (n : ℝ)) * (n : ℝ)
        = (δ + 2 * γ) * (n : ℝ) ^ 2 := by ring
    rw [e1, e2] at hchain
    exact lt_of_mul_lt_mul_right hchain hn2.le
  linarith [hfin, hδγ]

/-- **Removal for the dense-odds shape.**  Under the same hypotheses,
`C = (C ∩ odds n) ∪ (C ∩ evens)` is the required decomposition. -/
theorem exists_decomp_of_dense_odds {n : ℕ} {C : Finset ℤ}
    (hC : C ⊆ interval n) {ε γ δ : ℝ} (hε : 0 < ε) (hn : 0 < n)
    (hm : ((odds n \ C).card : ℝ) ≤ γ * (n : ℝ))
    (htri : (schurTripleCount C : ℝ) ≤ δ * (n : ℝ) ^ 2)
    (hδγ : δ + 2 * γ < ε ^ 2 / 2) :
    ∃ A D : Finset ℤ, C ⊆ A ∪ D ∧ IsSumFree A ∧
      (D.card : ℝ) ≤ ε * (n : ℝ) := by
  classical
  refine ⟨C.filter fun x => x % 2 = 1, C.filter fun x => x % 2 = 0,
    ?_, ?_, card_evens_le_of_dense_odds hC hε hn hm htri hδγ⟩
  · intro x hx
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    have hx1 : 1 ≤ x := (Finset.mem_Icc.mp (hC hx)).1
    rcases (show x % 2 = 0 ∨ x % 2 = 1 by omega) with h | h
    · exact Or.inr ⟨hx, h⟩
    · exact Or.inl ⟨hx, h⟩
  · apply (isSumFree_odds n).mono
    intro x hx
    rw [Finset.mem_filter] at hx
    exact mem_odds.mpr ⟨hC hx.1, hx.2⟩

/-- **Eventual form**: for every `ε > 0`, choosing `δ = γ = ε²/16`, the
dense-odds shape is decomposable for all `n ≥ 1`. -/
theorem almostSumFreeDecomp_of_dense_odds :
    ∀ ε : ℝ, 0 < ε → ∃ δ γ : ℝ, 0 < δ ∧ 0 < γ ∧
      ∀ᶠ n : ℕ in Filter.atTop,
        ∀ C : Finset ℤ, C ⊆ interval n →
          ((odds n \ C).card : ℝ) ≤ γ * (n : ℝ) →
          (schurTripleCount C : ℝ) ≤ δ * (n : ℝ) ^ 2 →
          ∃ A D : Finset ℤ, C ⊆ A ∪ D ∧ IsSumFree A ∧
            (D.card : ℝ) ≤ ε * (n : ℝ) := by
  intro ε hε
  refine ⟨ε ^ 2 / 16, ε ^ 2 / 16, by positivity, by positivity, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn C hC hm htri
  apply exists_decomp_of_dense_odds hC hε hn hm htri
  have h2 : 0 < ε ^ 2 := sq_pos_of_pos hε
  have e : ε ^ 2 / 16 + 2 * (ε ^ 2 / 16) = 3 * ε ^ 2 / 16 := by ring
  rw [e]; linarith

end JSP000728
