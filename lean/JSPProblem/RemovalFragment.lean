import JSPProblem.Supersat2
import Mathlib.Analysis.Real.Sqrt

/-!
# JSP-000728 — the linear (greedy) fragment of the Schur removal lemma

The *arithmetic removal lemma* (`SchurRemoval` in `Removal.lean`, the
Green / Ruzsa–Szemerédi content of the container argument) says that a
set `s ⊆ {1,…,n}` with at most `δ n²` Schur triples can be made sum-free
by deleting at most `ε n` elements, where `δ` may be chosen from `ε`
alone.  That statement is genuinely hard: it requires `o(n²)` triples to
be removable by `o(n)` deletions.

What is *easy* — and proved here unconditionally — is the **linear**
fragment: deleting one vertex of one Schur triple at a time (a greedy
descent on `schurTripleCount`) removes `|s ∖ t|` elements while
destroying at least `|s ∖ t|` triples, so one can always make `s`
sum-free by deleting at most `schurTripleCount s` elements:

* `exists_isSumFree_sub_card_le` — every `s : Finset ℤ` contains a
  sum-free `t` with `(s ∖ t).card ≤ schurTripleCount s`.
* `schurRemoval_linear` — the `ℝ`-valued corollary: `s ⊆ interval n`
  with `schurTripleCount s ≤ ε·n` admits a sum-free `t` with
  `(s ∖ t).card ≤ ε·n`.  **Caveat:** this only gives the removal
  conclusion when the triple count is *linear* in `n`; the real removal
  lemma needs `δ n² → ε n`, i.e. `o(n)` deletions for quadratically-few
  triples.

Packaged against the quadratic supersaturation bound of `Supersat2.lean`
(`schurTripleCount_quadratic`, `card_le_of_schurTripleCount_le`), solving
`3t² − (2n+1)t ≤ 2δn²` for the tight root (rather than relaxing `t ≤ n`
as in `card_le_of_schurTripleCount_le`) yields the sharp sparse bound

* `card_le_two_thirds_add_of_schurTripleCount_le` :
  `s.card ≤ (2n+1)/6 · (1 + √(1+6δ))`, which equals `(2n+1)/3` at `δ = 0`;
* `card_le_two_thirds_of_schurTripleCount_le` : the explicit
  `2/3 + O(√δ)` form
  `s.card ≤ (2/3)·n + (n + 1/2)·√(6δ)/3 + 1/3`,

matching the known supersaturation threshold: few Schur triples force
`|s| ≲ 2n/3 + O(√δ)·n`.
-/

namespace JSP000728

/-! ## Deletion decreases the Schur-triple count -/

/-- Schur triples are monotone in the ambient set. -/
theorem schurTriples_mono {s t : Finset ℤ} (h : s ⊆ t) :
    schurTriples s ⊆ schurTriples t := by
  intro x hx
  rw [schurTriples, Finset.mem_filter, Finset.mem_product,
    Finset.mem_product] at hx
  rw [schurTriples, Finset.mem_filter, Finset.mem_product,
    Finset.mem_product]
  exact ⟨⟨h hx.1.1, h hx.1.2.1, h hx.1.2.2⟩, hx.2⟩

/-- The Schur-triple count is monotone in the ambient set. -/
theorem schurTripleCount_mono {s t : Finset ℤ} (h : s ⊆ t) :
    schurTripleCount s ≤ schurTripleCount t :=
  Finset.card_le_card (schurTriples_mono h)

/-- Deleting the sum-coordinate `c` of a Schur triple `(a, b, c)` of `s`
strictly decreases the Schur-triple count: every triple of `s.erase c` is
a triple of `s` different from `(a, b, c)` (the latter requires
`c ∈ s.erase c`). -/
theorem schurTripleCount_erase_lt {s : Finset ℤ} {a b c : ℤ}
    (h : (a, b, c) ∈ schurTriples s) :
    schurTripleCount (s.erase c) < schurTripleCount s := by
  classical
  have hsub : schurTriples (s.erase c) ⊆ (schurTriples s).erase (a, b, c) := by
    intro x hx
    rw [Finset.mem_erase]
    refine ⟨?_, schurTriples_mono (Finset.erase_subset c s) hx⟩
    rintro rfl
    have hmem : (a, b, c) ∈ schurTriples (s.erase c) := hx
    rw [schurTriples, Finset.mem_filter, Finset.mem_product,
      Finset.mem_product] at hmem
    exact Finset.notMem_erase c s hmem.1.2.2
  have hpos : 0 < schurTripleCount s :=
    Finset.card_pos.mpr ⟨(a, b, c), h⟩
  calc schurTripleCount (s.erase c)
      ≤ ((schurTriples s).erase (a, b, c)).card := Finset.card_le_card hsub
    _ = schurTripleCount s - 1 := Finset.card_erase_of_mem h
    _ < schurTripleCount s := by omega

/-! ## The linear (greedy) removal fragment -/

/-- **Greedy removal.**  Every `s : Finset ℤ` contains a sum-free subset
`t` with `(s ∖ t).card ≤ schurTripleCount s`: delete the sum-coordinate
of one Schur triple, strictly decreasing the triple count, and recurse. -/
theorem exists_isSumFree_sub_card_le (s : Finset ℤ) :
    ∃ t : Finset ℤ, t ⊆ s ∧ IsSumFree t ∧
      (s \ t).card ≤ schurTripleCount s := by
  suffices H : ∀ k : ℕ, ∀ s : Finset ℤ, schurTripleCount s ≤ k →
      ∃ t : Finset ℤ, t ⊆ s ∧ IsSumFree t ∧
        (s \ t).card ≤ schurTripleCount s from
    H (schurTripleCount s) s le_rfl
  intro k
  induction k with
  | zero =>
    intro s h
    exact ⟨s, fun _ hx => hx,
      (schurTripleCount_eq_zero_iff s).mp (Nat.le_zero.mp h), by simp⟩
  | succ k ih =>
    intro s h
    rcases eq_or_ne (schurTripleCount s) 0 with h0 | h0
    · exact ⟨s, fun _ hx => hx,
        (schurTripleCount_eq_zero_iff s).mp h0, by simp⟩
    · classical
      obtain ⟨⟨a, b, c⟩, htri⟩ :=
        Finset.card_pos.mp (Nat.pos_of_ne_zero h0)
      have hlt : schurTripleCount (s.erase c) < schurTripleCount s :=
        schurTripleCount_erase_lt htri
      obtain ⟨t, hts, htf, hdel⟩ := ih (s.erase c) (by omega)
      refine ⟨t, hts.trans (Finset.erase_subset c s), htf, ?_⟩
      have hsplit : s \ t ⊆ insert c (s.erase c \ t) := by
        intro x hx
        rw [Finset.mem_sdiff] at hx
        rw [Finset.mem_insert]
        rcases eq_or_ne x c with rfl | hxc
        · exact Or.inl rfl
        · exact Or.inr (Finset.mem_sdiff.mpr
            ⟨Finset.mem_erase.mpr ⟨hxc, hx.1⟩, hx.2⟩)
      calc (s \ t).card
          ≤ (insert c (s.erase c \ t)).card := Finset.card_le_card hsplit
        _ ≤ (s.erase c \ t).card + 1 := Finset.card_insert_le _ _
        _ ≤ schurTripleCount s := by omega

/-- **Linear fragment of the Schur removal lemma.**  If `s ⊆ {1,…,n}`
has at most `ε·n` Schur triples, it contains a sum-free `t` obtained by
deleting at most `ε·n` elements.  This is only the *linear* fragment of
`SchurRemoval`: the genuine removal lemma deletes `ε n` elements when
there are `δ n²` triples (`δ ≪ ε` arbitrary), i.e. `o(n)` deletions for
`o(n²)` triples — that quadratic-to-linear amplification is the hard
Green / Ruzsa–Szemerédi content, kept as the `SchurRemoval` hypothesis
in `Removal.lean`. -/
theorem schurRemoval_linear {n : ℕ} {s : Finset ℤ}
    (_hsub : s ⊆ interval n) {ε : ℝ}
    (hε : (schurTripleCount s : ℝ) ≤ ε * (n : ℝ)) :
    ∃ t : Finset ℤ, t ⊆ s ∧ IsSumFree t ∧
      ((s \ t).card : ℝ) ≤ ε * (n : ℝ) := by
  obtain ⟨t, hts, htf, hdel⟩ := exists_isSumFree_sub_card_le s
  refine ⟨t, hts, htf, ?_⟩
  calc ((s \ t).card : ℝ)
      ≤ (schurTripleCount s : ℝ) := by exact_mod_cast hdel
    _ ≤ ε * (n : ℝ) := hε

/-! ## Sparse sets are at most `2/3 + O(√δ)` of the interval -/

/-- **Tight quadratic root.**  If `s ⊆ {1,…,n}` has at most `δ·n²` Schur
triples then `|s| ≤ (2n+1)/6 · (1 + √(1+6δ))`.  At `δ = 0` this recovers
the supersaturation threshold `|s| ≤ (2n+1)/3`; the slack
`card_le_of_schurTripleCount_le` (which relaxes `t ≤ n` before solving)
only gives `|s| ≤ n(1 + √(4+6δ))/3`, equal to `n` at `δ = 0`. -/
theorem card_le_two_thirds_add_of_schurTripleCount_le {n : ℕ}
    {s : Finset ℤ} {δ : ℝ} (hsub : s ⊆ interval n) (hδ : 0 ≤ δ)
    (htri : (schurTripleCount s : ℝ) ≤ δ * (n : ℝ) ^ 2) :
    (s.card : ℝ)
      ≤ (2 * (n : ℝ) + 1) / 6 * (1 + Real.sqrt (1 + 6 * δ)) := by
  have hmain : 3 * (s.card : ℝ) ^ 2
      ≤ 2 * (schurTripleCount s : ℝ) + 2 * s.card * n + s.card := by
    exact_mod_cast schurTripleCount_quadratic hsub
  have hNN : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
  have hr2 : Real.sqrt (1 + 6 * δ) ^ 2 = 1 + 6 * δ :=
    Real.sq_sqrt (by positivity)
  have hr0 : (0 : ℝ) ≤ Real.sqrt (1 + 6 * δ) := Real.sqrt_nonneg _
  -- `3t² − (2n+1)t ≤ 2δn²`.
  have hquad : 3 * (s.card : ℝ) ^ 2 - (2 * (n : ℝ) + 1) * (s.card : ℝ)
      ≤ 2 * δ * (n : ℝ) ^ 2 := by linarith [hmain, htri]
  -- `(6t − (2n+1))² ≤ ((2n+1)·√(1+6δ))²`, since
  -- `(6t−(2n+1))² = (2n+1)² + 12·(3t²−(2n+1)t)` and
  -- `(2n+1)²(1+6δ) − (2n+1)² − 24δn² = 6δ(4n+1) ≥ 0`.
  have hkey : 6 * (s.card : ℝ) - (2 * (n : ℝ) + 1)
      ≤ (2 * (n : ℝ) + 1) * Real.sqrt (1 + 6 * δ) := by
    apply le_of_sq_le_sq _ (mul_nonneg (by linarith) hr0)
    rw [mul_pow, hr2]
    nlinarith [hquad,
      mul_nonneg hδ (show (0 : ℝ) ≤ 4 * (n : ℝ) + 1 by linarith)]
  linarith [hkey]

/-- **`2/3 + O(√δ)` form.**  If `s ⊆ {1,…,n}` has at most `δ·n²` Schur
triples then `|s| ≤ (2/3)·n + (n + 1/2)·√(6δ)/3 + 1/3`, i.e.
`|s| ≲ 2n/3 + O(√δ·n)` for small `δ` — the supersaturation threshold. -/
theorem card_le_two_thirds_of_schurTripleCount_le {n : ℕ} {s : Finset ℤ}
    {δ : ℝ} (hsub : s ⊆ interval n) (hδ : 0 ≤ δ)
    (htri : (schurTripleCount s : ℝ) ≤ δ * (n : ℝ) ^ 2) :
    (s.card : ℝ) ≤ (2 / 3) * (n : ℝ)
      + ((n : ℝ) + 1 / 2) * Real.sqrt (6 * δ) / 3 + 1 / 3 := by
  have h := card_le_two_thirds_add_of_schurTripleCount_le hsub hδ htri
  -- `√(1+6δ) ≤ 1 + √(6δ)` by squaring.
  have hsqrt : Real.sqrt (1 + 6 * δ) ≤ 1 + Real.sqrt (6 * δ) := by
    apply le_of_sq_le_sq _ (by positivity)
    rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 1 + 6 * δ)]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 6 * δ by positivity),
      Real.sqrt_nonneg (6 * δ)]
  have hdiff : (0 : ℝ)
      ≤ 1 + Real.sqrt (6 * δ) - Real.sqrt (1 + 6 * δ) := by
    linarith [hsqrt]
  have hprod := mul_nonneg
    (show (0 : ℝ) ≤ 2 * (n : ℝ) + 1 by positivity) hdiff
  linarith [h, hprod]

end JSP000728
