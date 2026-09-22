import JSPProblem.DFSTBridge

/-!
# JSP-000728 — classification of large sum-free subsets of `{1,…,n}`

The target is the *dense case* of the Deshouillers–Freiman–Sós–Temkin
trichotomy: a sum-free set `M ⊆ {1,…,n}` with `|M| > 2n/5 + 1` is either
all-odd (`M ⊆ odds n`) or interval-type (`M ⊆ Finset.Icc |M| n`, i.e.
`min M ≥ |M|`).

## The threshold

The bare `2n/5` threshold is **false**: `{4,7,9,10,12} ⊆ [1,12]` is
sum-free of size `5 > 2·12/5` but is mixed-parity with `min = 4 < 5`
(`sharpness_example`).  The correct hypothesis is `|M| > 2n/5 + 1`, which
we phrase integrally as `2·n + 5 < 5·|M|` (`card_threshold_iff` shows it
coincides with the `(2/5)·n + 1 < |M|` real form used by `dfst_range`).

## What is proved unconditionally (for every `n`, no `∀ᶠ`)

* `subset_Icc_card_of_three_mul_min` — the high-minimum regime: a large
  sum-free set with `3·min M ≥ n` is interval-type (repackaging of
  `card_le_min_of_two_fifths_lt` into the `Icc` form).
* `largeSumFree_cases` — **the unconditional trichotomy**: every large
  sum-free `M ⊆ {1,…,n}` is all-odd, interval-type, or `MixedLowMin`
  (mixed-parity with `3·min M < n`).  The third alternative is exactly
  the locus where the trichotomy requires Freiman's `3k − 4` theorem —
  the all-odd alternative is trivial, all-even sets are too small
  (`card_le_of_forall_even`), and `3·min M ≥ n` is the high-minimum
  regime above.
* `two_mul_card_sub_le_min_of_mixedLowMin` — in the residual class the
  translate bound gives `min M ≥ 2|M| − n`; elementary interval counting
  provably cannot improve this to `|M| ≤ 2n/5 + 1` (see `DFSTattack`).

## The residual hypothesis and the conditional theorem

* `LargeSumFreeResidual n` — the pointwise body of `DFSTMixed`: the DFST
  conclusion for mixed-parity low-minimum sets at `n`.
  `dfstMixed_iff_eventually_residual` : `DFSTMixed ↔ ∀ᶠ n, LargeSumFreeResidual n`.
* `largeSumFree_odd_or_interval` — the clean classification at `n`,
  unconditionally modulo `LargeSumFreeResidual n`.
* `largeSumFree_class_iff_residual` — the classification at `n` is
  *equivalent* to forcing interval-type in the residual class: the
  entire remaining content lives there.
* `largeSumFree_odd_or_interval_eventually_of_dfst` /
  `…_of_dfstMixed` / `largeSumFree_odd_or_interval_eventually` — the
  classification holds eventually under `DFST`, `DFSTMixed`, or Freiman's
  `3k − 4` hypothesis `Freiman3k4`.
* `dfstMixed_of_forall_classification` — conversely, the pointwise
  classification for all `n` implies `DFSTMixed`, so the target theorem
  for all `n` is equivalent to `∀ n, LargeSumFreeResidual n`.

This packages the same content as `dfst_range` in the `M ⊆ Icc |M| n`
form used by the removal-bypass counting, while recording precisely
which case is still open.
-/

namespace JSP000728

/-! ## The interval-type conclusion -/

/-- For `M ⊆ {1,…,n}`, containment in the top interval `Icc |M| n` is
equivalent to `|M|` being a lower bound for the elements of `M`. -/
theorem subset_Icc_card_iff {n : ℕ} {M : Finset ℤ} (hsub : M ⊆ interval n) :
    M ⊆ Finset.Icc (M.card : ℤ) (n : ℤ) ↔ ∀ x ∈ M, (M.card : ℤ) ≤ x := by
  refine ⟨fun h x hx => (Finset.mem_Icc.mp (h hx)).1, fun h x hx => ?_⟩
  exact Finset.mem_Icc.mpr ⟨h x hx, (Finset.mem_Icc.mp (hsub hx)).2⟩

/-- If `min M ≥ |M|` then `M` is interval-type. -/
theorem subset_Icc_card_of_min'_ge {n : ℕ} {M : Finset ℤ}
    (hsub : M ⊆ interval n) (hne : M.Nonempty)
    (hmin : (M.card : ℤ) ≤ M.min' hne) :
    M ⊆ Finset.Icc (M.card : ℤ) (n : ℤ) :=
  (subset_Icc_card_iff hsub).mpr fun x hx =>
    hmin.trans (Finset.min'_le M x hx)

/-- The integral form `2n + 5 < 5·|M|` of the largeness hypothesis is
equivalent to the real form `(2/5)·n + 1 < |M|` used in `dfst_range`. -/
theorem card_threshold_iff {n k : ℕ} :
    2 * (n : ℤ) + 5 < 5 * (k : ℤ) ↔
      (2 / 5 : ℝ) * (n : ℝ) + 1 < (k : ℝ) := by
  constructor
  · intro h
    have h' : (2 : ℝ) * (n : ℝ) + 5 < 5 * (k : ℝ) := by exact_mod_cast h
    linarith
  · intro h
    have hr : (2 : ℝ) * (n : ℝ) + 5 < 5 * (k : ℝ) := by linarith
    exact_mod_cast hr

/-! ## Sharpness of the `+1` slack -/

/-- **Sharpness example.**  `M = {4,7,9,10,12} ⊆ [1,12]` is sum-free of
size `5` with `2·12/5 = 4 < 5`, yet `M` is neither all-odd nor contained
in `Icc 5 12`.  Hence the bare threshold `|M| > 2n/5` does **not** imply
the dichotomy; the `+1` slack in `2n + 5 < 5·|M|` is necessary.
(The set sits in the `n = 3·min M` boundary case `12 = 3·4`.) -/
theorem sharpness_example :
    ({4, 7, 9, 10, 12} : Finset ℤ) ⊆ interval 12 ∧
    IsSumFree ({4, 7, 9, 10, 12} : Finset ℤ) ∧
    (2 * 12 / 5 : ℤ) < (({4, 7, 9, 10, 12} : Finset ℤ).card : ℤ) ∧
    ¬ ({4, 7, 9, 10, 12} : Finset ℤ) ⊆ odds 12 ∧
    ¬ ({4, 7, 9, 10, 12} : Finset ℤ) ⊆
      Finset.Icc (({4, 7, 9, 10, 12} : Finset ℤ).card : ℤ) 12 := by
  decide

/-! ## Unconditional regimes -/

/-- **High-minimum regime, unconditional.**  A large sum-free
`M ⊆ {1,…,n}` with `3·min M ≥ n` is interval-type.  This is
`card_le_min_of_two_fifths_lt` restated in `Icc` form. -/
theorem subset_Icc_card_of_three_mul_min {n : ℕ} {M : Finset ℤ}
    (hsub : M ⊆ interval n) (hsf : IsSumFree M) {m : ℤ}
    (hm : m ∈ M) (hmin : ∀ x ∈ M, m ≤ x) (h3m : (n : ℤ) ≤ 3 * m)
    (hbig : 2 * (n : ℤ) + 5 < 5 * (M.card : ℤ)) :
    M ⊆ Finset.Icc (M.card : ℤ) (n : ℤ) :=
  (subset_Icc_card_iff hsub).mpr
    (card_le_min_of_two_fifths_lt hsub hsf hm hmin h3m
      (card_threshold_iff.mp hbig))

/-- `min'`-form of the high-minimum regime. -/
theorem subset_Icc_card_of_three_mul_min' {n : ℕ} {M : Finset ℤ}
    (hsub : M ⊆ interval n) (hsf : IsSumFree M) (hne : M.Nonempty)
    (h3m : (n : ℤ) ≤ 3 * M.min' hne)
    (hbig : 2 * (n : ℤ) + 5 < 5 * (M.card : ℤ)) :
    M ⊆ Finset.Icc (M.card : ℤ) (n : ℤ) :=
  subset_Icc_card_of_three_mul_min hsub hsf (M.min'_mem hne)
    (fun x hx => Finset.min'_le M x hx) h3m hbig

/-- **The residual class.**  `M` is *mixed-parity low-minimum*: it
contains both an even and an odd element and its minimum is below `n/3`.
This is precisely the locus where the classification is equivalent to
the DFST trichotomy and requires Freiman's `3k − 4` theorem. -/
def MixedLowMin (n : ℕ) (M : Finset ℤ) : Prop :=
  (∃ e ∈ M, e % 2 = 0) ∧ (∃ o ∈ M, o % 2 = 1) ∧
    ∃ m ∈ M, (∀ x ∈ M, m ≤ x) ∧ 3 * m < (n : ℤ)

/-- **The unconditional trichotomy.**  Every sum-free `M ⊆ {1,…,n}` with
`|M| > 2n/5 + 1` is either all-odd, interval-type, or a mixed-parity
low-minimum set.  The third alternative is the residual case isolated
by `DFSTMixed`; it cannot be closed by elementary counting. -/
theorem largeSumFree_cases {n : ℕ} {M : Finset ℤ}
    (hsub : M ⊆ interval n) (hsf : IsSumFree M)
    (hbig : 2 * (n : ℤ) + 5 < 5 * (M.card : ℤ)) :
    M ⊆ odds n ∨ M ⊆ Finset.Icc (M.card : ℤ) (n : ℤ) ∨
      MixedLowMin n M := by
  classical
  have hbigR : (2 / 5 : ℝ) * (n : ℝ) + 1 < (M.card : ℝ) :=
    card_threshold_iff.mp hbig
  have hcardpos : 0 < M.card := by omega
  have hne : M.Nonempty := Finset.card_pos.mp hcardpos
  rcases em (∃ e ∈ M, e % 2 = 0) with hev | hnev
  · rcases em (∃ o ∈ M, o % 2 = 1) with hod | hnod
    · -- Mixed parity: either `3·min M ≥ n` (interval-type) or residual.
      obtain ⟨m, hmm, hmin⟩ : ∃ m ∈ M, ∀ x ∈ M, m ≤ x :=
        ⟨M.min' hne, M.min'_mem hne, fun x hx => Finset.min'_le M x hx⟩
      rcases le_or_gt (n : ℤ) (3 * m) with h3m | h3m
      · exact Or.inr (Or.inl
          (subset_Icc_card_of_three_mul_min hsub hsf hmm hmin h3m hbig))
      · exact Or.inr (Or.inr ⟨hev, hod, m, hmm, hmin, h3m⟩)
    · -- All elements even: `|M| ≤ 2n/5 + 1` by halving, contradiction.
      exfalso
      have hpar : ∀ x ∈ M, x % 2 = 0 := by
        intro x hx
        have h2 : x % 2 = 0 ∨ x % 2 = 1 := by omega
        rcases h2 with h | h
        · exact h
        · exact absurd ⟨x, hx, h⟩ hnod
      exact absurd (card_le_of_forall_even hsub hsf hpar)
        (not_le_of_gt hbigR)
  · -- No even element: every element is odd, so `M ⊆ odds n`.
    left
    intro x hx
    have hpar : x % 2 = 1 := by
      have h2 : x % 2 = 0 ∨ x % 2 = 1 := by omega
      rcases h2 with h | h
      · exact absurd ⟨x, hx, h⟩ hnev
      · exact h
    exact mem_odds.mpr ⟨hsub hx, hpar⟩

/-- A residual-class set satisfying the largeness hypothesis is a
*genuine* counterexample to the classification: `min M < n/3 < |M|`, so
`M` is neither interval-type nor (being mixed) all-odd.  Hence the whole
content of the classification theorem is the non-existence of such sets
— which is what Freiman's `3k − 4` theorem supplies. -/
theorem min'_lt_card_of_mixedLowMin {n : ℕ} {M : Finset ℤ}
    (hne : M.Nonempty) (hbig : 2 * (n : ℤ) + 5 < 5 * (M.card : ℤ))
    (h : MixedLowMin n M) : M.min' hne < (M.card : ℤ) := by
  obtain ⟨-, -, m, hmm, hmin, h3m⟩ := h
  have hm_eq : m = M.min' hne :=
    le_antisymm (hmin _ (M.min'_mem hne)) (Finset.min'_le M m hmm)
  rw [← hm_eq]
  omega

/-- The translate bound in the residual class: `min M ≥ 2·|M| − n`.
Together with `min M < n/3` this only gives `|M| < 2n/3`, far short of
`2n/5` — elementary counting alone cannot close the residual case. -/
theorem two_mul_card_sub_le_min_of_mixedLowMin {n : ℕ} {M : Finset ℤ}
    (hsub : M ⊆ interval n) (hsf : IsSumFree M) (hne : M.Nonempty)
    (_h : MixedLowMin n M) :
    2 * (M.card : ℤ) - (n : ℤ) ≤ M.min' hne := by
  have h2 := two_mul_card_le_of_min hsub hsf (M.min'_mem hne)
    (fun x hx => Finset.min'_le M x hx)
  have hminpos : (0 : ℤ) ≤ M.min' hne := by
    have h1 := (Finset.mem_Icc.mp (hsub (M.min'_mem hne))).1
    omega
  have hcast : (2 * M.card : ℤ) ≤ (n : ℤ) + ((M.min' hne).toNat : ℤ) := by
    exact_mod_cast h2
  rw [Int.toNat_of_nonneg hminpos] at hcast
  omega

/-- Non-mixed large sum-free sets are classified unconditionally. -/
theorem largeSumFree_odd_or_interval_of_not_mixed {n : ℕ} {M : Finset ℤ}
    (hsub : M ⊆ interval n) (hsf : IsSumFree M)
    (hbig : 2 * (n : ℤ) + 5 < 5 * (M.card : ℤ))
    (hnomix : ¬ ((∃ e ∈ M, e % 2 = 0) ∧ ∃ o ∈ M, o % 2 = 1)) :
    M ⊆ odds n ∨ M ⊆ Finset.Icc (M.card : ℤ) (n : ℤ) := by
  rcases largeSumFree_cases hsub hsf hbig with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd ⟨h.1, h.2.1⟩ hnomix

/-- High-minimum large sum-free sets are classified unconditionally. -/
theorem largeSumFree_odd_or_interval_of_high_min {n : ℕ} {M : Finset ℤ}
    (hsub : M ⊆ interval n) (hsf : IsSumFree M)
    (hbig : 2 * (n : ℤ) + 5 < 5 * (M.card : ℤ)) (hne : M.Nonempty)
    (h3m : (n : ℤ) ≤ 3 * M.min' hne) :
    M ⊆ odds n ∨ M ⊆ Finset.Icc (M.card : ℤ) (n : ℤ) :=
  Or.inr (subset_Icc_card_of_three_mul_min' hsub hsf hne h3m hbig)

/-! ## The residual hypothesis and the conditional classification -/

/-- **The residual hypothesis at `n`** — the DFST conclusion (small or
interval-type) for mixed-parity low-minimum sum-free sets.  This is the
pointwise body of `DFSTMixed`; it is the precise locus where the
classification needs Freiman's `3k − 4` theorem. -/
def LargeSumFreeResidual (n : ℕ) : Prop :=
  ∀ s : Finset ℤ, s ⊆ interval n → IsSumFree s →
    (∃ m ∈ s, (∀ x ∈ s, m ≤ x) ∧ 3 * m < (n : ℤ)) →
    (∃ e ∈ s, e % 2 = 0) → (∃ o ∈ s, o % 2 = 1) →
      (s.card : ℝ) ≤ (2 / 5 : ℝ) * (n : ℝ) + 1 ∨
        ∀ x ∈ s, (s.card : ℤ) ≤ x

/-- `DFSTMixed` is exactly the eventual form of `LargeSumFreeResidual`. -/
theorem dfstMixed_iff_eventually_residual :
    DFSTMixed ↔ ∀ᶠ n : ℕ in Filter.atTop, LargeSumFreeResidual n :=
  Iff.rfl

/-- **The classification theorem at `n`**, unconditionally modulo the
residual case: a large sum-free `M ⊆ {1,…,n}` is all-odd or
interval-type, provided no mixed-parity low-minimum set violates the
DFST bound. -/
theorem largeSumFree_odd_or_interval {n : ℕ} {M : Finset ℤ}
    (hsub : M ⊆ interval n) (hsf : IsSumFree M)
    (hbig : 2 * (n : ℤ) + 5 < 5 * (M.card : ℤ))
    (hres : LargeSumFreeResidual n) :
    M ⊆ odds n ∨ M ⊆ Finset.Icc (M.card : ℤ) (n : ℤ) := by
  rcases largeSumFree_cases hsub hsf hbig with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · obtain ⟨⟨e, he, hep⟩, ⟨o, ho, hop⟩, m, hmm, hmin, h3m⟩ := h
    rcases hres M hsub hsf ⟨m, hmm, hmin, h3m⟩ ⟨e, he, hep⟩ ⟨o, ho, hop⟩
      with hle | hge
    · exact absurd hle (not_le_of_gt (card_threshold_iff.mp hbig))
    · exact Or.inr ((subset_Icc_card_iff hsub).mpr hge)

/-- The classification theorem pointwise in `n`, given the residual
hypothesis at every `n`. -/
theorem largeSumFree_odd_or_interval_of_forall_residual
    (hres : ∀ n : ℕ, LargeSumFreeResidual n) {n : ℕ} {M : Finset ℤ}
    (hsub : M ⊆ interval n) (hsf : IsSumFree M)
    (hbig : 2 * (n : ℤ) + 5 < 5 * (M.card : ℤ)) :
    M ⊆ odds n ∨ M ⊆ Finset.Icc (M.card : ℤ) (n : ℤ) :=
  largeSumFree_odd_or_interval hsub hsf hbig (hres n)

/-- **Reduction to the residual class.**  The classification at `n` is
equivalent to: every large mixed-parity low-minimum sum-free set is
interval-type (its elements are all `≥ |M|`). -/
theorem largeSumFree_class_iff_residual {n : ℕ} :
    (∀ M : Finset ℤ, M ⊆ interval n → IsSumFree M →
      2 * (n : ℤ) + 5 < 5 * (M.card : ℤ) →
        M ⊆ odds n ∨ M ⊆ Finset.Icc (M.card : ℤ) (n : ℤ)) ↔
    ∀ M : Finset ℤ, M ⊆ interval n → IsSumFree M →
      2 * (n : ℤ) + 5 < 5 * (M.card : ℤ) → MixedLowMin n M →
        ∀ x ∈ M, (M.card : ℤ) ≤ x := by
  constructor
  · intro h M hsub hsf hbig hmix
    rcases h M hsub hsf hbig with hodds | hIcc
    · obtain ⟨e, heM, hep⟩ := hmix.1
      exfalso
      have h2 := (mem_odds.mp (hodds heM)).2
      omega
    · exact (subset_Icc_card_iff hsub).mp hIcc
  · intro h M hsub hsf hbig
    rcases largeSumFree_cases hsub hsf hbig with h1 | h2 | h3
    · exact Or.inl h1
    · exact Or.inr h2
    · exact Or.inr ((subset_Icc_card_iff hsub).mpr (h M hsub hsf hbig h3))

/-- The pointwise classification (at every `n`) implies `DFSTMixed`: a
residual set either satisfies the size bound or is interval-type.  Hence
the classification for all `n` is equivalent to the residual hypothesis
`∀ n, LargeSumFreeResidual n` — which is exactly the content that
`Freiman3k4` supplies (eventually). -/
theorem dfstMixed_of_forall_classification
    (h : ∀ n : ℕ, ∀ M : Finset ℤ, M ⊆ interval n → IsSumFree M →
      2 * (n : ℤ) + 5 < 5 * (M.card : ℤ) →
        M ⊆ odds n ∨ M ⊆ Finset.Icc (M.card : ℤ) (n : ℤ)) :
    DFSTMixed := by
  rw [dfstMixed_iff_eventually_residual]
  apply Filter.Eventually.of_forall
  intro n s hsub hsf hmin heven hodd
  rcases le_or_gt (s.card : ℝ) ((2 / 5 : ℝ) * (n : ℝ) + 1) with hle | hgt
  · exact Or.inl hle
  · right
    rcases h n s hsub hsf (card_threshold_iff.mpr hgt) with hodds | hIcc
    · obtain ⟨e, heM, hep⟩ := heven
      exfalso
      have h2 := (mem_odds.mp (hodds heM)).2
      omega
    · exact (subset_Icc_card_iff hsub).mp hIcc

/-- `Freiman3k4` discharges the residual hypothesis for all sufficiently
large `n` (via `dfstMixed_of_freiman3k4`). -/
theorem eventually_residual_of_freiman3k4 (hF : Freiman3k4) :
    ∀ᶠ n : ℕ in Filter.atTop, LargeSumFreeResidual n :=
  dfstMixed_iff_eventually_residual.mp (dfstMixed_of_freiman3k4 hF)

/-- The eventual classification under `DFSTMixed`. -/
theorem largeSumFree_odd_or_interval_eventually_of_dfstMixed (h : DFSTMixed) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ M : Finset ℤ, M ⊆ interval n →
      IsSumFree M → 2 * (n : ℤ) + 5 < 5 * (M.card : ℤ) →
        M ⊆ odds n ∨ M ⊆ Finset.Icc (M.card : ℤ) (n : ℤ) := by
  filter_upwards [dfstMixed_iff_eventually_residual.mp h]
    with n hn M hsub hsf hbig
  exact largeSumFree_odd_or_interval hsub hsf hbig hn

/-- The eventual classification under `DFST`. -/
theorem largeSumFree_odd_or_interval_eventually_of_dfst (h : DFST) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ M : Finset ℤ, M ⊆ interval n →
      IsSumFree M → 2 * (n : ℤ) + 5 < 5 * (M.card : ℤ) →
        M ⊆ odds n ∨ M ⊆ Finset.Icc (M.card : ℤ) (n : ℤ) :=
  largeSumFree_odd_or_interval_eventually_of_dfstMixed (dfstMixed_of_dfst h)

/-- **The classification theorem under Freiman's `3k − 4` hypothesis.**
For all sufficiently large `n`, every sum-free `M ⊆ {1,…,n}` with
`|M| > 2n/5 + 1` is all-odd or interval-type.  This is `dfst_range`
transported to the `M ⊆ Icc |M| n` form via `dfst_of_freiman3k4`. -/
theorem largeSumFree_odd_or_interval_eventually (hF : Freiman3k4) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ M : Finset ℤ, M ⊆ interval n →
      IsSumFree M → 2 * (n : ℤ) + 5 < 5 * (M.card : ℤ) →
        M ⊆ odds n ∨ M ⊆ Finset.Icc (M.card : ℤ) (n : ℤ) :=
  largeSumFree_odd_or_interval_eventually_of_dfstMixed
    (dfstMixed_of_freiman3k4 hF)

/-- Real-threshold variant of `largeSumFree_odd_or_interval_eventually`,
matching the `(2/5)·n + 1 < |M|` hypothesis of `dfst_range`. -/
theorem largeSumFree_odd_or_interval_eventually' (hF : Freiman3k4) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ M : Finset ℤ, M ⊆ interval n →
      IsSumFree M → (2 / 5 : ℝ) * (n : ℝ) + 1 < (M.card : ℝ) →
        M ⊆ odds n ∨ M ⊆ Finset.Icc (M.card : ℤ) (n : ℤ) := by
  filter_upwards [largeSumFree_odd_or_interval_eventually hF]
    with n hn M hsub hsf hbig
  exact hn M hsub hsf (card_threshold_iff.mpr hbig)

end JSP000728
