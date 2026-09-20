import JSPProblem.Trichotomy
import JSPProblem.MinElement
import JSPProblem.MaxCard
import JSPProblem.EvenOdd

/-!
# JSP-000728 — attacking the DFST trichotomy

The hypothesis `DFST` (defined in `Trichotomy.lean`) is the
Deshouillers–Freiman–Sós–Temkin structure theorem: every sum-free
`s ⊆ {1,…,n}` satisfies (i) `|s| ≤ 2n/5 + 1`, or (ii) `s ⊆ odds n`, or
(iii) `min s ≥ |s|`.  Its proof uses Freiman-style inverse sumset analysis
and is genuinely hard.  This file attacks it and records precisely which
regime resists.

## What is proved unconditionally

* **High-minimum regime** (`min s ≥ n/3`).  Write `m = min s` and split
  `s = low ∪ high` at `n − m`.  The translate `low + m` is disjoint from
  `s` (Schur triples are forbidden) and, because `3m ≥ n`, it lands in the
  same top window `[n − m, n]` (resp. `[n − m + 1, n]` when `3m > n`) as
  `high`.  Counting gives `|s| ≤ m + 1`, and even `|s| ≤ m` when `3m > n`:
  - `card_le_min_add_one_of_le_three_mul_min` : `n ≤ 3m ⟹ |s| ≤ m + 1`;
  - `card_le_min_of_lt_three_mul_min` : `n < 3m ⟹ |s| ≤ m`;
  - `dfst_trichotomy_of_le_three_mul_min` : the DFST disjunction for
    `n ≤ 3m` (alternative (iii), or (i) at the boundary `n = 3m`);
  - `card_le_min_of_two_fifths_lt` : the weak trichotomy — `|s| > 2n/5 + 1`
    and `n ≤ 3·min s` force `min s ≥ |s|` — unconditionally.
  The bound `|s| ≤ m + 1` at `n = 3m` is sharp: `{4,7,9,10,12} ⊆ [1,12]`.

* **All-even sets.**  Halving is an injection of an all-even sum-free
  `s ⊆ {1,…,n}` onto a sum-free subset of `{1,…,⌊n/2⌋}`, so
  `|s| ≤ ⌊n/4⌋ + O(1) ≤ 2n/5 + 1` — alternative (i):
  `card_le_of_forall_even`.

* **Parity translates.**  If `e ∈ s` is even then `O + e` and `E + e`
  (the low parts of the odd/even sections of `s`, translated) sit inside
  `odds n`/`evens n` disjoint from `s`:
  `two_mul_card_odd_le_of_even_mem`, `two_mul_card_even_le_of_even_mem`.
  These give `2|O| ≤ ⌈n/2⌉ + e`, `2|E| ≤ ⌊n/2⌋ + e`; combined with
  `2|s| ≤ n + m` they are the full elementary input — and they provably
  never reach `2n/5` on their own, which is exactly where Freiman's
  inverse theory is needed.

* **Difference translate.**  `s.image (· − m)` is disjoint from `s` for
  `m ∈ s` (`disjoint_image_sub_of_isSumFree`).

## The residual hypothesis

The gap is isolated as two successively sharper named hypotheses:

* `DFSTLowMin` — the trichotomy for sets with `3·min s < n`;
* `DFSTMixed` — the trichotomy for *mixed-parity* sets (containing both
  an even and an odd element) with `3·min s < n`.

Reductions proved here: `DFSTMixed → DFSTLowMin → DFST`, and in fact
`DFST ↔ DFSTLowMin ↔ DFSTMixed` (`dfst_iff_dfstLowMin`,
`dfst_iff_dfstMixed`): **the entire content of DFST lives in the
mixed-parity low-minimum range**, which is precisely where the
Deshouillers–Freiman–Sós–Temkin argument needs Freiman's `3k − 4` theorem.

## Downstream interface

* `dfst_range` : `DFST → ∀ᶠ n, (s ⊆ interval n, sum-free, |s| > 2n/5 + 1)
  ⟹ s ⊆ odds n ∨ min s ≥ |s|` — the form used by `container_trichotomy`.
* `dfst_range_of_dfstLowMin` : the same conclusion from `DFSTLowMin`
  alone — the weak trichotomy never needs the all-odd branch's
  co-closure, only the residual range.
* `dfst_container_case` : `DFST` + `|s| ≥ (1/2 − γ)n` with `γ < 1/10`
  gives `s ⊆ odds n ∨ min s ≥ |s|` (the `9n/22`-scale application).
-/

namespace JSP000728

/-! ## Translate machinery -/

/-- **Difference translate.**  Translating a sum-free set *down* by one of
its own elements is disjoint from it: `x − m = y` with `x, y, m ∈ s` would
give the Schur triple `m + y = x`.  Companion to
`disjoint_image_add_min_of_isSumFree`. -/
theorem disjoint_image_sub_of_isSumFree {s : Finset ℤ} (hsf : IsSumFree s)
    {m : ℤ} (hm : m ∈ s) : Disjoint s (s.image (· - m)) := by
  rw [Finset.disjoint_left]
  rintro y hy hyim
  rcases Finset.mem_image.mp hyim with ⟨x, hx, hxy⟩
  have hsum : m + y ∈ s := by
    have h : m + y = x := by omega
    rw [h]
    exact hx
  exact hsf m hm y hy hsum

/-- The trivial bound: `s ⊆ Icc m n` gives `|s| ≤ n − m + 1`.  Stated for
`m ∈ s` so that `m ≤ n` is automatic. -/
theorem card_le_of_mem_min_le {n : ℕ} {s : Finset ℤ} (hsub : s ⊆ interval n)
    {m : ℤ} (hm : m ∈ s) (hmin : ∀ x ∈ s, m ≤ x) :
    (s.card : ℤ) ≤ n - m + 1 := by
  have hmI := Finset.mem_Icc.mp (hsub hm)
  have hss : s ⊆ Finset.Icc m (n : ℤ) := by
    intro x hx
    exact Finset.mem_Icc.mpr ⟨hmin x hx, (Finset.mem_Icc.mp (hsub hx)).2⟩
  have h := Finset.card_le_card hss
  rw [Int.card_Icc] at h
  have hnn : (0 : ℤ) ≤ n + 1 - m := by omega
  have h' : (s.card : ℤ) ≤ ((n + 1 - m).toNat : ℤ) := by exact_mod_cast h
  rw [Int.toNat_of_nonneg hnn] at h'
  linarith

/-! ## The high-minimum regime: `n ≤ 3·min s`

Split `s` at `n − m` into `low` and `high`.  The translate `low + m` is
disjoint from `s` and, when `3m` is large compared to `n`, lands in the
same top window as `high`; counting in that window bounds `|s|`. -/

/-- **Counting core of the high-minimum regime.**  If every element of the
low part `s ∩ [1, n − m]` translates into `[L, n]` under `· + m`, and the
high part `s ∩ (n − m, n]` already lies in `[L, n]`, then
`|s| ≤ n + 1 − L`: `low + m` and `high` are disjoint subsets of `Icc L n`. -/
private theorem card_le_of_translate {n : ℕ} {s : Finset ℤ}
    (hsub : s ⊆ interval n) (hsf : IsSumFree s) {m : ℤ}
    (hm : m ∈ s) (_hmin : ∀ x ∈ s, m ≤ x) {L : ℤ} (hLn : L ≤ (n : ℤ) + 1)
    (hLlow : ∀ x ∈ s, x ≤ (n : ℤ) - m → L ≤ x + m)
    (hLhigh : ∀ x ∈ s, ¬ x ≤ (n : ℤ) - m → L ≤ x) :
    (s.card : ℤ) ≤ n + 1 - L := by
  classical
  set low : Finset ℤ := s.filter (· ≤ (n : ℤ) - m) with hlowdef
  set high : Finset ℤ := s.filter (¬ · ≤ (n : ℤ) - m) with hhighdef
  have hlowsub : low.image (· + m) ⊆ Finset.Icc L (n : ℤ) := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨x, hxt, rfl⟩
    obtain ⟨hxs, hxle⟩ := Finset.mem_filter.mp hxt
    exact Finset.mem_Icc.mpr ⟨hLlow x hxs hxle, by omega⟩
  have hhighsub : high ⊆ Finset.Icc L (n : ℤ) := by
    intro x hx
    obtain ⟨hxs, hxle⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_Icc.mpr ⟨hLhigh x hxs hxle,
      (Finset.mem_Icc.mp (hsub hxs)).2⟩
  have hdisj : Disjoint (low.image (· + m)) high :=
    Disjoint.mono (Finset.image_subset_image (Finset.filter_subset _ _))
      (Finset.filter_subset _ _)
      (disjoint_image_add_min_of_isSumFree hsf hm).symm
  have hcard : (low.image (· + m)).card = low.card :=
    Finset.card_image_of_injective _ (add_left_injective m)
  have hsplit : low.card + high.card = s.card :=
    Finset.card_filter_add_card_filter_not _
  have hbound : (low.image (· + m) ∪ high).card ≤
      (Finset.Icc L (n : ℤ)).card :=
    Finset.card_le_card (Finset.union_subset hlowsub hhighsub)
  rw [Finset.card_union_of_disjoint hdisj, hcard, hsplit, Int.card_Icc]
    at hbound
  have hnn : (0 : ℤ) ≤ n + 1 - L := by omega
  have h' : (s.card : ℤ) ≤ ((n + 1 - L).toNat : ℤ) := by exact_mod_cast hbound
  rw [Int.toNat_of_nonneg hnn] at h'
  exact h'

/-- **Boundary case `n = 3m`.**  A sum-free `s ⊆ {1,…,n}` with minimum
`m` and `n ≤ 3m` satisfies `|s| ≤ m + 1`: `low + m` and `high` are
disjoint subsets of `Icc (n − m) n`, which has `m + 1` elements.
Sharp: `{4, 7, 9, 10, 12} ⊆ [1, 12]` has `|s| = m + 1 = 5`. -/
theorem card_le_min_add_one_of_le_three_mul_min {n : ℕ} {s : Finset ℤ}
    (hsub : s ⊆ interval n) (hsf : IsSumFree s) {m : ℤ}
    (hm : m ∈ s) (hmin : ∀ x ∈ s, m ≤ x) (h3m : (n : ℤ) ≤ 3 * m) :
    (s.card : ℤ) ≤ m + 1 := by
  have hm1 : 1 ≤ m := (Finset.mem_Icc.mp (hsub hm)).1
  have h := card_le_of_translate hsub hsf hm hmin (L := (n : ℤ) - m)
    (by omega)
    (fun x hxs _ => by have hxm := hmin x hxs; omega)
    (fun _ _ h => by omega)
  omega

/-- **High-minimum regime.**  A sum-free `s ⊆ {1,…,n}` with minimum `m`
and `n < 3m` (i.e. `n + 1 ≤ 3m`) satisfies `|s| ≤ m`: `low + m` and `high`
are disjoint subsets of `Icc (n − m + 1) n`, which has `m` elements. -/
theorem card_le_min_of_lt_three_mul_min {n : ℕ} {s : Finset ℤ}
    (hsub : s ⊆ interval n) (hsf : IsSumFree s) {m : ℤ}
    (hm : m ∈ s) (hmin : ∀ x ∈ s, m ≤ x) (h3m : (n : ℤ) < 3 * m) :
    (s.card : ℤ) ≤ m := by
  have hm1 : 1 ≤ m := (Finset.mem_Icc.mp (hsub hm)).1
  have h := card_le_of_translate hsub hsf hm hmin (L := (n : ℤ) - m + 1)
    (by omega)
    (fun x hxs _ => by have hxm := hmin x hxs; omega)
    (fun _ _ h => by omega)
  omega

/-- `min'`-form of the high-minimum bound: a nonempty sum-free
`s ⊆ {1,…,n}` with `s.min' > n/3` satisfies `|s| ≤ min s`. -/
theorem card_le_min'_of_lt_three_mul_min' {n : ℕ} {s : Finset ℤ}
    (hsub : s ⊆ interval n) (hsf : IsSumFree s) (hne : s.Nonempty)
    (h3m : (n : ℤ) < 3 * s.min' hne) :
    (s.card : ℤ) ≤ s.min' hne :=
  card_le_min_of_lt_three_mul_min hsub hsf (s.min'_mem hne)
    (fun x hx => Finset.min'_le s x hx) h3m

/-- **DFST trichotomy in the high-minimum range** — unconditional.  If
`s ⊆ {1,…,n}` is sum-free with minimum `m` and `n ≤ 3m`, then either
`|s| ≤ 2n/5 + 1` (the boundary case `n = 3m`, where `|s| ≤ m + 1 = n/3 + 1`)
or `min s ≥ |s|` (when `n < 3m`, where `|s| ≤ m`). -/
theorem dfst_trichotomy_of_le_three_mul_min {n : ℕ} {s : Finset ℤ}
    (hsub : s ⊆ interval n) (hsf : IsSumFree s) {m : ℤ}
    (hm : m ∈ s) (hmin : ∀ x ∈ s, m ≤ x) (h3m : (n : ℤ) ≤ 3 * m) :
    (s.card : ℝ) ≤ (2 / 5 : ℝ) * (n : ℝ) + 1 ∨
      ∀ x ∈ s, (s.card : ℤ) ≤ x := by
  have hm1 : (1 : ℤ) ≤ m := (Finset.mem_Icc.mp (hsub hm)).1
  rcases lt_or_eq_of_le h3m with hlt | heq
  · -- `n < 3m`: `|s| ≤ m`, so every `x ∈ s` has `x ≥ m ≥ |s|`.
    refine Or.inr fun x hx => ?_
    exact (card_le_min_of_lt_three_mul_min hsub hsf hm hmin hlt).trans
      (hmin x hx)
  · -- `n = 3m`: `|s| ≤ m + 1 = n/3 + 1 ≤ 2n/5 + 1`.
    refine Or.inl ?_
    have h1 := card_le_min_add_one_of_le_three_mul_min hsub hsf hm hmin h3m
    have hcard : (s.card : ℝ) ≤ (m : ℝ) + 1 := by exact_mod_cast h1
    have hn : (n : ℝ) = 3 * (m : ℝ) := by exact_mod_cast heq
    have hm1' : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
    linarith

/-- **Weak trichotomy in the high-minimum range** — unconditional.  A
sum-free `s ⊆ {1,…,n}` with `|s| > 2n/5 + 1` and `n ≤ 3·min s` satisfies
`min s ≥ |s|`.  (The boundary `n = 3·min s` is incompatible with
`|s| > 2n/5 + 1`.) -/
theorem card_le_min_of_two_fifths_lt {n : ℕ} {s : Finset ℤ}
    (hsub : s ⊆ interval n) (hsf : IsSumFree s) {m : ℤ}
    (hm : m ∈ s) (hmin : ∀ x ∈ s, m ≤ x) (h3m : (n : ℤ) ≤ 3 * m)
    (hbig : (2 / 5 : ℝ) * (n : ℝ) + 1 < (s.card : ℝ)) :
    ∀ x ∈ s, (s.card : ℤ) ≤ x := by
  rcases lt_or_eq_of_le h3m with hlt | heq
  · exact fun x hx =>
      (card_le_min_of_lt_three_mul_min hsub hsf hm hmin hlt).trans
        (hmin x hx)
  · exfalso
    have h1 := card_le_min_add_one_of_le_three_mul_min hsub hsf hm hmin h3m
    have hm1 : (1 : ℤ) ≤ m := (Finset.mem_Icc.mp (hsub hm)).1
    have hcard : (s.card : ℝ) ≤ (m : ℝ) + 1 := by exact_mod_cast h1
    have hn : (n : ℝ) = 3 * (m : ℝ) := by exact_mod_cast heq
    have hm1' : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
    linarith

/-! ## Parity translates

If `e ∈ s` is even then `x ↦ x + e` preserves the parity of `x` and moves
`s` off itself; restricting to `x ≤ n − e` keeps the image inside
`{1,…,n}`.  Hence the odd part `O` and its low translate sit disjointly
inside `odds n`, and likewise for the even part inside `evens n`. -/

/-- The even numbers in `{1, …, n}`. -/
def evens (n : ℕ) : Finset ℤ := (interval n).filter fun x => x % 2 = 0

theorem mem_evens {n : ℕ} {x : ℤ} :
    x ∈ evens n ↔ x ∈ interval n ∧ x % 2 = 0 :=
  Finset.mem_filter

/-- The map `k ↦ 2k` is a bijection between `{1, …, n/2}` and the even
numbers of `{1, …, n}`, so `(evens n).card = n / 2`. -/
theorem card_evens (n : ℕ) : (evens n).card = n / 2 := by
  have himg : evens n = (Finset.Icc 1 ((n / 2 : ℕ) : ℤ)).image (2 * ·) := by
    ext x
    constructor
    · intro hx
      obtain ⟨hxI, hpar⟩ := Finset.mem_filter.mp hx
      obtain ⟨h1, hn⟩ := Finset.mem_Icc.mp hxI
      have h2 : (((n / 2 : ℕ)) : ℤ) * 2 ≤ (n : ℤ) := by
        exact_mod_cast Nat.div_mul_le_self n 2
      refine Finset.mem_image.mpr
        ⟨x / 2, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
    · intro hx
      obtain ⟨k, hk, hke⟩ := Finset.mem_image.mp hx
      obtain ⟨hk1, hkm⟩ := Finset.mem_Icc.mp hk
      have hke2 : 2 * k = x := hke
      have h2 : (((n / 2 : ℕ)) : ℤ) * 2 ≤ (n : ℤ) := by
        exact_mod_cast Nat.div_mul_le_self n 2
      refine Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
  have hinj : Set.InjOn (fun k : ℤ => 2 * k)
      ↑(Finset.Icc 1 ((n / 2 : ℕ) : ℤ)) :=
    fun a _ b _ h => by
      have h2 : 2 * a = 2 * b := h
      omega
  rw [himg, Finset.card_image_of_injOn hinj, Int.card_Icc]
  have heq : ((n / 2 : ℕ) : ℤ) + 1 - 1 = ((n / 2 : ℕ) : ℤ) := by ring
  rw [heq, Int.toNat_natCast]

/-- **Odd-part translate bound.**  If `e ∈ s` is even then the low odd
part `O ∩ [1, n − e]` translates by `e` into `odds n` disjointly from `O`;
hence `2·|O| ≤ |odds n| + |O ∩ (n − e, n]| ≤ ⌈n/2⌉ + e`. -/
theorem two_mul_card_odd_le_of_even_mem {n : ℕ} {s : Finset ℤ}
    (hsub : s ⊆ interval n) (hsf : IsSumFree s) {e : ℤ}
    (he : e ∈ s) (hep : e % 2 = 0) :
    2 * (s.filter fun x => x % 2 = 1).card ≤ (n + 1) / 2 + e.toNat := by
  classical
  have heI := Finset.mem_Icc.mp (hsub he)
  set O : Finset ℤ := s.filter fun x => x % 2 = 1 with hO
  set Olow : Finset ℤ := O.filter fun x => x ≤ (n : ℤ) - e with hOl
  set Ohigh : Finset ℤ := O.filter fun x => ¬ x ≤ (n : ℤ) - e with hOh
  have hOsub : O ⊆ odds n := by
    intro x hx
    obtain ⟨hxs, hxpar⟩ := Finset.mem_filter.mp hx
    exact mem_odds.mpr ⟨hsub hxs, hxpar⟩
  have hlowsub : Olow.image (· + e) ⊆ odds n := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨x, hxt, rfl⟩
    obtain ⟨hxO, hxle⟩ := Finset.mem_filter.mp hxt
    obtain ⟨hxs, hxpar⟩ := Finset.mem_filter.mp hxO
    have hxI := Finset.mem_Icc.mp (hsub hxs)
    exact mem_odds.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
  have hOlowsub : Olow ⊆ s :=
    (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
  have hdisj : Disjoint (Olow.image (· + e)) O :=
    Disjoint.mono (Finset.image_subset_image hOlowsub)
      (Finset.filter_subset _ _)
      (disjoint_image_add_min_of_isSumFree hsf he).symm
  have hcount : Olow.card + O.card ≤ (odds n).card := by
    calc Olow.card + O.card
        = (Olow.image (· + e)).card + O.card := by
          rw [Finset.card_image_of_injective _ (add_left_injective e)]
      _ = (Olow.image (· + e) ∪ O).card :=
          (Finset.card_union_of_disjoint hdisj).symm
      _ ≤ (odds n).card :=
          Finset.card_le_card (Finset.union_subset hlowsub hOsub)
  have hhigh : Ohigh.card ≤ e.toNat := by
    have hss : Ohigh ⊆ Finset.Icc ((n : ℤ) - e + 1) (n : ℤ) := by
      intro x hx
      obtain ⟨hxO, hxle⟩ := Finset.mem_filter.mp hx
      obtain ⟨hxs, -⟩ := Finset.mem_filter.mp hxO
      exact Finset.mem_Icc.mpr ⟨by omega,
        (Finset.mem_Icc.mp (hsub hxs)).2⟩
    calc Ohigh.card ≤ (Finset.Icc ((n : ℤ) - e + 1) (n : ℤ)).card :=
        Finset.card_le_card hss
      _ = e.toNat := by rw [Int.card_Icc]; congr 1; omega
  have hsplit : Olow.card + Ohigh.card = O.card :=
    Finset.card_filter_add_card_filter_not _
  rw [card_odds] at hcount
  omega

/-- **Even-part translate bound.**  If `e ∈ s` is even then the low even
part `E ∩ [1, n − e]` translates by `e` into `evens n` disjointly from
`E`; hence `2·|E| ≤ |evens n| + |E ∩ (n − e, n]| ≤ ⌊n/2⌋ + e`. -/
theorem two_mul_card_even_le_of_even_mem {n : ℕ} {s : Finset ℤ}
    (hsub : s ⊆ interval n) (hsf : IsSumFree s) {e : ℤ}
    (he : e ∈ s) (hep : e % 2 = 0) :
    2 * (s.filter fun x => x % 2 = 0).card ≤ n / 2 + e.toNat := by
  classical
  have heI := Finset.mem_Icc.mp (hsub he)
  set E : Finset ℤ := s.filter fun x => x % 2 = 0 with hE
  set Elow : Finset ℤ := E.filter fun x => x ≤ (n : ℤ) - e with hEl
  set Ehigh : Finset ℤ := E.filter fun x => ¬ x ≤ (n : ℤ) - e with hEh
  have hEsub : E ⊆ evens n := by
    intro x hx
    obtain ⟨hxs, hxpar⟩ := Finset.mem_filter.mp hx
    exact mem_evens.mpr ⟨hsub hxs, hxpar⟩
  have hlowsub : Elow.image (· + e) ⊆ evens n := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨x, hxt, rfl⟩
    obtain ⟨hxE, hxle⟩ := Finset.mem_filter.mp hxt
    obtain ⟨hxs, hxpar⟩ := Finset.mem_filter.mp hxE
    have hxI := Finset.mem_Icc.mp (hsub hxs)
    exact mem_evens.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
  have hElowsub : Elow ⊆ s :=
    (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
  have hdisj : Disjoint (Elow.image (· + e)) E :=
    Disjoint.mono (Finset.image_subset_image hElowsub)
      (Finset.filter_subset _ _)
      (disjoint_image_add_min_of_isSumFree hsf he).symm
  have hcount : Elow.card + E.card ≤ (evens n).card := by
    calc Elow.card + E.card
        = (Elow.image (· + e)).card + E.card := by
          rw [Finset.card_image_of_injective _ (add_left_injective e)]
      _ = (Elow.image (· + e) ∪ E).card :=
          (Finset.card_union_of_disjoint hdisj).symm
      _ ≤ (evens n).card :=
          Finset.card_le_card (Finset.union_subset hlowsub hEsub)
  have hhigh : Ehigh.card ≤ e.toNat := by
    have hss : Ehigh ⊆ Finset.Icc ((n : ℤ) - e + 1) (n : ℤ) := by
      intro x hx
      obtain ⟨hxE, hxle⟩ := Finset.mem_filter.mp hx
      obtain ⟨hxs, -⟩ := Finset.mem_filter.mp hxE
      exact Finset.mem_Icc.mpr ⟨by omega,
        (Finset.mem_Icc.mp (hsub hxs)).2⟩
    calc Ehigh.card ≤ (Finset.Icc ((n : ℤ) - e + 1) (n : ℤ)).card :=
        Finset.card_le_card hss
      _ = e.toNat := by rw [Int.card_Icc]; congr 1; omega
  have hsplit : Elow.card + Ehigh.card = E.card :=
    Finset.card_filter_add_card_filter_not _
  rw [card_evens] at hcount
  omega

/-- **All-even sum-free sets are small.**  Halving maps an all-even
sum-free `s ⊆ {1,…,n}` injectively onto a sum-free subset of
`{1,…,⌊n/2⌋}`, so `|s| ≤ (⌊n/2⌋ + 1)/2 ≤ 2n/5 + 1`: alternative (i) of the
trichotomy holds unconditionally for all-even sets. -/
theorem card_le_of_forall_even {n : ℕ} {s : Finset ℤ}
    (hsub : s ⊆ interval n) (hsf : IsSumFree s)
    (hpar : ∀ x ∈ s, x % 2 = 0) :
    (s.card : ℝ) ≤ (2 / 5 : ℝ) * (n : ℝ) + 1 := by
  have hEven : ∀ x ∈ s, Even x := fun x hx =>
    ⟨x / 2, by have h := hpar x hx; omega⟩
  have hsub' : halve s ⊆ interval (n / 2) := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨a, rfl⟩ := hEven x hx
    have hxI := Finset.mem_Icc.mp (hsub hx)
    have h2 : (((n / 2 : ℕ)) : ℤ) * 2 ≤ (n : ℤ) := by
      exact_mod_cast Nat.div_mul_le_self n 2
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hsf' : IsSumFree (halve s) := (isSumFree_halve_iff hEven).mpr hsf
  have hcard : (halve s).card = s.card := by
    apply Finset.card_image_of_injOn
    intro a ha b hb hab
    obtain ⟨x, rfl⟩ := hEven a ha
    obtain ⟨y, rfl⟩ := hEven b hb
    have hxy : (x + x) / 2 = (y + y) / 2 := hab
    omega
  have hle := card_le_of_isSumFree hsub' hsf'
  rw [hcard] at hle
  -- `|s| ≤ (⌊n/2⌋ + 1)/2 ≤ (n + 2)/4 ≤ 2n/5 + 1`.
  have hbound : (s.card : ℝ) ≤ ((n : ℝ) + 2) / 4 := by
    have h1 : (s.card : ℝ) ≤ ((((n / 2) + 1) / 2 : ℕ) : ℝ) := by
      exact_mod_cast hle
    have hcast1 : (((n / 2 : ℕ)) : ℝ) ≤ (n : ℝ) / 2 := Nat.cast_div_le
    have hcast2 : ((((n / 2) + 1) / 2 : ℕ) : ℝ) ≤
        (((n / 2 : ℕ)) : ℝ) / 2 + 1 / 2 := by
      have h := Nat.cast_div_le (m := (n / 2) + 1) (n := 2) (α := ℝ)
      push_cast at h
      linarith
    linarith
  have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith

/-! ## The residual hypotheses and the reductions

Everything proved so far disposes of:

* sets with `3·min s ≥ n` (high-minimum regime, `card_le_min…`);
* all-odd sets — alternative (ii) by definition;
* all-even sets — alternative (i) by halving (`card_le_of_forall_even`).

The remaining content of `DFST` is therefore exactly the mixed-parity
low-minimum range, packaged below. -/

/-- **Residual hypothesis, coarse form:** the DFST trichotomy for sets
whose minimum is below `n/3`.  Equivalent to `DFST`
(`dfst_iff_dfstLowMin`): the complementary range is proved in this file. -/
def DFSTLowMin : Prop :=
  ∀ᶠ n : ℕ in Filter.atTop, ∀ s : Finset ℤ, s ⊆ interval n →
    IsSumFree s → (∃ m ∈ s, (∀ x ∈ s, m ≤ x) ∧ 3 * m < (n : ℤ)) →
      (s.card : ℝ) ≤ (2 / 5 : ℝ) * (n : ℝ) + 1 ∨
        s ⊆ odds n ∨ ∀ x ∈ s, (s.card : ℤ) ≤ x

/-- **Residual hypothesis, sharp form:** the DFST conclusion (i) or (iii)
for *mixed-parity* sum-free sets — those containing both an even and an
odd element — whose minimum is below `n/3`.  This is the precise locus of
the Deshouillers–Freiman–Sós–Temkin theorem's difficulty: all-odd sets
give (ii) trivially, all-even sets give (i) by halving, and `min s ≥ n/3`
is handled unconditionally by `card_le_min_of_lt_three_mul_min`. -/
def DFSTMixed : Prop :=
  ∀ᶠ n : ℕ in Filter.atTop, ∀ s : Finset ℤ, s ⊆ interval n →
    IsSumFree s → (∃ m ∈ s, (∀ x ∈ s, m ≤ x) ∧ 3 * m < (n : ℤ)) →
      (∃ e ∈ s, e % 2 = 0) → (∃ o ∈ s, o % 2 = 1) →
        (s.card : ℝ) ≤ (2 / 5 : ℝ) * (n : ℝ) + 1 ∨
          ∀ x ∈ s, (s.card : ℤ) ≤ x

/-- `DFSTMixed → DFSTLowMin`: in the low-minimum range, a set with an even
element is either mixed (hypothesis applies) or all-even (small by
halving); a set with no even element is all-odd, giving alternative (ii). -/
theorem dfstLowMin_of_dfstMixed (h : DFSTMixed) : DFSTLowMin := by
  filter_upwards [h] with n hn
  intro s hsub hsf hmin
  rcases em (∃ e ∈ s, e % 2 = 0) with hev | hnev
  · rcases em (∃ o ∈ s, o % 2 = 1) with hod | hnod
    · obtain ⟨e, he, hep⟩ := hev
      obtain ⟨o, ho, hop⟩ := hod
      rcases hn s hsub hsf hmin ⟨e, he, hep⟩ ⟨o, ho, hop⟩ with h1 | h2
      · exact Or.inl h1
      · exact Or.inr (Or.inr h2)
    · -- No odd element: `s` is all even, so `|s| ≤ 2n/5 + 1` by halving.
      refine Or.inl ?_
      apply card_le_of_forall_even hsub hsf
      intro x hx
      have hx' : ¬ x % 2 = 1 := fun hpar => hnod ⟨x, hx, hpar⟩
      omega
  · -- No even element: `s` is all odd, so `s ⊆ odds n`.
    refine Or.inr (Or.inl ?_)
    intro x hx
    have hx' : x % 2 = 1 := by
      have h2 : ¬ x % 2 = 0 := fun hpar => hnev ⟨x, hx, hpar⟩
      omega
    exact mem_odds.mpr ⟨hsub hx, hx'⟩

/-- `DFSTLowMin → DFST`: sets with `3·min s ≥ n` are handled
unconditionally by `dfst_trichotomy_of_le_three_mul_min`. -/
theorem dfst_of_dfstLowMin (h : DFSTLowMin) : DFST := by
  filter_upwards [h] with n hn
  intro s hsub hsf
  rcases s.eq_empty_or_nonempty with rfl | hne
  · left
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  · rcases le_or_gt (n : ℤ) (3 * s.min' hne) with hle | hgt
    · rcases dfst_trichotomy_of_le_three_mul_min hsub hsf
        (s.min'_mem hne) (fun x hx => Finset.min'_le s x hx) hle
        with h1 | h2
      · exact Or.inl h1
      · exact Or.inr (Or.inr h2)
    · exact hn s hsub hsf
        ⟨s.min' hne, s.min'_mem hne, fun x hx => Finset.min'_le s x hx, hgt⟩

/-- The mixed-parity low-minimum hypothesis suffices for the full DFST
trichotomy. -/
theorem dfst_of_dfstMixed (h : DFSTMixed) : DFST :=
  dfst_of_dfstLowMin (dfstLowMin_of_dfstMixed h)

/-- `DFST → DFSTLowMin` is immediate, so the low-minimum range captures
the full strength of the trichotomy. -/
theorem dfstLowMin_of_dfst (h : DFST) : DFSTLowMin := by
  filter_upwards [h] with n hn
  intro s hsub hsf _
  exact hn s hsub hsf

/-- `DFST → DFSTMixed` is immediate: a mixed set contains an even element,
which already kills alternative (ii). -/
theorem dfstMixed_of_dfst (h : DFST) : DFSTMixed := by
  filter_upwards [h] with n hn
  intro s hsub hsf _ ⟨e, he, hep⟩ _
  rcases hn s hsub hsf with h1 | h2 | h3
  · exact Or.inl h1
  · -- `s ⊆ odds n` is incompatible with the even element `e ∈ s`.
    exact absurd hep (by
      have hpar := (mem_odds.mp (h2 he)).2
      omega)
  · exact Or.inr h3

/-- `DFST ↔ DFSTLowMin`: the entire trichotomy is equivalent to its
low-minimum range. -/
theorem dfst_iff_dfstLowMin : DFST ↔ DFSTLowMin :=
  ⟨dfstLowMin_of_dfst, dfst_of_dfstLowMin⟩

/-- `DFST ↔ DFSTMixed`: the entire trichotomy is equivalent to its
mixed-parity low-minimum range. -/
theorem dfst_iff_dfstMixed : DFST ↔ DFSTMixed :=
  ⟨dfstMixed_of_dfst, dfst_of_dfstMixed⟩

/-! ## Downstream interface -/

/-- **Weak trichotomy** (the form used by `container_trichotomy`): under
`DFST`, every sum-free `s ⊆ {1,…,n}` with `|s| > 2n/5 + 1` is all-odd or
satisfies `min s ≥ |s|`. -/
theorem dfst_range (hDFST : DFST) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ s : Finset ℤ, s ⊆ interval n →
      IsSumFree s → (2 / 5 : ℝ) * (n : ℝ) + 1 < (s.card : ℝ) →
        s ⊆ odds n ∨ ∀ x ∈ s, (s.card : ℤ) ≤ x := by
  filter_upwards [hDFST] with n hn
  intro s hsub hsf hbig
  rcases hn s hsub hsf with h1 | h2 | h3
  · exact absurd h1 (not_le_of_gt hbig)
  · exact Or.inl h2
  · exact Or.inr h3

/-- The weak trichotomy from the low-minimum hypothesis alone: in the
high-minimum range the conclusion `min s ≥ |s|` is unconditional
(`card_le_min_of_two_fifths_lt`). -/
theorem dfst_range_of_dfstLowMin (h : DFSTLowMin) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ s : Finset ℤ, s ⊆ interval n →
      IsSumFree s → (2 / 5 : ℝ) * (n : ℝ) + 1 < (s.card : ℝ) →
        s ⊆ odds n ∨ ∀ x ∈ s, (s.card : ℤ) ≤ x := by
  filter_upwards [h] with n hn
  intro s hsub hsf hbig
  have hpos : 0 < s.card := by
    have h0 : (0 : ℝ) < (s.card : ℝ) := by
      have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    exact_mod_cast h0
  have hne : s.Nonempty := Finset.card_pos.mp hpos
  rcases le_or_gt (n : ℤ) (3 * s.min' hne) with hle | hgt
  · exact Or.inr (card_le_min_of_two_fifths_lt hsub hsf
      (s.min'_mem hne) (fun x hx => Finset.min'_le s x hx) hle hbig)
  · rcases hn s hsub hsf
      ⟨s.min' hne, s.min'_mem hne, fun x hx => Finset.min'_le s x hx, hgt⟩
      with h1 | h2 | h3
    · exact absurd h1 (not_le_of_gt hbig)
    · exact Or.inl h2
    · exact Or.inr h3

/-- The weak trichotomy from the sharp residual hypothesis. -/
theorem dfst_range_of_dfstMixed (h : DFSTMixed) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ s : Finset ℤ, s ⊆ interval n →
      IsSumFree s → (2 / 5 : ℝ) * (n : ℝ) + 1 < (s.card : ℝ) →
        s ⊆ odds n ∨ ∀ x ∈ s, (s.card : ℤ) ≤ x :=
  dfst_range_of_dfstLowMin (dfstLowMin_of_dfstMixed h)

/-- **Container-scale corollary.**  Under `DFST`, every sum-free
`s ⊆ {1,…,n}` with `|s| ≥ (1/2 − γ)·n` for `γ < 1/10` is all-odd or
satisfies `min s ≥ |s|` — the disjunction consumed by the container
argument (applied there at `γ = 1/11 + o(1)`, `|s| ≥ 9n/22`-ish). -/
theorem dfst_container_case (hDFST : DFST) {γ : ℝ} (hγ : γ < 1 / 10) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ s : Finset ℤ, s ⊆ interval n →
      IsSumFree s → ((1 / 2 : ℝ) - γ) * (n : ℝ) ≤ (s.card : ℝ) →
        s ⊆ odds n ∨ ∀ x ∈ s, (s.card : ℤ) ≤ x := by
  have hδ : (0 : ℝ) < 1 / 10 - γ := by linarith
  filter_upwards [dfst_range hDFST,
    Filter.eventually_ge_atTop (⌈(1 / 10 - γ)⁻¹⌉₊ + 1)] with n hn hnbig
  intro s hsub hsf hcard
  refine hn s hsub hsf ?_
  have hceil : (⌈(1 / 10 - γ)⁻¹⌉₊ : ℕ) < n := by omega
  have hstrict : (1 / 10 - γ)⁻¹ < (n : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hceil)
  have h1 : (1 : ℝ) < (1 / 10 - γ) * (n : ℝ) := by
    have h2 := mul_lt_mul_of_pos_right hstrict hδ
    rw [inv_mul_cancel₀ hδ.ne'] at h2
    rw [mul_comm]
    exact h2
  have hsplit : ((1 / 2 : ℝ) - γ) * (n : ℝ) =
      (2 / 5 : ℝ) * (n : ℝ) + (1 / 10 - γ) * (n : ℝ) := by ring
  rw [hsplit] at hcard
  linarith

/-- The container-scale corollary from the sharp residual hypothesis. -/
theorem dfst_container_case_of_dfstMixed (h : DFSTMixed) {γ : ℝ}
    (hγ : γ < 1 / 10) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ s : Finset ℤ, s ⊆ interval n →
      IsSumFree s → ((1 / 2 : ℝ) - γ) * (n : ℝ) ≤ (s.card : ℝ) →
        s ⊆ odds n ∨ ∀ x ∈ s, (s.card : ℤ) ≤ x :=
  dfst_container_case (dfst_of_dfstMixed h) hγ

end JSP000728
