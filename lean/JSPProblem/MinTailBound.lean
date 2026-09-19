import JSPProblem.Fingerprint
import JSPProblem.MinDecomp
import JSPProblem.Obstruction
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# JSP-000728 — the per-container tail bound (containers avoiding small elements)

A *warmup* container ingredient of the BLST18 fingerprint bound: containers
`C ⊆ {1,…,n}` that avoid the initial segment `{1,…,K}` house few maximal
sum-free sets.  The mechanism is a **single trace injection**, sharper than
the naive minimum-class geometric sum: if `s ⊆ {K+1,…,n}` is sum-free and
inclusion-maximal (inside `{1,…,n}` or inside `C`), then `s` is determined
by its trace `s ∩ {K+1,…,n−K−1}`.

Indeed, let `x` be the least element of `A ∆ B` for two such sets with equal
traces.  Since `K < x ≤ n`, the hypothesis `x ∉ {K+1,…,n−K−1}` forces
`x ≥ n − K`.  Maximality obstructs adjoining `x` to the other set in one of
four ways, all numerically impossible: a sum `a + b = x` would transfer to
the other side (both summands are below `x`), while `a + x`, `x + a` and
`x + x` exceed `n` — for the last one, `x ≥ n − K` and `x ≥ K + 1` give
`2x ≥ min(2n − 2K, 2K + 2) ≥ n + 1`.

Consequences:

* `card_maxSumFreeSets_min_gt` — the maximal sum-free sets of `{1,…,n}`
  all of whose elements exceed `K` number at most `2 ^ (n − 2K − 1)₊`.
* `filter_min_gt_eq_empty_of_two_mul` — for `2K ≥ n + 3` there are none at
  all: such a set would have to equal `upperHalf n`, whose least element
  `⌊n/2⌋ + 1` is `≤ K`.
* `card_maxSumFreeSets_min_gt_real` — the `4 · 2^{n−2K}` real-valued form.
* `card_maxSumFreeSetsIn_le_two_pow_of_lower` — the **per-container** count:
  a container `C ⊆ {1,…,n}` avoiding `{1,…,K}` houses at most
  `2 ^ (n − 2K − 1)₊` maximal-in-`C` sum-free sets (the bound is tight:
  `C = {5}`, `n = 5`, `K = 4` gives `1`).
* `card_maxSumFreeSets_filter_subset_of_lower` — the same bound for the
  maximal sets literally contained in `C` (via
  `card_maxSumFreeSets_filter_le`).
* `card_maxSumFreeSetsIn_Icc_le`, `card_maxSumFreeSetsIn_Icc_le_rpow` and
  `maxSumFreeSetsIn_upper_third_le` — the interval container `{a,…,n}`
  houses at most `2^{n−2a+1}₊` sets, i.e. `2^{(n+1)/3} = O(2^{n/3})` when
  `a > n/3`.
-/

namespace JSP000728

open scoped symmDiff

/-- **Obstruction extraction.**  If `insert x s` is not sum-free (`x > 0`,
`s` positive and sum-free), one of the four obstruction types occurs:
`x` is a sum `a + b` in `s`, or `a + x`, `x + a`, `x + x ∈ s`.  This is the
content of `IsMaxSumFree.exists_obstruction` with the maximality hypothesis
replaced by the raw failure of sum-freeness. -/
theorem obstruction_of_not_isSumFree_insert {s : Finset ℤ} {x : ℤ}
    (hs : IsSumFree s) (hx : 0 < x) (hpos : ∀ a ∈ s, 0 < a)
    (h : ¬ IsSumFree (insert x s)) :
    (∃ a ∈ s, ∃ b ∈ s, a + b = x) ∨ (∃ a ∈ s, a + x ∈ s) ∨
      (∃ a ∈ s, x + a ∈ s) ∨ (x + x ∈ s) := by
  have hiff := hs.insert_iff hx hpos
  have hnot' : ¬ ((∀ a ∈ s, ∀ b ∈ s, a + b ≠ x) ∧ (∀ a ∈ s, a + x ∉ s) ∧
      (∀ a ∈ s, x + a ∉ s) ∧ (x + x ∉ s)) :=
    fun hb => h (hiff.mpr ⟨hs, hb⟩)
  by_cases h2 : ∃ a ∈ s, ∃ b ∈ s, a + b = x
  · exact Or.inl h2
  by_cases h3 : ∃ a ∈ s, a + x ∈ s
  · exact Or.inr (Or.inl h3)
  by_cases h4 : ∃ a ∈ s, x + a ∈ s
  · exact Or.inr (Or.inr (Or.inl h4))
  refine Or.inr (Or.inr (Or.inr ?_))
  by_contra hxx
  exact hnot' ⟨fun a ha b hb hab => h2 ⟨a, ha, b, hb, hab⟩,
    fun a ha hax => h3 ⟨a, ha, hax⟩,
    fun a ha hxa => h4 ⟨a, ha, hxa⟩,
    hxx⟩

/-- One-sided step of the tail-determination argument.  If `x` is the least
element of `A ∆ B`, `x ∈ A`, `x ∉ B`, and `A B ⊆ {K+1,…,n}` agree on the
trace `{K+1,…,n−K−1}`, then `x ≥ n − K`; every obstruction to `x` over `B`
is impossible: `a + b = x` transfers below `x` and contradicts `A`
sum-free, while `a + x`, `x + a`, `x + x` exceed `n`. -/
private theorem false_of_symmDiff_min_mem {n : ℕ} {K : ℕ} {A B : Finset ℤ}
    {x : ℤ}
    (hKA : ∀ y ∈ A, (K : ℤ) < y) (hKB : ∀ y ∈ B, (K : ℤ) < y)
    (_hAn : ∀ y ∈ A, y ≤ (n : ℤ)) (hBn : ∀ y ∈ B, y ≤ (n : ℤ))
    (hsfA : IsSumFree A) (hsfB : IsSumFree B)
    (hmaxB : ∀ y ∈ A \ B, ¬ IsSumFree (insert y B))
    (htr : A ∩ Finset.Icc ((K : ℤ) + 1) ((n : ℤ) - K - 1) =
           B ∩ Finset.Icc ((K : ℤ) + 1) ((n : ℤ) - K - 1))
    (hxmin : ∀ y ∈ A ∆ B, x ≤ y)
    (hxA : x ∈ A) (hxB : x ∉ B) : False := by
  have hxK : (K : ℤ) < x := hKA x hxA
  -- Since `x ∈ A ⊆ {K+1,…,n}` and `x ∉ B`, `x` must lie above the trace
  -- window `{K+1,…,n−K−1}`: `x ≥ n − K`.
  have hxbig : (n : ℤ) - K ≤ x := by
    by_contra hlt
    have hlt' : x < (n : ℤ) - K := not_le.mp hlt
    have hxI : x ∈ Finset.Icc ((K : ℤ) + 1) ((n : ℤ) - K - 1) :=
      Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    exact hxB (Finset.mem_inter.mp
      (htr ▸ Finset.mem_inter.mpr ⟨hxA, hxI⟩)).1
  have hnot := hmaxB x (Finset.mem_sdiff.mpr ⟨hxA, hxB⟩)
  have hposB : ∀ a ∈ B, (0 : ℤ) < a := fun a ha => by
    have := hKB a ha; omega
  rcases obstruction_of_not_isSumFree_insert hsfB (by omega : (0:ℤ) < x)
    hposB hnot with hsum | hax | hxa | hxx
  · -- `a + b = x` with `a, b ∈ B`: both summands lie below `x`, hence are
    -- not in `A ∆ B`, hence lie in `A` — contradicting `A` sum-free.
    obtain ⟨a, ha, b, hb, hab⟩ := hsum
    have hbpos : (0 : ℤ) < b := hposB b hb
    have haA : a ∈ A := by
      by_contra haA
      have hge := hxmin a (Finset.mem_symmDiff.mpr (Or.inr ⟨ha, haA⟩))
      omega
    have hapos : (0 : ℤ) < a := hposB a ha
    have hbA : b ∈ A := by
      by_contra hbA
      have hge := hxmin b (Finset.mem_symmDiff.mpr (Or.inr ⟨hb, hbA⟩))
      omega
    exact hsfA a haA b hbA (hab ▸ hxA)
  · -- `a + x ∈ B ⊆ {1,…,n}`: `a ≥ K+1` and `x ≥ n − K` give `a + x ≥ n+1`.
    obtain ⟨a, ha, hax⟩ := hax
    have hbnd := hBn (a + x) hax
    have ham := hKB a ha
    omega
  · obtain ⟨a, ha, hxa⟩ := hxa
    have hbnd := hBn (x + a) hxa
    have ham := hKB a ha
    omega
  · -- `x + x ∈ B`: `2x ≥ 2·max(n−K, K+1) ≥ n + 1 > n`.
    have hbnd := hBn (x + x) hxx
    omega

/-- **Tail determination.**  Two sum-free sets `A B ⊆ {K+1,…,n}` that are
*mutually maximal* (each `x ∈ A ∖ B` fails to extend `B` and vice versa) and
share the trace `{K+1,…,n−K−1}` are equal. -/
theorem eq_of_forall_gt_of_trace_eq {n : ℕ} {K : ℕ} {A B : Finset ℤ}
    (hKA : ∀ y ∈ A, (K : ℤ) < y) (hKB : ∀ y ∈ B, (K : ℤ) < y)
    (hAn : ∀ y ∈ A, y ≤ (n : ℤ)) (hBn : ∀ y ∈ B, y ≤ (n : ℤ))
    (hsfA : IsSumFree A) (hsfB : IsSumFree B)
    (hmaxA : ∀ y ∈ B \ A, ¬ IsSumFree (insert y A))
    (hmaxB : ∀ y ∈ A \ B, ¬ IsSumFree (insert y B))
    (htr : A ∩ Finset.Icc ((K : ℤ) + 1) ((n : ℤ) - K - 1) =
           B ∩ Finset.Icc ((K : ℤ) + 1) ((n : ℤ) - K - 1)) :
    A = B := by
  by_contra hne
  have hD : (A ∆ B).Nonempty := Finset.symmDiff_nonempty.mpr hne
  set x := (A ∆ B).min' hD
  have hxmem : x ∈ A ∆ B := Finset.min'_mem _ hD
  have hxmin : ∀ y ∈ A ∆ B, x ≤ y := fun y hy => Finset.min'_le _ y hy
  rcases Finset.mem_symmDiff.mp hxmem with ⟨hxA, hxB⟩ | ⟨hxB, hxA⟩
  · exact false_of_symmDiff_min_mem hKA hKB hAn hBn hsfA hsfB hmaxB htr
      hxmin hxA hxB
  · have hxmin' : ∀ y ∈ B ∆ A, x ≤ y :=
      fun y hy => hxmin y (symmDiff_comm B A ▸ hy)
    exact false_of_symmDiff_min_mem hKB hKA hBn hAn hsfB hsfA hmaxA htr.symm
      hxmin' hxB hxA

/-- The trace window `{K+1,…,n−K−1}` has `n − 2K − 1` elements (when
positive). -/
theorem card_trace_window (n : ℕ) (K : ℕ) :
    (Finset.Icc ((K : ℤ) + 1) ((n : ℤ) - K - 1)).card =
      ((n : ℤ) - 2 * K - 1).toNat := by
  rw [Int.card_Icc]
  congr 1
  ring

/-- **Tail bound.**  The maximal sum-free subsets of `{1,…,n}` all of whose
elements exceed `K` number at most `2 ^ (n − 2K − 1)` — each is determined
by its trace on `{K+1,…,n−K−1}` (`eq_of_forall_gt_of_trace_eq`), the
obstruction for the interval case being `IsMaxSumFree`'s third component. -/
theorem card_maxSumFreeSets_min_gt {n : ℕ} (K : ℕ) :
    ((maxSumFreeSets n).filter fun M => ∀ x ∈ M, (K : ℤ) < x).card ≤
      2 ^ ((n : ℤ) - 2 * K - 1).toNat := by
  rw [← card_trace_window n K]
  calc ((maxSumFreeSets n).filter fun M => ∀ x ∈ M, (K : ℤ) < x).card
      ≤ (Finset.Icc ((K : ℤ) + 1) ((n : ℤ) - K - 1)).powerset.card := by
        refine Finset.card_le_card_of_injOn
          (fun M => M ∩ Finset.Icc ((K : ℤ) + 1) ((n : ℤ) - K - 1)) ?_ ?_
        · intro M _
          exact Finset.mem_powerset.mpr Finset.inter_subset_right
        · intro A hA B hB htr
          rw [Finset.mem_coe, Finset.mem_filter] at hA hB
          obtain ⟨hAm, hAgt⟩ := hA
          obtain ⟨hBm, hBgt⟩ := hB
          have hA' := mem_maxSumFreeSets.mp hAm
          have hB' := mem_maxSumFreeSets.mp hBm
          exact eq_of_forall_gt_of_trace_eq hAgt hBgt
            (fun y hy => (Finset.mem_Icc.mp (hA'.1 hy)).2)
            (fun y hy => (Finset.mem_Icc.mp (hB'.1 hy)).2)
            hA'.2.1 hB'.2.1
            (fun y hy => hA'.2.2 y
              (hB'.1 (Finset.mem_sdiff.mp hy).1) (Finset.mem_sdiff.mp hy).2)
            (fun y hy => hB'.2.2 y
              (hA'.1 (Finset.mem_sdiff.mp hy).1) (Finset.mem_sdiff.mp hy).2)
            htr
    _ = 2 ^ (Finset.Icc ((K : ℤ) + 1) ((n : ℤ) - K - 1)).card :=
        Finset.card_powerset _

/-- **Emptiness in the far tail.**  If `2K ≥ n + 3` (and `n ≥ 1`), no
maximal sum-free subset of `{1,…,n}` avoids `{1,…,K}`: such a set `M` would
lie in `{x : 2x > n} = upperHalf n`, forcing `M = upperHalf n`, but the
least element `⌊n/2⌋ + 1 = (n + 2)/2` of `upperHalf n` satisfies
`(n+2)/2 ≤ K`. -/
theorem filter_min_gt_eq_empty_of_two_mul {n : ℕ} (hn : 1 ≤ n) {K : ℕ}
    (hK : (n : ℤ) + 2 < 2 * (K : ℤ)) :
    ((maxSumFreeSets n).filter fun M => ∀ x ∈ M, (K : ℤ) < x) = ∅ := by
  rw [Finset.filter_eq_empty_iff]
  intro M hM hgt
  have hM' := mem_maxSumFreeSets.mp hM
  have hne := nonempty_of_mem_maxSumFreeSets hn hM
  -- `M ⊆ upperHalf n`, hence `M = upperHalf n`.
  have hsub : M ⊆ upperHalf n := by
    intro x hx
    rw [mem_upperHalf]
    exact ⟨hM'.1 hx, by have := hgt x hx; omega⟩
  have hMeq : M = upperHalf n :=
    eq_upperHalf_of_isMaxSumFree_subset hM' hsub
  -- A nonempty `M ⊆ {1,…,n}` with all elements `> K` forces `K < n`.
  obtain ⟨x₀, hx₀⟩ := hne
  have hx₀n : x₀ ≤ (n : ℤ) := (Finset.mem_Icc.mp (hM'.1 hx₀)).2
  have hx₀K : (K : ℤ) < x₀ := hgt x₀ hx₀
  -- `t = (n+2)/2 ∈ upperHalf n` but `t ≤ K`, contradicting `K < t`.
  have htuh : ((n : ℤ) + 2) / 2 ∈ upperHalf n := by
    rw [mem_upperHalf]
    refine ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
  have htM : ((n : ℤ) + 2) / 2 ∈ M := hMeq ▸ htuh
  have hKlt := hgt (((n : ℤ) + 2) / 2) htM
  omega

/-- `2 ^ (t − 1)₊ ≤ 4 · 2 ^ t` for `t ≥ −2` (in `ℝ`). -/
private theorem two_pow_toNat_sub_one_le_four_mul {t : ℤ} (ht : -2 ≤ t) :
    (2 : ℝ) ^ (t - 1).toNat ≤ 4 * 2 ^ (t : ℝ) := by
  rcases le_or_gt 0 (t - 1) with h | h
  · -- `t ≥ 1`: the left side is `2 ^ (t−1)` and `2 ^ t = 2 · 2 ^ (t−1)`.
    rw [← Real.rpow_natCast]
    have he : (((t - 1).toNat : ℕ) : ℝ) = (t : ℝ) - 1 := by
      exact_mod_cast Int.toNat_of_nonneg h
    rw [he]
    have h2t : (2 : ℝ) ^ (t : ℝ) = 2 * (2 : ℝ) ^ ((t : ℝ) - 1) := by
      conv_lhs => rw [show (t : ℝ) = ((t : ℝ) - 1) + 1 from by ring,
        Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
      ring
    rw [h2t]
    have hu : (0 : ℝ) < (2 : ℝ) ^ ((t : ℝ) - 1) :=
      Real.rpow_pos_of_pos (by norm_num) _
    nlinarith
  · -- `t ≤ 0`: the left side is `1`, and `t ≥ −2` gives `2 ^ t ≥ 1/4`.
    rw [Int.toNat_of_nonpos h.le, pow_zero]
    have hge : (1 / 4 : ℝ) ≤ (2 : ℝ) ^ (t : ℝ) := by
      have h2 : (2 : ℝ) ^ (-2 : ℝ) ≤ (2 : ℝ) ^ (t : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num)
          (by exact_mod_cast ht)
      have h4 : (2 : ℝ) ^ (-2 : ℝ) = 1 / 4 := by
        rw [show (-2 : ℝ) = ((-2 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
        norm_num
      rwa [h4] at h2
    nlinarith

/-- **Real-valued tail bound** (the `4 · 2^{n−2K}` form).  For `2K ≤ n + 2`
this follows from `card_maxSumFreeSets_min_gt`; for `2K ≥ n + 3` the
filtered family is empty (`filter_min_gt_eq_empty_of_two_mul`). -/
theorem card_maxSumFreeSets_min_gt_real {n : ℕ} (hn : 1 ≤ n) (K : ℕ) :
    (((maxSumFreeSets n).filter fun M => ∀ x ∈ M, (K : ℤ) < x).card : ℝ) ≤
      4 * 2 ^ ((n : ℝ) - 2 * (K : ℝ)) := by
  rcases le_or_gt (2 * (K : ℤ)) ((n : ℤ) + 2) with hle | hlt
  · have h1 : (((maxSumFreeSets n).filter
        fun M => ∀ x ∈ M, (K : ℤ) < x).card : ℝ) ≤
        (2 : ℝ) ^ ((n : ℤ) - 2 * K - 1).toNat := by
      exact_mod_cast card_maxSumFreeSets_min_gt K
    refine h1.trans ?_
    have h2 := two_pow_toNat_sub_one_le_four_mul
      (t := (n : ℤ) - 2 * K) (by omega)
    rwa [show (((n : ℤ) - 2 * (K : ℤ) : ℤ) : ℝ) = (n : ℝ) - 2 * (K : ℝ)
      from by push_cast; ring] at h2
  · rw [filter_min_gt_eq_empty_of_two_mul hn hlt, Finset.card_empty,
      Nat.cast_zero]
    positivity

/-- **Per-container tail bound.**  A container `C ⊆ {1,…,n}` avoiding
`{1,…,K}` houses at most `2 ^ (n − 2K − 1)₊` maximal-in-`C` sum-free sets:
the same trace determination applies, the obstruction now coming from
`IsMaxSumFreeIn`.  The bound is tight (`C = {n}` with `2K ≥ n + 3` houses
exactly one set). -/
theorem card_maxSumFreeSetsIn_le_two_pow_of_lower {n : ℕ} {C : Finset ℤ}
    {K : ℕ}
    (hC : C ⊆ interval n) (hCK : ∀ x ∈ C, (K : ℤ) < x) :
    (maxSumFreeSetsIn n C).card ≤ 2 ^ ((n : ℤ) - 2 * K - 1).toNat := by
  rw [← card_trace_window n K]
  calc (maxSumFreeSetsIn n C).card
      ≤ (Finset.Icc ((K : ℤ) + 1) ((n : ℤ) - K - 1)).powerset.card := by
        refine Finset.card_le_card_of_injOn
          (fun s => s ∩ Finset.Icc ((K : ℤ) + 1) ((n : ℤ) - K - 1)) ?_ ?_
        · intro s _
          exact Finset.mem_powerset.mpr Finset.inter_subset_right
        · intro A hA B hB htr
          rw [Finset.mem_coe, mem_maxSumFreeSetsIn] at hA hB
          obtain ⟨hAC, hAi⟩ := hA
          obtain ⟨hBC, hBi⟩ := hB
          exact eq_of_forall_gt_of_trace_eq
            (fun y hy => hCK y (hAC hy)) (fun y hy => hCK y (hBC hy))
            (fun y hy => (Finset.mem_Icc.mp (hC (hAC hy))).2)
            (fun y hy => (Finset.mem_Icc.mp (hC (hBC hy))).2)
            hAi.2.1 hBi.2.1
            (fun y hy => hAi.2.2 y
              (hBC (Finset.mem_sdiff.mp hy).1) (Finset.mem_sdiff.mp hy).2)
            (fun y hy => hBi.2.2 y
              (hAC (Finset.mem_sdiff.mp hy).1) (Finset.mem_sdiff.mp hy).2)
            htr
    _ = 2 ^ (Finset.Icc ((K : ℤ) + 1) ((n : ℤ) - K - 1)).card :=
        Finset.card_powerset _

/-- The maximal sum-free sets of `{1,…,n}` contained in a container `C`
avoiding `{1,…,K}` number at most `2 ^ (n − 2K − 1)₊`. -/
theorem card_maxSumFreeSets_filter_subset_of_lower {n : ℕ} {C : Finset ℤ}
    {K : ℕ}
    (hC : C ⊆ interval n) (hCK : ∀ x ∈ C, (K : ℤ) < x) :
    ((maxSumFreeSets n).filter (· ⊆ C)).card ≤
      2 ^ ((n : ℤ) - 2 * K - 1).toNat :=
  (card_maxSumFreeSets_filter_le hC).trans
    (card_maxSumFreeSetsIn_le_two_pow_of_lower hC hCK)

/-! ## Interval containers `{a,…,n}` -/

/-- The interval container `{a,…,n}` houses at most `2 ^ (n − 2a + 1)₊`
maximal-in-container sum-free sets (`K = a − 1` in
`card_maxSumFreeSetsIn_le_two_pow_of_lower`). -/
theorem card_maxSumFreeSetsIn_Icc_le {n : ℕ} {a : ℕ} (ha : 1 ≤ a) :
    (maxSumFreeSetsIn n (Finset.Icc (a : ℤ) (n : ℤ))).card ≤
      2 ^ ((n : ℤ) - 2 * a + 1).toNat := by
  have hC : Finset.Icc (a : ℤ) (n : ℤ) ⊆ interval n := by
    intro x hx
    rw [Finset.mem_Icc] at hx
    exact Finset.mem_Icc.mpr ⟨by omega, hx.2⟩
  have hCK : ∀ x ∈ Finset.Icc (a : ℤ) (n : ℤ), ((a - 1 : ℕ) : ℤ) < x := by
    intro x hx
    rw [Finset.mem_Icc] at hx
    omega
  have h := card_maxSumFreeSetsIn_le_two_pow_of_lower
    (C := Finset.Icc (a : ℤ) (n : ℤ)) (K := a - 1) hC hCK
  have hcast : ((a - 1 : ℕ) : ℤ) = (a : ℤ) - 1 := by omega
  rw [show ((n : ℤ) - 2 * (a : ℤ) + 1) = (n : ℤ) - 2 * ((a - 1 : ℕ) : ℤ) - 1
    by rw [hcast]; ring]
  exact h

/-- For `a > n/3` the interval container `{a,…,n}` houses at most
`2 ^ ((n+1)/3)` maximal-in-container sum-free sets. -/
theorem card_maxSumFreeSetsIn_Icc_le_rpow {n : ℕ} {a : ℕ}
    (ha : 1 ≤ a) (h3a : (n : ℤ) < 3 * a) :
    ((maxSumFreeSetsIn n (Finset.Icc (a : ℤ) (n : ℤ))).card : ℝ) ≤
      2 ^ (((n : ℝ) + 1) / 3) := by
  have hcast : ((maxSumFreeSetsIn n (Finset.Icc (a : ℤ) (n : ℤ))).card : ℝ) ≤
      (2 : ℝ) ^ ((n : ℤ) - 2 * a + 1).toNat := by
    exact_mod_cast card_maxSumFreeSetsIn_Icc_le ha
  refine hcast.trans ?_
  rcases le_or_gt 0 ((n : ℤ) - 2 * a + 1) with he | he
  · rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
    have hcast2 : (((n : ℤ) - 2 * a + 1).toNat : ℝ) =
        (n : ℝ) - 2 * (a : ℝ) + 1 := by
      have h2 : (((n : ℤ) - 2 * a + 1).toNat : ℤ) = (n : ℤ) - 2 * a + 1 :=
        Int.toNat_of_nonneg he
      exact_mod_cast h2
    rw [hcast2]
    have h3aR : (n : ℝ) + 1 ≤ 3 * (a : ℝ) := by
      have h3ai : (n : ℤ) + 1 ≤ 3 * (a : ℤ) := by omega
      exact_mod_cast h3ai
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 3)]
    linarith
  · rw [Int.toNat_of_nonpos he.le, pow_zero]
    exact Real.one_le_rpow (by norm_num : (1 : ℝ) ≤ 2) (by positivity)

/-- **Upper-third container count.**  An interval container `{a,…,n}` with
`a > n/3` houses at most `2 · 2^{n/3}` maximal-in-container sum-free sets —
the determined bound `2^{n−2a+1}` is `O(2^{n/3})`. -/
theorem maxSumFreeSetsIn_upper_third_le {n : ℕ} {a : ℕ}
    (ha : 1 ≤ a) (h3a : (n : ℤ) < 3 * a) :
    ((maxSumFreeSetsIn n (Finset.Icc (a : ℤ) (n : ℤ))).card : ℝ) ≤
      2 * 2 ^ ((n : ℝ) / 3) := by
  refine (card_maxSumFreeSetsIn_Icc_le_rpow ha h3a).trans ?_
  have hpos : (0 : ℝ) < (2 : ℝ) ^ ((n : ℝ) / 3) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hsplit : (2 : ℝ) ^ (((n : ℝ) + 1) / 3) =
      (2 : ℝ) ^ ((n : ℝ) / 3) * (2 : ℝ) ^ (1 / 3 : ℝ) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  rw [hsplit]
  have h13 : (2 : ℝ) ^ (1 / 3 : ℝ) ≤ 2 :=
    calc (2 : ℝ) ^ (1 / 3 : ℝ)
        ≤ (2 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 2 := Real.rpow_one 2
  calc (2 : ℝ) ^ ((n : ℝ) / 3) * (2 : ℝ) ^ (1 / 3 : ℝ)
      ≤ (2 : ℝ) ^ ((n : ℝ) / 3) * 2 :=
        mul_le_mul_of_nonneg_left h13 hpos.le
    _ = 2 * 2 ^ ((n : ℝ) / 3) := by ring

end JSP000728
