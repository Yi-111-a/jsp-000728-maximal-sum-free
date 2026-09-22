import JSPProblem.BMSContainer
import JSPProblem.FiberWalk
import JSPProblem.IntervalTypeCount
import JSPProblem.AsymptoticReduction
import JSPProblem.UpperBound

/-!
# JSP-000728 — the `3/8` bound: `log₂ f(n) / n ≤ 3/8 + ε`

This file assembles an **unconditional** `EventualRatioUpper (3/8)`, improving
the `1/2` bound of `ContainerHalf.eventualRatioUpper_half`.  The improvement
comes from counting maximal sum-free sets *inside* each container instead of
bounding them by `2^{|C|}`.

## Per-container count

Split a container `C ⊆ {1,…,n}` into its halves (`FiberWalk.lowHalf`,
`FiberWalk.upHalf`):

* `lowHalf n C = C ∩ [1, n/2]` — the *fingerprint* side: at most
  `2^{|low|}` traces `M ∩ low`.
* `upHalf n C = C ∩ (n/2, n]` — the *link-graph* side.  The trace `M ∩ up`
  is a maximal link-independent set in `up`
  (`linkMaxIndepSet_inter_of_isMaxSumFree`), and `up` is sum-free (two of
  its elements sum to more than `n`), so Hujter–Tuza
  (`card_linkMaxSets_le_two_rpow`) gives `≤ 2^{|up|/2}` continuations.

Hence `#{M ∈ maxSumFreeSets n : M ⊆ C} ≤ 2^{|low| + |up|/2}`
(`card_maxSumFreeSets_filter_subset_le`), the same gluing pattern as
`IntervalTypeCount.intervalTypeSets_card_le`.

## The exponent

The key inequality is `FiberWalk.two_mul_card_lowHalf_add_card_upHalf_le`:
`2|low| + |up| = |low| + |C| ≤ 3n/4 + 1 + √(2·T)`, proved by applying the
prefix record bound at `m = n/2` and at `m = n`.  Its sparse form
(`two_mul_card_lowHalf_add_card_upHalf_le_of_schurTripleCount_le`) gives
`2|low| + |up| ≤ (3/4 + ε)·n`, hence the per-container exponent

    `|low| + |up|/2 = (2|low| + |up|)/2 ≤ (3/8 + ε/2)·n`.

(This is tight: for `C =` odds, `|low| = |up| = n/4` and the exponent is
exactly `3n/8`.)

A container family of size `≤ 2^{ε·n}` (`BMSContainer.containerExistence`)
then yields `f(n) ≤ 2^{(3/8 + o(1))·n}`, i.e. `EventualRatioUpper (3/8)`.
-/

namespace JSP000728

/-- The upper half is contained in `{1,…,n}`. -/
theorem upHalf_subset_interval {n : ℕ} {C : Finset ℤ} (hC : C ⊆ interval n) :
    upHalf n C ⊆ interval n :=
  Finset.inter_subset_left.trans hC

/-- The upper half is sum-free: two of its elements exceed `n/2`, so their
sum exceeds `n`. -/
theorem isSumFree_upHalf {n : ℕ} {C : Finset ℤ} : IsSumFree (upHalf n C) := by
  intro x hx y hy hxy
  obtain ⟨hx1, -⟩ := Finset.mem_Icc.1 (Finset.mem_inter.1 hx).2
  obtain ⟨hy1, -⟩ := Finset.mem_Icc.1 (Finset.mem_inter.1 hy).2
  obtain ⟨-, hz2⟩ := Finset.mem_Icc.1 (Finset.mem_inter.1 hxy).2
  omega

/-- Every element of the upper half exceeds `n/2`. -/
theorem upHalf_mem_lt_two_mul {n : ℕ} {C : Finset ℤ} {x : ℤ}
    (hx : x ∈ upHalf n C) : (n : ℤ) < 2 * x := by
  obtain ⟨hx1, -⟩ := Finset.mem_Icc.1 (Finset.mem_inter.1 hx).2
  omega

/-- `C ⊆ {1,…,n}` is covered by its two halves. -/
theorem C_subset_upHalf_union_lowHalf {n : ℕ} {C : Finset ℤ}
    (hC : C ⊆ interval n) : C ⊆ upHalf n C ∪ lowHalf n C := by
  intro x hx
  obtain ⟨hx1, hx2⟩ := Finset.mem_Icc.1 (hC hx)
  rcases le_or_gt x ((n : ℤ) / 2) with h | h
  · exact Finset.mem_union.2 (Or.inr (Finset.mem_inter.2
      ⟨hx, Finset.mem_Icc.2 ⟨hx1, h⟩⟩))
  · exact Finset.mem_union.2 (Or.inl (Finset.mem_inter.2
      ⟨hx, Finset.mem_Icc.2 ⟨by omega, hx2⟩⟩))

/-- **Per-container count**: a container `C ⊆ {1,…,n}` houses at most
`2^{|low| + |up|/2}` maximal sum-free sets, where `low = C ∩ [1, n/2]` and
`up = C ∩ (n/2, n]`: `2^{|low|}` fingerprints `M ∩ low`, each with at most
`2^{|up|/2}` maximal link-independent continuations `M ∩ up` (Hujter–Tuza on
the sum-free ground `up`). -/
theorem card_maxSumFreeSets_filter_subset_le {n : ℕ} {C : Finset ℤ}
    (hC : C ⊆ interval n) :
    (((maxSumFreeSets n).filter (· ⊆ C)).card : ℝ) ≤
      (2 : ℝ) ^ (((lowHalf n C).card : ℝ) +
        ((upHalf n C).card : ℝ) / 2) := by
  classical
  have hAsf : IsSumFree (upHalf n C) := isSumFree_upHalf
  have hAI : upHalf n C ⊆ interval n := upHalf_subset_interval hC
  have hsub : (maxSumFreeSets n).filter (· ⊆ C) ⊆
      (maxSumFreeSets n).filter (· ⊆ upHalf n C ∪ lowHalf n C) := by
    intro M hM
    rw [Finset.mem_filter] at hM ⊢
    exact ⟨hM.1, hM.2.trans (C_subset_upHalf_union_lowHalf hC)⟩
  have hsigma :=
    card_maxSumFreeSets_filter_union_le_sum_linkMaxSets_filter_isSumFree
      (A := upHalf n C) (B := lowHalf n C) hAI hAsf
  have hcard : ((maxSumFreeSets n).filter (· ⊆ C)).card ≤
      ∑ S ∈ (lowHalf n C).powerset.filter IsSumFree,
        (linkMaxSets S (upHalf n C)).card :=
    (Finset.card_le_card hsub).trans hsigma
  have hreal : (((maxSumFreeSets n).filter (· ⊆ C)).card : ℝ) ≤
      ∑ S ∈ (lowHalf n C).powerset.filter IsSumFree,
        ((linkMaxSets S (upHalf n C)).card : ℝ) := by
    exact_mod_cast hcard
  have hbound : ∀ S ∈ (lowHalf n C).powerset.filter IsSumFree,
      ((linkMaxSets S (upHalf n C)).card : ℝ) ≤
        (2 : ℝ) ^ (((upHalf n C).card : ℝ) / 2) := by
    intro S hS
    obtain ⟨hSpow, hSsf⟩ := Finset.mem_filter.1 hS
    have hSsub : S ⊆ interval n :=
      (Finset.mem_powerset.1 hSpow).trans
        (Finset.inter_subset_left.trans hC)
    refine card_linkMaxSets_le_two_rpow hSsub hSsf ?_
    intro x hx
    exact upHalf_mem_lt_two_mul hx
  calc (((maxSumFreeSets n).filter (· ⊆ C)).card : ℝ)
      ≤ _ := hreal
    _ ≤ ∑ _S ∈ (lowHalf n C).powerset.filter IsSumFree,
          (2 : ℝ) ^ (((upHalf n C).card : ℝ) / 2) :=
        Finset.sum_le_sum hbound
    _ = (((lowHalf n C).powerset.filter IsSumFree).card : ℝ) *
          (2 : ℝ) ^ (((upHalf n C).card : ℝ) / 2) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 : ℝ) ^ ((lowHalf n C).card : ℝ) *
          (2 : ℝ) ^ (((upHalf n C).card : ℝ) / 2) := by
        refine mul_le_mul_of_nonneg_right ?_
          (Real.rpow_nonneg (by norm_num) _)
        have hle := Finset.card_le_card
          (Finset.filter_subset IsSumFree (lowHalf n C).powerset)
        rw [Finset.card_powerset] at hle
        exact_mod_cast hle
    _ = (2 : ℝ) ^ (((lowHalf n C).card : ℝ) +
          ((upHalf n C).card : ℝ) / 2) := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]

/-- **Unconditional `3/8` bound.**  A container family of size `≤ 2^{(ε/8)n}`
whose members each have `≤ δ·n²` Schur triples (`δ` from the sparse form of
`2|low| + |up| ≤ 3n/4`) gives, per container, at most
`2^{|low| + |up|/2} ≤ 2^{(3/8 + ε/32)n}` maximal sum-free sets, hence
`f(n) ≤ 2^{(3/8 + 5ε/32)·n}` and `log₂ f(n)/n ≤ 3/8 + ε` eventually. -/
theorem eventualRatioUpper_three_eighths : EventualRatioUpper (3 / 8) := by
  intro ε hε
  have hε16 : 0 < ε / 16 := by linarith
  obtain ⟨δ, hδ, hcomb⟩ :=
    two_mul_card_lowHalf_add_card_upHalf_le_of_schurTripleCount_le hε16
  have hε8 : 0 < ε / 8 := by linarith
  have hcont := containerExistence (ε / 8) hε8 δ hδ
  filter_upwards [hcomb, hcont, Filter.eventually_ge_atTop 1]
    with n hcn hcontn hn1
  obtain ⟨F, hFfam, hFcard, hFtr⟩ := hcontn
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have h2pos : (0 : ℝ) < 2 := by norm_num
  -- Per-container exponent: `|low| + |up|/2 = (2|low| + |up|)/2 ≤ (3/8 + ε/32)·n`.
  have hE : ∀ C ∈ F, ((lowHalf n C).card : ℝ) +
      ((upHalf n C).card : ℝ) / 2 ≤ (3 / 8 + ε / 32) * (n : ℝ) := by
    intro C hCmem
    have h := hcn C (hFfam.1 C hCmem) (hFtr C hCmem)
    linarith
  -- Cover: every maximal sum-free `M` sits in some `C ∈ F`.
  have hcover : maxSumFreeSets n ⊆
      F.biUnion fun C => (maxSumFreeSets n).filter (· ⊆ C) := by
    intro M hM
    have hMmax := mem_maxSumFreeSets.1 hM
    obtain ⟨C, hCF, hMC⟩ := hFfam.2 M hMmax.1 hMmax.2.1
    rw [Finset.mem_biUnion]
    exact ⟨C, hCF, Finset.mem_filter.2 ⟨hM, hMC⟩⟩
  have hcountℕ : maxSumFreeCount n ≤
      ∑ C ∈ F, ((maxSumFreeSets n).filter (· ⊆ C)).card :=
    (Finset.card_le_card hcover).trans Finset.card_biUnion_le
  -- Per-container real bound.
  have hper : ∀ C ∈ F,
      (((maxSumFreeSets n).filter (· ⊆ C)).card : ℝ) ≤
        (2 : ℝ) ^ ((3 / 8 + ε / 32) * (n : ℝ)) := by
    intro C hCmem
    exact (card_maxSumFreeSets_filter_subset_le (hFfam.1 C hCmem)).trans
      (Real.rpow_le_rpow_of_exponent_le (by norm_num) (hE C hCmem))
  have hcount : (maxSumFreeCount n : ℝ) ≤
      (F.card : ℝ) * (2 : ℝ) ^ ((3 / 8 + ε / 32) * (n : ℝ)) := by
    calc (maxSumFreeCount n : ℝ)
        ≤ ((∑ C ∈ F, ((maxSumFreeSets n).filter (· ⊆ C)).card : ℕ) : ℝ) := by
          exact_mod_cast hcountℕ
      _ = ∑ C ∈ F, (((maxSumFreeSets n).filter (· ⊆ C)).card : ℝ) := by
          push_cast; rfl
      _ ≤ ∑ _C ∈ F, (2 : ℝ) ^ ((3 / 8 + ε / 32) * (n : ℝ)) :=
          Finset.sum_le_sum hper
      _ = (F.card : ℝ) * (2 : ℝ) ^ ((3 / 8 + ε / 32) * (n : ℝ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  -- Total: `f(n) ≤ 2^{(ε/8)n} · 2^{(3/8 + ε/32)n} = 2^{(3/8 + 5ε/32)n}`.
  have hbound : (maxSumFreeCount n : ℝ) ≤
      (2 : ℝ) ^ ((3 / 8 + 5 * ε / 32) * (n : ℝ)) := by
    calc (maxSumFreeCount n : ℝ)
        ≤ (F.card : ℝ) * (2 : ℝ) ^ ((3 / 8 + ε / 32) * (n : ℝ)) :=
          hcount
      _ ≤ (2 : ℝ) ^ ((ε / 8) * (n : ℝ)) *
            (2 : ℝ) ^ ((3 / 8 + ε / 32) * (n : ℝ)) :=
          mul_le_mul_of_nonneg_right hFcard
            (Real.rpow_nonneg h2pos.le _)
      _ = (2 : ℝ) ^ ((ε / 8) * (n : ℝ) +
            (3 / 8 + ε / 32) * (n : ℝ)) := by
          rw [← Real.rpow_add h2pos]
      _ = (2 : ℝ) ^ ((3 / 8 + 5 * ε / 32) * (n : ℝ)) := by
          congr 1; ring
  -- Take `log₂` and divide by `n ≥ 1`.
  have hpos : (0 : ℝ) < (maxSumFreeCount n : ℝ) := by
    exact_mod_cast maxSumFreeCount_pos n
  have hlog : Real.logb 2 (maxSumFreeCount n : ℝ) ≤
      (3 / 8 + 5 * ε / 32) * (n : ℝ) := by
    calc Real.logb 2 (maxSumFreeCount n : ℝ)
        ≤ Real.logb 2 ((2 : ℝ) ^ ((3 / 8 + 5 * ε / 32) * (n : ℝ))) :=
          (Real.logb_le_logb (by norm_num) hpos
            (Real.rpow_pos_of_pos h2pos _)).mpr hbound
      _ = (3 / 8 + 5 * ε / 32) * (n : ℝ) :=
          Real.logb_rpow h2pos (by norm_num : (2 : ℝ) ≠ 1)
  calc Real.logb 2 (maxSumFreeCount n : ℝ) / (n : ℝ)
      ≤ ((3 / 8 + 5 * ε / 32) * (n : ℝ)) / (n : ℝ) :=
        div_le_div_of_nonneg_right hlog hnR.le
    _ = 3 / 8 + 5 * ε / 32 := by
        rw [mul_div_cancel_right₀ _ hnR.ne']
    _ ≤ 3 / 8 + ε := by linarith

end JSP000728
