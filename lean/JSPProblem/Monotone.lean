import JSPProblem.Extend

/-!
# JSP-000728 — monotonicity of `maxSumFreeCount`

The number `maxSumFreeCount n` of inclusion-maximal sum-free subsets of
`{1, …, n}` is nondecreasing in `n`.

The proof injects `maxSumFreeSets n` into `maxSumFreeSets (n + 1)` by sending
each maximal sum-free `M ⊆ {1, …, n}` to a chosen maximal sum-free extension
`maxExt (n + 1) M ⊆ {1, …, n + 1}`.  Injectivity: if two sets `M₁`, `M₂` have
the same extension `M*`, then `M* ∩ {1, …, n}` is a sum-free subset of
`{1, …, n}` containing `Mᵢ`, so maximality of `Mᵢ` forces
`Mᵢ = M* ∩ {1, …, n}`, hence `M₁ = M₂`.

* `interval_subset_interval_succ` : `{1, …, n} ⊆ {1, …, n + 1}`.
* `maxSumFreeCount_le_succ` : `maxSumFreeCount n ≤ maxSumFreeCount (n + 1)`.
* `monotone_maxSumFreeCount` : `Monotone maxSumFreeCount`.
* `maxSumFreeCount_le_of_le` : the same, uncurried.
-/

namespace JSP000728

/-- The interval `{1, …, n}` sits inside `{1, …, n + 1}`. -/
theorem interval_subset_interval_succ (n : ℕ) :
    interval n ⊆ interval (n + 1) := by
  refine Finset.Icc_subset_Icc le_rfl ?_
  exact_mod_cast Nat.le_succ n

/-- Cutting back a maximal extension to `{1, …, n}` recovers the original
maximal sum-free set — the key step for injectivity. -/
theorem maxExt_inter_interval_eq {n : ℕ} {M : Finset ℤ}
    (hM : IsMaxSumFree n M) :
    maxExt (n + 1) M ∩ interval n = M := by
  have hmaximal := isMaxSumFree_iff_isMaximalSumFree.mp hM
  obtain ⟨hMn, hMsf, -⟩ := hM
  have hsub : M ⊆ interval (n + 1) :=
    hMn.trans (interval_subset_interval_succ n)
  obtain ⟨hle, hmax⟩ := maxExt_spec hsub hMsf
  exact le_antisymm
    (hmaximal.2.2 _ Finset.inter_subset_right
      (hmax.2.1.mono Finset.inter_subset_left)
      (Finset.subset_inter hle hMn))
    (Finset.subset_inter hle hMn)

/-- `maxSumFreeCount` grows from `n` to `n + 1`: the extension map
`M ↦ maxExt (n + 1) M` injects `maxSumFreeSets n` into
`maxSumFreeSets (n + 1)`. -/
theorem maxSumFreeCount_le_succ (n : ℕ) :
    maxSumFreeCount n ≤ maxSumFreeCount (n + 1) := by
  show (maxSumFreeSets n).card ≤ (maxSumFreeSets (n + 1)).card
  refine Finset.card_le_card_of_injOn (fun M => maxExt (n + 1) M) ?_ ?_
  · intro M hM
    obtain ⟨hMn, hMsf, -⟩ := mem_maxSumFreeSets.mp hM
    exact maxExt_mem (hMn.trans (interval_subset_interval_succ n)) hMsf
  · intro M₁ hM₁ M₂ hM₂ hEq
    calc M₁ = maxExt (n + 1) M₁ ∩ interval n :=
          (maxExt_inter_interval_eq
            (mem_maxSumFreeSets.mp (Finset.mem_coe.mp hM₁))).symm
      _ = maxExt (n + 1) M₂ ∩ interval n := congrArg (· ∩ interval n) hEq
      _ = M₂ :=
          maxExt_inter_interval_eq
            (mem_maxSumFreeSets.mp (Finset.mem_coe.mp hM₂))

/-- `maxSumFreeCount` is nondecreasing in `n`. -/
theorem monotone_maxSumFreeCount : Monotone maxSumFreeCount := by
  intro m n hmn
  induction hmn with
  | refl => exact le_refl _
  | step _ ih => exact le_trans ih (maxSumFreeCount_le_succ _)

/-- Unfolded form of `monotone_maxSumFreeCount`. -/
theorem maxSumFreeCount_le_of_le {m n : ℕ} (h : m ≤ n) :
    maxSumFreeCount m ≤ maxSumFreeCount n :=
  monotone_maxSumFreeCount h

end JSP000728
