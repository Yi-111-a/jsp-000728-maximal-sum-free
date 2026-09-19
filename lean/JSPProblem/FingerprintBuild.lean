import JSPProblem.MoonMoser
import JSPProblem.Removal
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# JSP-000728 — the fingerprint + link-MIS counting interface

This file packages the *fingerprint determination* of maximal sum-free sets
into the per-container counting scaffold that the BLST18 kernel needs.

## Recovery layer

* `maxSumFree_eq_fingerprint_union` — in the regime `n < 2(K+1)` (where the
  link-maximality transfer `linkMax_indep_of_isMaxSumFree_of_lt` applies
  unconditionally), every `M ∈ maxSumFreeSets n` is recovered from its
  fingerprint `M ∩ [1,K]` and its trace `M ∩ {K+1,…,n}`, and the trace is a
  *maximal link-independent* set.
* `linkMaxIndepSet.mono` — maximal link-independence in `B` restricts to any
  `B' ⊆ B` still containing `t`.
* `linkMax_indep_of_isMaxSumFree_of_lt_in`,
  `maxSumFree_eq_fingerprint_union_in` — the per-container refinement: the
  trace is link-maximal inside `C ∩ {K+1,…,n}` whenever `M ⊆ C`.

## Counting layer

* `fingerprint_injOn` — the map `M ↦ (M ∩ [1,K], M ∩ {K+1,…,n})` is injective
  on subsets of `interval n`.
* `maxSumFreeCount_le_sum_linkMaxSets` — `f(n)` is at most the total number
  of maximal link-independent sets over all fingerprints `S ⊆ [1,K]`
  (injectivity into the `Finset.sigma` of fingerprint/link-MIS pairs).
* `card_maxSumFreeSets_filter_le_sum_linkMaxSets` — the per-container
  version bounding `#{M ∈ maxSumFreeSets n : M ⊆ C}`.

## Moon–Moser assembly

* `maxSumFreeCount_le_two_pow_mul_three_rpow` —
  `f(n) ≤ 2^{|Icc 1 K|} · 3^{|Icc (K+1) n|/3}` (cardinal form).
* `maxSumFreeCount_le_pow_link` — the clean form
  `f(n) ≤ 2^K · 3^{(n−K)/3}` valid for `0 ≤ K ≤ n < 2(K+1)`.
* `card_maxSumFreeSets_filter_le_two_pow_mul_three_rpow(_card)` —
  per-container versions; note the exponent is driven by
  `|C ∩ {K+1,…,n}|`, which is where sparse containers win.

## The sparse fingerprint hypothesis

* `SparseFingerprintBound` — the honest weakening of `FingerprintBound`:
  for every `ε > 0` there is a `δ > 0` such that, eventually, the
  per-container bound `≤ 2^{(1/4+ε)n}` is required **only** for containers
  `C ⊆ interval n` with `schurTripleCount C ≤ δ·n²`.  This is the true
  mathematical content of BLST18's fingerprint counting: the ambient
  interval is *not* sparse (`schurTripleCount_interval_ge` gives
  `≥ n(n−1)/2` Schur triples), so `FingerprintBound` — which quantifies
  over `C = interval n` — already presupposes the full count.
* `sparseFingerprintBound_of_fingerprintBound` — the trivial direction.
* `maxContainerBound_of_containerExistence_sparseFingerprint` — container
  existence supplies sparse containers (each `C ∈ F` has
  `schurTripleCount C ≤ δ n²`), so the sparse fingerprint bound applies to
  exactly the containers that matter.
* `sharpAsymptotic_of_sparse_container_fingerprint` — the sharpened prize
  reduction: `ContainerExistence → SparseFingerprintBound → SharpAsymptotic`.
-/

namespace JSP000728

/-! ## Recovery -/

/-- **Fingerprint recovery.**  For `n < 2(K+1)` every maximal sum-free
`M ⊆ {1,…,n}` satisfies `M = (M ∩ [1,K]) ∪ (M ∩ {K+1,…,n})`, and the upper
trace is a maximal link-independent subset of `B = {K+1,…,n}` for the link
graph of the fingerprint `S = M ∩ [1,K]`. -/
theorem maxSumFree_eq_fingerprint_union {n : ℕ} {M : Finset ℤ} {K : ℤ}
    (hM : M ∈ maxSumFreeSets n) (hK : (n : ℤ) < 2 * (K + 1)) :
    M = M ∩ Finset.Icc 1 K ∪ M ∩ Finset.Icc (K + 1) (n : ℤ) ∧
      M ∩ Finset.Icc (K + 1) (n : ℤ) ∈
        linkMaxSets (M ∩ Finset.Icc 1 K) (Finset.Icc (K + 1) (n : ℤ)) := by
  have hMmax : IsMaxSumFree n M := mem_maxSumFreeSets.mp hM
  exact ⟨(inter_Icc_union_inter_Icc hMmax.1).symm,
    mem_linkMaxSets.mpr ⟨Finset.inter_subset_right,
      linkMax_indep_of_isMaxSumFree_of_lt hMmax hK⟩⟩

/-- **Monotonicity of maximal link-independence in the ground set.**  A
maximal link-independent `t` of `B` stays maximal inside any intermediate
`B'` with `t ⊆ B' ⊆ B`: independence is intrinsic, and domination of
`B ∖ t` a fortiori dominates `B' ∖ t`. -/
theorem linkMaxIndepSet.mono {S B B' t : Finset ℤ} (h : linkMaxIndepSet S B t)
    (htB' : t ⊆ B') (hB' : B' ⊆ B) : linkMaxIndepSet S B' t :=
  ⟨htB', h.2.1, fun x hx hxt => h.2.2 x (hB' hx) hxt⟩

/-- **Per-container maximality transfer.**  For `M ⊆ C` maximal sum-free
and `n < 2(K+1)`, the trace `M ∩ {K+1,…,n}` is a maximal link-independent
subset of the *container's* upper part `C ∩ {K+1,…,n}`. -/
theorem linkMax_indep_of_isMaxSumFree_of_lt_in {n : ℕ} {M C : Finset ℤ}
    {K : ℤ} (hM : IsMaxSumFree n M) (hMC : M ⊆ C)
    (hK : (n : ℤ) < 2 * (K + 1)) :
    linkMaxIndepSet (M ∩ Finset.Icc 1 K) (C ∩ Finset.Icc (K + 1) (n : ℤ))
      (M ∩ Finset.Icc (K + 1) (n : ℤ)) :=
  (linkMax_indep_of_isMaxSumFree_of_lt hM hK).mono
    (fun _x hx => Finset.mem_inter.mpr
      ⟨hMC (Finset.mem_inter.mp hx).1, (Finset.mem_inter.mp hx).2⟩)
    Finset.inter_subset_right

/-- **Per-container fingerprint recovery.** -/
theorem maxSumFree_eq_fingerprint_union_in {n : ℕ} {M C : Finset ℤ} {K : ℤ}
    (hM : M ∈ maxSumFreeSets n) (hMC : M ⊆ C) (hK : (n : ℤ) < 2 * (K + 1)) :
    M = M ∩ Finset.Icc 1 K ∪ M ∩ Finset.Icc (K + 1) (n : ℤ) ∧
      M ∩ Finset.Icc (K + 1) (n : ℤ) ∈
        linkMaxSets (M ∩ Finset.Icc 1 K)
          (C ∩ Finset.Icc (K + 1) (n : ℤ)) := by
  have hMmax : IsMaxSumFree n M := mem_maxSumFreeSets.mp hM
  refine ⟨(inter_Icc_union_inter_Icc hMmax.1).symm, mem_linkMaxSets.mpr ⟨?_,
    linkMax_indep_of_isMaxSumFree_of_lt_in hMmax hMC hK⟩⟩
  intro x hx
  rw [Finset.mem_inter] at hx ⊢
  exact ⟨hMC hx.1, hx.2⟩

/-! ## Injectivity and counting -/

/-- **The fingerprint map is injective** on subsets of `interval n`: `M` is
recovered as the union of its two traces. -/
theorem fingerprint_injOn {n : ℕ} {K : ℤ} :
    Set.InjOn
      (fun M : Finset ℤ =>
        (M ∩ Finset.Icc 1 K, M ∩ Finset.Icc (K + 1) (n : ℤ)))
      ↑(interval n).powerset := by
  intro M hM M' hM' heq
  have e := inter_Icc_union_inter_Icc (K := K)
    (Finset.mem_powerset.mp (Finset.mem_coe.mp hM))
  have e' := inter_Icc_union_inter_Icc (K := K)
    (Finset.mem_powerset.mp (Finset.mem_coe.mp hM'))
  have h1 : M ∩ Finset.Icc 1 K = M' ∩ Finset.Icc 1 K :=
    congrArg Prod.fst heq
  have h2 : M ∩ Finset.Icc (K + 1) (n : ℤ) =
      M' ∩ Finset.Icc (K + 1) (n : ℤ) := congrArg Prod.snd heq
  calc M = M ∩ Finset.Icc 1 K ∪ M ∩ Finset.Icc (K + 1) (n : ℤ) := e.symm
    _ = M' ∩ Finset.Icc 1 K ∪ M' ∩ Finset.Icc (K + 1) (n : ℤ) := by
        rw [h1, h2]
    _ = M' := e'

/-- **Counting through the fingerprint/link-MIS sigma.**  The map
`M ↦ (M ∩ [1,K], M ∩ {K+1,…,n})` injects `maxSumFreeSets n` into the sigma
type of pairs `(S, t)` with `S ⊆ [1,K]` and `t ∈ linkMaxSets S {K+1,…,n}`,
giving `f(n) ≤ Σ_{S ⊆ [1,K]} |linkMaxSets S {K+1,…,n}|`. -/
theorem maxSumFreeCount_le_sum_linkMaxSets {n : ℕ} {K : ℤ}
    (hK : (n : ℤ) < 2 * (K + 1)) :
    maxSumFreeCount n ≤
      ∑ S ∈ (Finset.Icc 1 K).powerset,
        (linkMaxSets S (Finset.Icc (K + 1) (n : ℤ))).card := by
  classical
  have him : ∀ M ∈ maxSumFreeSets n,
      (⟨M ∩ Finset.Icc 1 K, M ∩ Finset.Icc (K + 1) (n : ℤ)⟩ :
          Σ _ : Finset ℤ, Finset ℤ) ∈
        (Finset.Icc 1 K).powerset.sigma
          fun S => linkMaxSets S (Finset.Icc (K + 1) (n : ℤ)) := by
    intro M hM
    have hMmax := mem_maxSumFreeSets.mp hM
    rw [Finset.mem_sigma]
    exact ⟨Finset.mem_powerset.mpr Finset.inter_subset_right,
      mem_linkMaxSets.mpr ⟨Finset.inter_subset_right,
        linkMax_indep_of_isMaxSumFree_of_lt hMmax hK⟩⟩
  have hinj : Set.InjOn
      (fun M : Finset ℤ =>
        (⟨M ∩ Finset.Icc 1 K, M ∩ Finset.Icc (K + 1) (n : ℤ)⟩ :
          Σ _ : Finset ℤ, Finset ℤ))
      ↑(maxSumFreeSets n) := by
    intro M hM M' hM' heq
    have e := inter_Icc_union_inter_Icc (K := K)
      (mem_maxSumFreeSets.mp (Finset.mem_coe.mp hM)).1
    have e' := inter_Icc_union_inter_Icc (K := K)
      (mem_maxSumFreeSets.mp (Finset.mem_coe.mp hM')).1
    have h1 : M ∩ Finset.Icc 1 K = M' ∩ Finset.Icc 1 K :=
      congrArg Sigma.fst heq
    have h2 : M ∩ Finset.Icc (K + 1) (n : ℤ) =
        M' ∩ Finset.Icc (K + 1) (n : ℤ) := congrArg Sigma.snd heq
    calc M = M ∩ Finset.Icc 1 K ∪ M ∩ Finset.Icc (K + 1) (n : ℤ) := e.symm
      _ = M' ∩ Finset.Icc 1 K ∪ M' ∩ Finset.Icc (K + 1) (n : ℤ) := by
          rw [h1, h2]
      _ = M' := e'
  calc maxSumFreeCount n = (maxSumFreeSets n).card := rfl
    _ ≤ ((Finset.Icc 1 K).powerset.sigma
          fun S => linkMaxSets S (Finset.Icc (K + 1) (n : ℤ))).card :=
        Finset.card_le_card_of_injOn _ him hinj
    _ = ∑ S ∈ (Finset.Icc 1 K).powerset,
          (linkMaxSets S (Finset.Icc (K + 1) (n : ℤ))).card :=
        Finset.card_sigma _ _

/-- **Per-container counting.**  The same fingerprint map injects the
maximal sum-free sets housed by `C` into the sigma type of pairs `(S, t)`
with `S ⊆ [1,K]` and `t ∈ linkMaxSets S (C ∩ {K+1,…,n})`:
`#{M ∈ maxSumFreeSets n : M ⊆ C} ≤ Σ_{S ⊆ [1,K]} |linkMaxSets S (C∩B)|`. -/
theorem card_maxSumFreeSets_filter_le_sum_linkMaxSets {n : ℕ} (C : Finset ℤ)
    {K : ℤ} (hK : (n : ℤ) < 2 * (K + 1)) :
    ((maxSumFreeSets n).filter (· ⊆ C)).card ≤
      ∑ S ∈ (Finset.Icc 1 K).powerset,
        (linkMaxSets S (C ∩ Finset.Icc (K + 1) (n : ℤ))).card := by
  classical
  have him : ∀ M ∈ (maxSumFreeSets n).filter (· ⊆ C),
      (⟨M ∩ Finset.Icc 1 K, M ∩ Finset.Icc (K + 1) (n : ℤ)⟩ :
          Σ _ : Finset ℤ, Finset ℤ) ∈
        (Finset.Icc 1 K).powerset.sigma
          fun S => linkMaxSets S (C ∩ Finset.Icc (K + 1) (n : ℤ)) := by
    intro M hM
    obtain ⟨hMmem, hMC⟩ := Finset.mem_filter.mp hM
    have hMmax := mem_maxSumFreeSets.mp hMmem
    rw [Finset.mem_sigma]
    refine ⟨Finset.mem_powerset.mpr Finset.inter_subset_right, ?_⟩
    rw [mem_linkMaxSets]
    refine ⟨?_, linkMax_indep_of_isMaxSumFree_of_lt_in hMmax hMC hK⟩
    intro x hx
    rw [Finset.mem_inter] at hx ⊢
    exact ⟨hMC hx.1, hx.2⟩
  have hinj : Set.InjOn
      (fun M : Finset ℤ =>
        (⟨M ∩ Finset.Icc 1 K, M ∩ Finset.Icc (K + 1) (n : ℤ)⟩ :
          Σ _ : Finset ℤ, Finset ℤ))
      ↑((maxSumFreeSets n).filter (· ⊆ C)) := by
    intro M hM M' hM' heq
    have e := inter_Icc_union_inter_Icc (K := K)
      (mem_maxSumFreeSets.mp
        (Finset.mem_filter.mp (Finset.mem_coe.mp hM)).1).1
    have e' := inter_Icc_union_inter_Icc (K := K)
      (mem_maxSumFreeSets.mp
        (Finset.mem_filter.mp (Finset.mem_coe.mp hM')).1).1
    have h1 : M ∩ Finset.Icc 1 K = M' ∩ Finset.Icc 1 K :=
      congrArg Sigma.fst heq
    have h2 : M ∩ Finset.Icc (K + 1) (n : ℤ) =
        M' ∩ Finset.Icc (K + 1) (n : ℤ) := congrArg Sigma.snd heq
    calc M = M ∩ Finset.Icc 1 K ∪ M ∩ Finset.Icc (K + 1) (n : ℤ) := e.symm
      _ = M' ∩ Finset.Icc 1 K ∪ M' ∩ Finset.Icc (K + 1) (n : ℤ) := by
          rw [h1, h2]
      _ = M' := e'
  calc ((maxSumFreeSets n).filter (· ⊆ C)).card
      ≤ ((Finset.Icc 1 K).powerset.sigma
          fun S => linkMaxSets S (C ∩ Finset.Icc (K + 1) (n : ℤ))).card :=
        Finset.card_le_card_of_injOn _ him hinj
    _ = ∑ S ∈ (Finset.Icc 1 K).powerset,
          (linkMaxSets S (C ∩ Finset.Icc (K + 1) (n : ℤ))).card :=
        Finset.card_sigma _ _

/-! ## Moon–Moser assembly -/

/-- **Assembled fingerprint × Moon–Moser bound** (cardinal form): in the
regime `n < 2(K+1)`, `f(n) ≤ |𝒫([1,K])| · 3^{|{K+1,…,n}|/3}
= 2^{K.toNat} · 3^{|{K+1,…,n}|/3}`. -/
theorem maxSumFreeCount_le_two_pow_mul_three_rpow {n : ℕ} {K : ℤ}
    (hK : (n : ℤ) < 2 * (K + 1)) :
    (maxSumFreeCount n : ℝ) ≤
      2 ^ K.toNat *
        (3 : ℝ) ^ (((Finset.Icc (K + 1) (n : ℤ)).card : ℝ) / 3) := by
  have hsum := maxSumFreeCount_le_sum_linkMaxSets hK
  have hreal : (maxSumFreeCount n : ℝ) ≤
      ∑ S ∈ (Finset.Icc 1 K).powerset,
        ((linkMaxSets S (Finset.Icc (K + 1) (n : ℤ))).card : ℝ) := by
    exact_mod_cast hsum
  calc (maxSumFreeCount n : ℝ)
      ≤ ∑ S ∈ (Finset.Icc 1 K).powerset,
          ((linkMaxSets S (Finset.Icc (K + 1) (n : ℤ))).card : ℝ) := hreal
    _ ≤ ∑ _S ∈ (Finset.Icc 1 K).powerset,
          (3 : ℝ) ^ (((Finset.Icc (K + 1) (n : ℤ)).card : ℝ) / 3) :=
        Finset.sum_le_sum fun S _ => card_linkMaxSets_le_three_rpow _ _
    _ = ((Finset.Icc 1 K).powerset.card : ℝ) *
          (3 : ℝ) ^ (((Finset.Icc (K + 1) (n : ℤ)).card : ℝ) / 3) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = 2 ^ K.toNat *
          (3 : ℝ) ^ (((Finset.Icc (K + 1) (n : ℤ)).card : ℝ) / 3) := by
        congr 1
        rw [Finset.card_powerset, Int.card_Icc,
          show (K : ℤ) + 1 - 1 = K from by ring]
        norm_cast

/-- **Assembled bound, clean form.**  For `0 ≤ K ≤ n < 2(K+1)`:
`f(n) ≤ 2^K · 3^{(n−K)/3}` — `2^K` fingerprints times the Moon–Moser
maximal-independent-set bound `3^{|B|/3}` on `B = {K+1,…,n}`. -/
theorem maxSumFreeCount_le_pow_link {n : ℕ} {K : ℤ}
    (hK : (n : ℤ) < 2 * (K + 1)) (hKn : K ≤ (n : ℤ)) :
    (maxSumFreeCount n : ℝ) ≤
      (2 : ℝ) ^ (K : ℝ) * (3 : ℝ) ^ (((n : ℝ) - K) / 3) := by
  have h := maxSumFreeCount_le_two_pow_mul_three_rpow hK
  have hK0 : (0 : ℤ) ≤ K := by omega
  have htoK : (K.toNat : ℝ) = (K : ℝ) := by
    have e : (K.toNat : ℤ) = K := Int.toNat_of_nonneg hK0
    exact_mod_cast e
  have hcardR : ((Finset.Icc (K + 1) (n : ℤ)).card : ℝ) = (n : ℝ) - K := by
    have e : ((Finset.Icc (K + 1) (n : ℤ)).card : ℤ) = (n : ℤ) - K := by
      rw [Int.card_Icc]
      have e2 : ((n : ℤ) + 1 - (K + 1)).toNat = (n : ℤ) - K := by
        rw [show (n : ℤ) + 1 - (K + 1) = (n : ℤ) - K from by ring]
        exact Int.toNat_of_nonneg (by omega)
      exact_mod_cast e2
    have e3 : (((Finset.Icc (K + 1) (n : ℤ)).card : ℤ) : ℝ) =
        ((n : ℤ) - K : ℤ) := congrArg _ e
    rw [Int.cast_natCast, Int.cast_sub, Int.cast_natCast] at e3
    exact e3
  have hpow : (2 : ℝ) ^ K.toNat = (2 : ℝ) ^ (K : ℝ) := by
    rw [← Real.rpow_natCast, htoK]
  calc (maxSumFreeCount n : ℝ)
      ≤ 2 ^ K.toNat *
          (3 : ℝ) ^ (((Finset.Icc (K + 1) (n : ℤ)).card : ℝ) / 3) := h
    _ = (2 : ℝ) ^ (K : ℝ) * (3 : ℝ) ^ (((n : ℝ) - K) / 3) := by
        rw [hpow, hcardR]

/-- **Per-container assembled bound**: the maximal sum-free sets housed by
`C` number at most `2^{K.toNat} · 3^{|C ∩ {K+1,…,n}|/3}`.  The Moon–Moser
factor is driven by the container's upper trace, which is where a sparse
container improves over the ambient interval. -/
theorem card_maxSumFreeSets_filter_le_two_pow_mul_three_rpow {n : ℕ}
    (C : Finset ℤ) {K : ℤ} (hK : (n : ℤ) < 2 * (K + 1)) :
    (((maxSumFreeSets n).filter (· ⊆ C)).card : ℝ) ≤
      2 ^ K.toNat *
        (3 : ℝ) ^ (((C ∩ Finset.Icc (K + 1) (n : ℤ)).card : ℝ) / 3) := by
  have hsum := card_maxSumFreeSets_filter_le_sum_linkMaxSets C hK
  have hreal : (((maxSumFreeSets n).filter (· ⊆ C)).card : ℝ) ≤
      ∑ S ∈ (Finset.Icc 1 K).powerset,
        ((linkMaxSets S (C ∩ Finset.Icc (K + 1) (n : ℤ))).card : ℝ) := by
    exact_mod_cast hsum
  calc (((maxSumFreeSets n).filter (· ⊆ C)).card : ℝ)
      ≤ ∑ S ∈ (Finset.Icc 1 K).powerset,
          ((linkMaxSets S (C ∩ Finset.Icc (K + 1) (n : ℤ))).card : ℝ) :=
        hreal
    _ ≤ ∑ _S ∈ (Finset.Icc 1 K).powerset,
          (3 : ℝ) ^
            (((C ∩ Finset.Icc (K + 1) (n : ℤ)).card : ℝ) / 3) :=
        Finset.sum_le_sum fun S _ => card_linkMaxSets_le_three_rpow _ _
    _ = ((Finset.Icc 1 K).powerset.card : ℝ) *
          (3 : ℝ) ^
            (((C ∩ Finset.Icc (K + 1) (n : ℤ)).card : ℝ) / 3) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = 2 ^ K.toNat *
          (3 : ℝ) ^
            (((C ∩ Finset.Icc (K + 1) (n : ℤ)).card : ℝ) / 3) := by
        congr 1
        rw [Finset.card_powerset, Int.card_Icc,
          show (K : ℤ) + 1 - 1 = K from by ring]
        norm_cast

/-- Coarser per-container form with exponent `|C|/3`. -/
theorem card_maxSumFreeSets_filter_le_two_pow_mul_three_rpow_card {n : ℕ}
    (C : Finset ℤ) {K : ℤ} (hK : (n : ℤ) < 2 * (K + 1)) :
    (((maxSumFreeSets n).filter (· ⊆ C)).card : ℝ) ≤
      2 ^ K.toNat * (3 : ℝ) ^ ((C.card : ℝ) / 3) := by
  refine (card_maxSumFreeSets_filter_le_two_pow_mul_three_rpow C hK).trans ?_
  refine mul_le_mul_of_nonneg_left ?_
    (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) ?_
  have hle : ((C ∩ Finset.Icc (K + 1) (n : ℤ)).card : ℝ) ≤ (C.card : ℝ) := by
    exact_mod_cast Finset.card_le_card Finset.inter_subset_left
  linarith

/-! ## The sparse fingerprint hypothesis -/

/-- **Sparse fingerprint bound** (hypothesis): for every `ε > 0` there is a
`δ > 0` such that, eventually, every container `C ⊆ {1,…,n}` with at most
`δ·n²` Schur triples houses at most `2^{(1/4+ε)n}` maximal sum-free sets.

Unlike `FingerprintBound`, the quantification is restricted to *sparse*
containers.  This is essential: `interval n` itself has at least
`n(n−1)/2` Schur triples (`schurTripleCount_interval_ge`), so for `δ < 1/2`
the ambient interval is not admissible and `SparseFingerprintBound` does
not trivially contain the full count — it is the honest per-container
hypothesis that the container lemma's output feeds into. -/
def SparseFingerprintBound : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n : ℕ in Filter.atTop,
    ∀ C : Finset ℤ, C ⊆ interval n →
      (schurTripleCount C : ℝ) ≤ δ * (n : ℝ) ^ 2 →
      (((maxSumFreeSets n).filter (· ⊆ C)).card : ℝ) ≤
        2 ^ ((1 / 4 + ε) * (n : ℝ))

/-- The trivial direction: the (over-strong) `FingerprintBound`, which
quantifies over *all* `C ⊆ interval n`, implies the sparse version. -/
theorem sparseFingerprintBound_of_fingerprintBound (hFB : FingerprintBound) :
    SparseFingerprintBound := by
  intro ε hε
  exact ⟨1, one_pos, (hFB ε hε).mono fun n hn C hC _ => hn C hC⟩

/-- **Container existence + sparse fingerprint bound ⇒ `MaxContainerBound`.**
The container family supplied by `ContainerExistence` at the `δ` chosen by
`SparseFingerprintBound` consists entirely of `δ n²`-sparse containers, so
the sparse per-container bound applies to every member — this is the point
of the refinement: the fingerprint count is only needed on containers that
are actually sparse. -/
theorem maxContainerBound_of_containerExistence_sparseFingerprint
    (hCE : ContainerExistence) (hSFB : SparseFingerprintBound) :
    MaxContainerBound := by
  intro ε hε
  obtain ⟨δ, hδ, hfp⟩ := hSFB ε hε
  filter_upwards [hCE ε hε δ hδ, hfp] with n hcont hfpn
  obtain ⟨F, hFfam, hFcard, hFtr⟩ := hcont
  refine ⟨F, hFcard, fun M hM => ?_,
    fun C hC => hfpn C (hFfam.1 C hC) (hFtr C hC)⟩
  obtain ⟨hsub, hsf, -⟩ := mem_maxSumFreeSets.mp hM
  exact hFfam.2 M hsub hsf

/-- **Sharpened conditional BLST18 headline.**  Container existence plus the
*sparse* fingerprint bound already imply `log₂ f(n) / n → 1/4`: the
per-container counting only has to work on the sparse containers that the
container lemma actually produces. -/
theorem sharpAsymptotic_of_sparse_container_fingerprint
    (hCE : ContainerExistence) (hSFB : SparseFingerprintBound) :
    SharpAsymptotic :=
  sharpAsymptotic_of_maxContainerBound
    (maxContainerBound_of_containerExistence_sparseFingerprint hCE hSFB)

end JSP000728
