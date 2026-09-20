import JSPProblem.FingerprintBuild
import JSPProblem.FingerprintCount
import JSPProblem.HujterTuza
import JSPProblem.MinTailBound

/-!
# JSP-000728 — per-container glue: sum-free fingerprints and the
determining-fingerprint reduction

This file sharpens the fingerprint counting of `FingerprintBuild.lean` and
then packages the *last* piece of mathematics needed for the BLST18
per-container bound `2^{(1/4+o(1))n}` as an explicit named hypothesis.

## Sum-free fingerprints

The sigma injection `card_maxSumFreeSets_filter_le_sum_linkMaxSets` sends a
maximal sum-free `M ⊆ C` to `(M ∩ [1,K], M ∩ {K+1,…,n})`.  The fingerprint
`M ∩ [1,K]` is not an arbitrary subset of `[1,K]` — it is sum-free and lies
inside the container — so the sum can be restricted to
`(C ∩ [1,K]).powerset.filter IsSumFree`:

* `card_maxSumFreeSets_filter_le_sum_linkMaxSets_sf` — the refined count
  `#{M ⊆ C} ≤ Σ_{S ⊆ C∩[1,K], S sum-free} |linkMaxSets S (C ∩ {K+1,…,n})|`.

## Hujter–Tuza assembly

Since every fingerprint in the sum is sum-free, the upper-half link graphs
are triangle-free and the sharp `2^{|B|/2}` bound (Hujter–Tuza, via
`card_linkMaxSets_le_two_rpow`) applies to every term:

* `card_maxSumFreeSets_filter_le_pow_sf` —
  `#{M ⊆ C} ≤ # {S ⊆ C∩[1,K] sum-free} · 2^{|C∩{K+1,…,n}|/2}`;
* `card_maxSumFreeSets_filter_le_two_rpow_low_mul` — the coarse
  `2^{|C∩[1,K]|} · 2^{|C∩{K+1,…,n}|/2}` form;
* `card_maxSumFreeSets_filter_le_two_rpow_low_add_quarter` — at
  `K = ⌈n/2⌉`, `#{M ⊆ C} ≤ 2^{|C∩[1,⌈n/2⌉]| + n/4}`: the *upper* factor is
  already the sharp `n/4`, and all remaining difficulty is concentrated in
  the number of lower traces.

## The determining-fingerprint hypothesis

The full lower trace `T = M ∩ [1,⌊n/2⌋]` always determines `M`: the trace
`M ∩ {⌊n/2⌋+1,…,n}` is a maximal link-independent set of `L_T` on the
"available" upper vertices of `C` (`detGround n T C`), and `M` is the unique
maximal set containing `T` with that trace (`mem_detFiber_full_trace`).  The
only problem is that `|T|` can be `Θ(n)`.

`DeterminingFingerprint` asserts that this determination survives
compression: inside a `o(n²)`-Schur-triple container, every maximal sum-free
`M` admits a fingerprint `T ⊆ M` of size `≤ ε·n` lying in `detFiber n C T` —
i.e. the upper trace is still link-maximal on `detGround n T C` *and* the
pair `(T, M ∩ detGround n T C)` pins down `M` among the maximal sets housed
by `C`.

* `detGround`, `detFiber`, `mem_detFiber`, `card_detFiber_le` — the
  vocabulary, with the unconditional fiber bound
  `|detFiber n C T| ≤ |linkMaxSets T (detGround n T C)|`.
* `sparseFingerprintBound_of_determiningFingerprint` — the key reduction
  `DeterminingFingerprint → SparseFingerprintBound`: the number of small
  sum-free fingerprints is `2^{o(n)}` (`smallPowersetCard_le_two_rpow`) and
  each contributes at most `2^{|detGround|/2} ≤ 2^{n/4+o(n)}` maximal sets
  by Hujter–Tuza.
* `sharpAsymptotic_of_containerExistence_determiningFingerprint` — the
  prize path `ContainerExistence → DeterminingFingerprint → SharpAsymptotic`.

Together with `ContainerExistence` the prize statement is thus reduced to
two symmetric residual hypotheses: `SmallFingerprint` (small generating
fingerprints for sum-free sets) and `DeterminingFingerprint` (small
*determining* fingerprints for maximal sets inside sparse containers).
-/

namespace JSP000728

/-! ## Sum-free fingerprints -/

/-- **Refined per-container count through sum-free fingerprints.**  In the
regime `n < 2(K+1)` the map `M ↦ (M ∩ [1,K], M ∩ {K+1,…,n})` injects the
maximal sum-free sets housed by `C` into the sigma of pairs `(S, t)` with
`S ⊆ C ∩ [1,K]` *sum-free* and `t` a maximal link-independent subset of
`C ∩ {K+1,…,n}` for `L_S`: the fingerprint `M ∩ [1,K]` is sum-free because
`M` is, and lies in `C` because `M ⊆ C`. -/
theorem card_maxSumFreeSets_filter_le_sum_linkMaxSets_sf {n : ℕ}
    (C : Finset ℤ) {K : ℤ} (hK : (n : ℤ) < 2 * (K + 1)) :
    ((maxSumFreeSets n).filter (· ⊆ C)).card ≤
      ∑ S ∈ (C ∩ Finset.Icc 1 K).powerset.filter IsSumFree,
        (linkMaxSets S (C ∩ Finset.Icc (K + 1) (n : ℤ))).card := by
  classical
  have him : ∀ M ∈ (maxSumFreeSets n).filter (· ⊆ C),
      (⟨M ∩ Finset.Icc 1 K, M ∩ Finset.Icc (K + 1) (n : ℤ)⟩ :
          Σ _ : Finset ℤ, Finset ℤ) ∈
        ((C ∩ Finset.Icc 1 K).powerset.filter IsSumFree).sigma
          fun S => linkMaxSets S (C ∩ Finset.Icc (K + 1) (n : ℤ)) := by
    intro M hM
    obtain ⟨hMmem, hMC⟩ := Finset.mem_filter.mp hM
    have hMmax := mem_maxSumFreeSets.mp hMmem
    rw [Finset.mem_sigma]
    refine ⟨?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_powerset]
      refine ⟨?_, hMmax.2.1.mono Finset.inter_subset_left⟩
      intro x hx
      rw [Finset.mem_inter] at hx ⊢
      exact ⟨hMC hx.1, hx.2⟩
    · rw [mem_linkMaxSets]
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
      ≤ (((C ∩ Finset.Icc 1 K).powerset.filter IsSumFree).sigma
          fun S => linkMaxSets S (C ∩ Finset.Icc (K + 1) (n : ℤ))).card :=
        Finset.card_le_card_of_injOn _ him hinj
    _ = ∑ S ∈ (C ∩ Finset.Icc 1 K).powerset.filter IsSumFree,
          (linkMaxSets S (C ∩ Finset.Icc (K + 1) (n : ℤ))).card :=
        Finset.card_sigma _ _

/-! ## Hujter–Tuza assembly -/

/-- **Per-container bound: sum-free fingerprints × Hujter–Tuza.**  In the
regime `n < 2(K+1)` every term of the refined sum has the sharp bound
`|linkMaxSets S (C ∩ {K+1,…,n})| ≤ 2^{|C ∩ {K+1,…,n}|/2}`: each `S` in the
sum is sum-free, and the ground set lies above `n/2` (`x ≥ K+1` gives
`2x ≥ 2K+2 > n`), so the link graph is triangle-free. -/
theorem card_maxSumFreeSets_filter_le_pow_sf {n : ℕ} (C : Finset ℤ) {K : ℤ}
    (hK : (n : ℤ) < 2 * (K + 1)) :
    (((maxSumFreeSets n).filter (· ⊆ C)).card : ℝ) ≤
      (((C ∩ Finset.Icc 1 K).powerset.filter IsSumFree).card : ℝ) *
        (2 : ℝ) ^ (((C ∩ Finset.Icc (K + 1) (n : ℤ)).card : ℝ) / 2) := by
  have hK0 : (0 : ℤ) ≤ K := by omega
  have hsum := card_maxSumFreeSets_filter_le_sum_linkMaxSets_sf C hK
  have hreal : (((maxSumFreeSets n).filter (· ⊆ C)).card : ℝ) ≤
      ∑ S ∈ (C ∩ Finset.Icc 1 K).powerset.filter IsSumFree,
        ((linkMaxSets S (C ∩ Finset.Icc (K + 1) (n : ℤ))).card : ℝ) := by
    exact_mod_cast hsum
  refine hreal.trans ?_
  calc ∑ S ∈ (C ∩ Finset.Icc 1 K).powerset.filter IsSumFree,
        ((linkMaxSets S (C ∩ Finset.Icc (K + 1) (n : ℤ))).card : ℝ)
      ≤ ∑ _S ∈ (C ∩ Finset.Icc 1 K).powerset.filter IsSumFree,
          (2 : ℝ) ^
            (((C ∩ Finset.Icc (K + 1) (n : ℤ)).card : ℝ) / 2) := by
        refine Finset.sum_le_sum fun S hS => ?_
        rw [Finset.mem_filter, Finset.mem_powerset] at hS
        obtain ⟨hSsub, hSf⟩ := hS
        refine card_linkMaxSets_le_two_rpow (n := max (n : ℤ) K) ?_ hSf ?_
        · intro a ha
          obtain ⟨-, haI⟩ := Finset.mem_inter.mp (hSsub ha)
          rw [Finset.mem_Icc] at haI ⊢
          exact ⟨haI.1, le_trans haI.2 (le_max_right _ _)⟩
        · intro x hx
          obtain ⟨-, hxI⟩ := Finset.mem_inter.mp hx
          obtain ⟨hx1, -⟩ := Finset.mem_Icc.mp hxI
          -- `x ≥ K+1` gives `2x ≥ 2K+2`, which beats both `n` and `K`.
          exact max_lt (by omega) (by omega)
    _ = (((C ∩ Finset.Icc 1 K).powerset.filter IsSumFree).card : ℝ) *
          (2 : ℝ) ^
            (((C ∩ Finset.Icc (K + 1) (n : ℤ)).card : ℝ) / 2) := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-- **Coarse form.**  Dropping the sum-free restriction on fingerprints:
`#{M ⊆ C} ≤ 2^{|C ∩ [1,K]|} · 2^{|C ∩ {K+1,…,n}|/2}`. -/
theorem card_maxSumFreeSets_filter_le_two_rpow_low_mul {n : ℕ}
    (C : Finset ℤ) {K : ℤ} (hK : (n : ℤ) < 2 * (K + 1)) :
    (((maxSumFreeSets n).filter (· ⊆ C)).card : ℝ) ≤
      (2 : ℝ) ^ ((C ∩ Finset.Icc 1 K).card : ℝ) *
        (2 : ℝ) ^ (((C ∩ Finset.Icc (K + 1) (n : ℤ)).card : ℝ) / 2) := by
  refine (card_maxSumFreeSets_filter_le_pow_sf C hK).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (by norm_num) _)
  have hcard : (((C ∩ Finset.Icc 1 K).powerset.filter IsSumFree).card : ℝ) ≤
      (((C ∩ Finset.Icc 1 K).powerset).card : ℝ) := by
    exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
  rw [Finset.card_powerset] at hcard
  calc (((C ∩ Finset.Icc 1 K).powerset.filter IsSumFree).card : ℝ)
      ≤ (((2 : ℕ) ^ (C ∩ Finset.Icc 1 K).card : ℕ) : ℝ) := hcard
    _ = (2 : ℝ) ^ ((C ∩ Finset.Icc 1 K).card : ℝ) := by
        rw [Nat.cast_pow, Nat.cast_ofNat, Real.rpow_natCast]

/-- The upper interval `{⌊n/2⌋+1,…,n}` has `⌈n/2⌉ ≤ (n+1)/2` elements. -/
private theorem card_Icc_half_le (n : ℕ) :
    ((Finset.Icc ((n : ℤ) / 2 + 1) (n : ℤ)).card : ℝ) ≤
      ((n : ℝ) + 1) / 2 := by
  rw [Int.card_Icc]
  have h0 : (0 : ℤ) ≤ (n : ℤ) + 1 - ((n : ℤ) / 2 + 1) := by omega
  have hcast : (((n : ℤ) + 1 - ((n : ℤ) / 2 + 1)).toNat : ℝ) =
      (((n : ℤ) + 1 - ((n : ℤ) / 2 + 1) : ℤ) : ℝ) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg h0]
  rw [hcast]
  have hXR : (((n : ℤ) + 1 - ((n : ℤ) / 2 + 1) : ℤ) : ℝ) =
      (n : ℝ) - (((n : ℤ) / 2 : ℤ) : ℝ) := by push_cast; ring
  rw [hXR]
  have h2 : (n : ℤ) - 1 ≤ 2 * ((n : ℤ) / 2) := by omega
  have h2R : (n : ℝ) - 1 ≤ 2 * (((n : ℤ) / 2 : ℤ) : ℝ) := by
    exact_mod_cast h2
  linarith

/-- The upper interval `{⌈n/2⌉+1,…,n}` has `⌊n/2⌋ ≤ n/2` elements. -/
private theorem card_Icc_ceil_half_succ_le (n : ℕ) :
    ((Finset.Icc (((n : ℤ) + 1) / 2 + 1) (n : ℤ)).card : ℝ) ≤
      (n : ℝ) / 2 := by
  rw [Int.card_Icc]
  have h0 : (0 : ℤ) ≤ (n : ℤ) + 1 - (((n : ℤ) + 1) / 2 + 1) := by omega
  have hcast : (((n : ℤ) + 1 - (((n : ℤ) + 1) / 2 + 1)).toNat : ℝ) =
      (((n : ℤ) + 1 - (((n : ℤ) + 1) / 2 + 1) : ℤ) : ℝ) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg h0]
  rw [hcast]
  have hXR : (((n : ℤ) + 1 - (((n : ℤ) + 1) / 2 + 1) : ℤ) : ℝ) =
      (n : ℝ) - ((((n : ℤ) + 1) / 2 : ℤ) : ℝ) := by push_cast; ring
  rw [hXR]
  have h2 : (n : ℤ) ≤ 2 * (((n : ℤ) + 1) / 2) := by omega
  have h2R : (n : ℝ) ≤ 2 * ((((n : ℤ) + 1) / 2 : ℤ) : ℝ) := by
    exact_mod_cast h2
  linarith

/-- **Unconditional `|C∩low| + n/4` bound.**  Splitting at
`K = ⌈n/2⌉ = ⌊(n+1)/2⌋`, the upper trace `C ∩ {⌈n/2⌉+1,…,n}` has at most
`⌊n/2⌋` elements, so `#{M ⊆ C} ≤ 2^{|C ∩ [1,⌈n/2⌉]| + n/4}`.  The `n/4`
exponent of the sharp conjecture is already visible; what remains is that a
sparse container has `o(n)` *relevant* lower traces — that residual is
`DeterminingFingerprint` below. -/
theorem card_maxSumFreeSets_filter_le_two_rpow_low_add_quarter {n : ℕ}
    (C : Finset ℤ) :
    (((maxSumFreeSets n).filter (· ⊆ C)).card : ℝ) ≤
      (2 : ℝ) ^ (((C ∩ Finset.Icc 1 (((n : ℤ) + 1) / 2)).card : ℝ)
        + (n : ℝ) / 4) := by
  have hK : (n : ℤ) < 2 * (((n : ℤ) + 1) / 2 + 1) := by omega
  refine (card_maxSumFreeSets_filter_le_two_rpow_low_mul C hK).trans ?_
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) ?_
  -- `|C ∩ {⌈n/2⌉+1,…,n}| ≤ ⌊n/2⌋ ≤ n/2`, so its half is `≤ n/4`.
  have hup : ((C ∩ Finset.Icc (((n : ℤ) + 1) / 2 + 1) (n : ℤ)).card : ℝ) ≤
      (n : ℝ) / 2 := by
    have h := Finset.card_le_card (Finset.inter_subset_right :
      C ∩ Finset.Icc (((n : ℤ) + 1) / 2 + 1) (n : ℤ) ⊆
        Finset.Icc (((n : ℤ) + 1) / 2 + 1) (n : ℤ))
    have h' : ((C ∩ Finset.Icc (((n : ℤ) + 1) / 2 + 1) (n : ℤ)).card : ℝ) ≤
        ((Finset.Icc (((n : ℤ) + 1) / 2 + 1) (n : ℤ)).card : ℝ) := by
      exact_mod_cast h
    exact h'.trans (card_Icc_ceil_half_succ_le n)
  linarith

/-! ## The determining ground set and the fingerprint fiber -/

/-- The **determining ground set** of a fingerprint `T` inside a container
`C`: the elements of `C` in the upper half `{⌊n/2⌋+1,…,n}` that are not
`T`-looped — i.e. the vertices that could still be adjoined to a sum-free
superset of `T`.  It depends only on `(n, T, C)`, which is what makes a
small `T` a plausible *determining* fingerprint: a maximal `M ⊇ T` housed
by `C` whose upper trace is link-maximal on this ground set is pinned down
by the pair `(T, M ∩ detGround n T C)`. -/
def detGround (n : ℕ) (T C : Finset ℤ) : Finset ℤ :=
  (C ∩ Finset.Icc ((n : ℤ) / 2 + 1) (n : ℤ)).filter fun x => ¬ linkLoop T x

theorem detGround_subset_upper (n : ℕ) (T C : Finset ℤ) :
    detGround n T C ⊆ Finset.Icc ((n : ℤ) / 2 + 1) (n : ℤ) :=
  (Finset.filter_subset _ _).trans Finset.inter_subset_right

theorem detGround_subset_container (n : ℕ) (T C : Finset ℤ) :
    detGround n T C ⊆ C :=
  (Finset.filter_subset _ _).trans Finset.inter_subset_left

/-- Every vertex of `detGround n T C` lies in the upper half:
`x ≥ ⌊n/2⌋+1` gives `2x ≥ n + 1 > n`. -/
theorem two_mul_gt_of_mem_detGround {n : ℕ} {T C : Finset ℤ} {x : ℤ}
    (hx : x ∈ detGround n T C) : (n : ℤ) < 2 * x := by
  obtain ⟨hxC, -⟩ := Finset.mem_filter.mp hx
  obtain ⟨-, hxI⟩ := Finset.mem_inter.mp hxC
  obtain ⟨hx1, -⟩ := Finset.mem_Icc.mp hxI
  omega

/-- The determining ground set has at most `⌈n/2⌉ ≤ (n+1)/2` elements. -/
theorem card_detGround_le (n : ℕ) (T C : Finset ℤ) :
    ((detGround n T C).card : ℝ) ≤ ((n : ℝ) + 1) / 2 := by
  have h : ((detGround n T C).card : ℝ) ≤
      ((Finset.Icc ((n : ℤ) / 2 + 1) (n : ℤ)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card (detGround_subset_upper n T C)
  exact h.trans (card_Icc_half_le n)

/-- The **fingerprint fiber** of `T` inside `C`: the maximal sum-free sets
of `{1,…,n}` housed by `C` that are *determined* by `T` — `T ⊆ M`, the
upper trace `M ∩ detGround n T C` is a maximal link-independent set of the
link graph `L_T` on the determining ground set, and `M` is the only such
set with its trace. -/
def detFiber (n : ℕ) (C T : Finset ℤ) : Finset (Finset ℤ) :=
  ((maxSumFreeSets n).filter (· ⊆ C)).filter fun M =>
    T ⊆ M ∧ M ∩ detGround n T C ∈ linkMaxSets T (detGround n T C) ∧
      ∀ M' ∈ maxSumFreeSets n, M' ⊆ C → T ⊆ M' →
        M' ∩ detGround n T C = M ∩ detGround n T C → M' = M

theorem mem_detFiber {n : ℕ} {C T M : Finset ℤ} :
    M ∈ detFiber n C T ↔
      M ∈ (maxSumFreeSets n).filter (· ⊆ C) ∧ T ⊆ M ∧
        M ∩ detGround n T C ∈ linkMaxSets T (detGround n T C) ∧
          ∀ M' ∈ maxSumFreeSets n, M' ⊆ C → T ⊆ M' →
            M' ∩ detGround n T C = M ∩ detGround n T C → M' = M :=
  Finset.mem_filter

/-- **The fiber bound**: a determining fiber is counted by the maximal
link-independent sets of the ground set, since `M ↦ M ∩ detGround n T C`
injects `detFiber n C T` into `linkMaxSets T (detGround n T C)` — the
uniqueness clause is exactly the injectivity. -/
theorem card_detFiber_le (n : ℕ) (C T : Finset ℤ) :
    (detFiber n C T).card ≤ (linkMaxSets T (detGround n T C)).card := by
  classical
  refine Finset.card_le_card_of_injOn (fun M => M ∩ detGround n T C) ?_ ?_
  · intro M hM
    rw [Finset.mem_coe, mem_detFiber] at hM
    exact hM.2.2.1
  · intro M₁ h₁ M₂ h₂ heq
    rw [Finset.mem_coe, mem_detFiber] at h₁ h₂
    obtain ⟨h1f, h1T, -, h1uni⟩ := h₁
    obtain ⟨h2f, h2T, -, -⟩ := h₂
    obtain ⟨h2mem, h2C⟩ := Finset.mem_filter.mp h2f
    exact (h1uni M₂ h2mem h2C h2T heq.symm).symm

/-- **The full lower trace determines `M`.**  For
`T = M ∩ [1, ⌊n/2⌋]` the `detFiber` membership is provable
unconditionally:

* the upper trace `M ∩ {⌊n/2⌋+1,…,n}` is link-maximal inside `C`'s upper
  part (`linkMax_indep_of_isMaxSumFree_of_lt_in`), and it lands inside
  `detGround` because no element of a sum-free `M ⊇ T` can be `T`-looped;
* the uniqueness clause follows since `M' ⊇ T` with the same trace forces
  `M ⊆ M'`, hence `M = M'` by maximality.

`DeterminingFingerprint` is therefore exactly the assertion that this
determination survives compression of `T` to `o(n)` elements — the genuine
residual content of the BLST18 per-container count. -/
theorem mem_detFiber_full_trace {n : ℕ} {M C : Finset ℤ}
    (hM : M ∈ maxSumFreeSets n) (hMC : M ⊆ C) :
    M ∈ detFiber n C (M ∩ Finset.Icc 1 ((n : ℤ) / 2)) := by
  obtain ⟨hsub, hsf, hmax⟩ := mem_maxSumFreeSets.mp hM
  set T : Finset ℤ := M ∩ Finset.Icc 1 ((n : ℤ) / 2) with hTdef
  set upI : Finset ℤ := Finset.Icc ((n : ℤ) / 2 + 1) (n : ℤ) with hupdef
  have hK : (n : ℤ) < 2 * ((n : ℤ) / 2 + 1) := by omega
  have hTsub : T ⊆ M := Finset.inter_subset_left
  have hTsf : IsSumFree T := hsf.mono hTsub
  have hTpos : ∀ a ∈ T, (0 : ℤ) < a :=
    fun a ha => interval_pos (hsub (hTsub ha))
  -- No element of a sum-free `N ⊇ T` inside `{1,…,n}` is `T`-looped.
  have hunloop : ∀ N : Finset ℤ, N ⊆ interval n → IsSumFree N → T ⊆ N →
      ∀ x ∈ N, ¬ linkLoop T x := by
    intro N hN hNsf hTN x hx hloop
    have hnot := (linkLoop_iff_not_isSumFree_insert hTsf
      (interval_pos (hN hx)) hTpos).mp hloop
    exact hnot (hNsf.mono (Finset.insert_subset hx hTN))
  -- The trace `M ∩ upI` sits inside the ground set `detGround n T C`.
  have htrB : M ∩ upI ⊆ detGround n T C := by
    intro x hx
    obtain ⟨hxM, hxI⟩ := Finset.mem_inter.mp hx
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_inter.mpr ⟨hMC hxM, hxI⟩,
        hunloop M hsub hsf hTsub x hxM⟩
  have htrace : M ∩ detGround n T C = M ∩ upI := by
    apply Finset.Subset.antisymm
    · intro x hx
      obtain ⟨hxM, hxB⟩ := Finset.mem_inter.mp hx
      exact Finset.mem_inter.mpr
        ⟨hxM, (Finset.mem_inter.mp (Finset.mem_filter.mp hxB).1).2⟩
    · intro x hx
      exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hx).1, htrB hx⟩
  refine mem_detFiber.mpr ⟨Finset.mem_filter.mpr ⟨hM, hMC⟩, hTsub, ?_, ?_⟩
  · rw [htrace, mem_linkMaxSets]
    refine ⟨htrB, ?_⟩
    have hlm := linkMax_indep_of_isMaxSumFree_of_lt_in
      ⟨hsub, hsf, hmax⟩ hMC hK
    exact hlm.mono htrB (Finset.filter_subset _ _)
  · intro M' hM' hM'C hTM' heq
    obtain ⟨hsub', hsf', -⟩ := mem_maxSumFreeSets.mp hM'
    have htrB' : M' ∩ upI ⊆ detGround n T C := by
      intro x hx
      obtain ⟨hxM, hxI⟩ := Finset.mem_inter.mp hx
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_inter.mpr ⟨hM'C hxM, hxI⟩,
          hunloop M' hsub' hsf' hTM' x hxM⟩
    -- `M ⊆ M'`: low elements are in `T ⊆ M'`; upper elements lie in the
    -- trace `M ∩ B = M' ∩ B ⊆ M'`.
    have hMM' : M ⊆ M' := by
      intro x hx
      obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp (hsub hx)
      by_cases hxK : x ≤ (n : ℤ) / 2
      · exact hTM' (Finset.mem_inter.mpr
          ⟨hx, Finset.mem_Icc.mpr ⟨h1, hxK⟩⟩)
      · have hxup : x ∈ upI :=
          Finset.mem_Icc.mpr ⟨by omega, h2⟩
        have hxB : x ∈ M ∩ detGround n T C :=
          Finset.mem_inter.mpr
            ⟨hx, htrB (Finset.mem_inter.mpr ⟨hx, hxup⟩)⟩
        rw [← heq] at hxB
        exact (Finset.mem_inter.mp hxB).1
    have hM'M : M' ⊆ M :=
      (isMaxSumFree_iff_isMaximalSumFree.mp ⟨hsub, hsf, hmax⟩).2.2 M'
        hsub' hsf' hMM'
    exact Finset.Subset.antisymm hM'M hMM'

/-! ## The determining-fingerprint hypothesis and the key reduction -/

/-- **Determining-fingerprint hypothesis** (BLST18 residual): for every
`ε > 0` there is a `δ > 0` such that, eventually, inside every container
`C ⊆ {1,…,n}` with at most `δ·n²` Schur triples, every maximal sum-free
`M ⊆ C` has a *determining fingerprint* `T ⊆ M` of size at most `ε·n` —
meaning `M ∈ detFiber n C T`: the upper trace `M ∩ detGround n T C` is a
maximal link-independent set of `L_T` on the available upper vertices of
`C`, and `M` is the unique maximal set housed by `C` containing `T` with
that trace.

`mem_detFiber_full_trace` shows the fiber membership is provable for the
full lower trace `T = M ∩ [1,⌊n/2⌋]`; the hypothesis is precisely that the
same determination holds with `|T| = o(n)`.  This is symmetric to the
`SmallFingerprint` hypothesis behind `ContainerExistence`: small generating
fingerprints for sum-free sets on the one hand, small *determining*
fingerprints for maximal sets in sparse containers on the other. -/
def DeterminingFingerprint : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n : ℕ in Filter.atTop,
    ∀ C : Finset ℤ, C ⊆ interval n →
      (schurTripleCount C : ℝ) ≤ δ * (n : ℝ) ^ 2 →
      ∀ M ∈ maxSumFreeSets n, M ⊆ C →
        ∃ T : Finset ℤ, T ⊆ M ∧ (T.card : ℝ) ≤ ε * (n : ℝ) ∧
          M ∈ detFiber n C T

/-- **The key glue**: `DeterminingFingerprint → SparseFingerprintBound`.

Each maximal sum-free `M` housed by a sparse `C` lies in the fiber
`detFiber n C T` of its `o(n)`-sized determining fingerprint `T`.  The
number of candidate fingerprints — small sum-free subsets of `{1,…,n}` — is
subexponential (`smallPowersetCard_le_two_rpow`), and each fiber is counted
by the maximal link-independent sets of `detGround n T C`, which lives in
the triangle-free upper half: `|detFiber| ≤ |linkMaxSets T (detGround)| ≤
2^{|detGround|/2} ≤ 2^{(n+1)/4}` (`card_detFiber_le`, `card_detGround_le`,
`card_linkMaxSets_le_two_rpow`).  Multiplying gives
`#{M ⊆ C} ≤ 2^{(ε/2)n} · 2^{(n+1)/4} ≤ 2^{(1/4+ε)n}` for `n ≥ 1/(2ε)`. -/
theorem sparseFingerprintBound_of_determiningFingerprint
    (hDF : DeterminingFingerprint) : SparseFingerprintBound := by
  intro ε hε
  obtain ⟨δ₁, hδ₁, hsmall⟩ :=
    smallPowersetCard_le_two_rpow (half_pos hε)
  obtain ⟨δ₂, hδ₂, hdf⟩ := hDF δ₁ hδ₁
  refine ⟨δ₂, hδ₂, ?_⟩
  filter_upwards [hdf, hsmall,
    Filter.eventually_ge_atTop ⌈(1 / (2 * ε) : ℝ)⌉₊]
    with n hdfn hsmalln hnN
  intro C hC htr
  classical
  -- the small sum-free fingerprints
  set P : Finset (Finset ℤ) := (interval n).powerset.filter
    fun T => T.card ≤ ⌊δ₁ * (n : ℝ)⌋₊ ∧ IsSumFree T with hPdef
  -- every maximal set in `C` lies in the fiber of some `T ∈ P`
  have hcover : (maxSumFreeSets n).filter (· ⊆ C) ⊆
      P.biUnion (detFiber n C) := by
    intro M hM
    obtain ⟨hMmem, hMC⟩ := Finset.mem_filter.mp hM
    obtain ⟨T, hTM, hTcard, hfin⟩ := hdfn C hC htr M hMmem hMC
    rw [Finset.mem_biUnion]
    refine ⟨T, ?_, hfin⟩
    rw [hPdef, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨hTM.trans (hMC.trans hC), Nat.le_floor hTcard,
      (mem_maxSumFreeSets.mp hMmem).2.1.mono hTM⟩
  -- summing the fiber bounds over `P`
  have hcard : (((maxSumFreeSets n).filter (· ⊆ C)).card : ℝ) ≤
      ∑ T ∈ P, ((linkMaxSets T (detGround n T C)).card : ℝ) := by
    have h1 : ((maxSumFreeSets n).filter (· ⊆ C)).card ≤
        ∑ T ∈ P, (detFiber n C T).card :=
      (Finset.card_le_card hcover).trans Finset.card_biUnion_le
    have h2 : ∑ T ∈ P, (detFiber n C T).card ≤
        ∑ T ∈ P, (linkMaxSets T (detGround n T C)).card :=
      Finset.sum_le_sum fun T _ => card_detFiber_le n C T
    exact_mod_cast h1.trans h2
  -- Hujter–Tuza on each ground set: `≤ 2^{|detGround|/2} ≤ 2^{(n+1)/4}`
  have hTbound : ∀ T ∈ P, ((linkMaxSets T (detGround n T C)).card : ℝ) ≤
      (2 : ℝ) ^ (((n : ℝ) + 1) / 4) := by
    intro T hT
    rw [hPdef, Finset.mem_filter, Finset.mem_powerset] at hT
    obtain ⟨hTI, -, hTsf⟩ := hT
    have hBcard := card_detGround_le n T C
    refine (card_linkMaxSets_le_two_rpow hTI hTsf
      (fun x hx => two_mul_gt_of_mem_detGround hx)).trans ?_
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) ?_
    linarith
  -- assemble: `# ≤ |P| · 2^{(n+1)/4} ≤ 2^{(ε/2)n} · 2^{(n+1)/4}`
  have hsum : (((maxSumFreeSets n).filter (· ⊆ C)).card : ℝ) ≤
      (P.card : ℝ) * (2 : ℝ) ^ (((n : ℝ) + 1) / 4) := by
    calc (((maxSumFreeSets n).filter (· ⊆ C)).card : ℝ)
        ≤ ∑ T ∈ P, ((linkMaxSets T (detGround n T C)).card : ℝ) := hcard
      _ ≤ ∑ _T ∈ P, (2 : ℝ) ^ (((n : ℝ) + 1) / 4) :=
          Finset.sum_le_sum fun T hT => hTbound T hT
      _ = (P.card : ℝ) * (2 : ℝ) ^ (((n : ℝ) + 1) / 4) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hPcard : (P.card : ℝ) ≤ (2 : ℝ) ^ ((ε / 2) * (n : ℝ)) := by
    have hsub : P ⊆ (interval n).powerset.filter
        (fun T => T.card ≤ ⌊δ₁ * (n : ℝ)⌋₊) := by
      intro T hT
      rw [hPdef, Finset.mem_filter] at hT
      exact Finset.mem_filter.mpr ⟨hT.1, hT.2.1⟩
    have hle : (P.card : ℝ) ≤ (((interval n).powerset.filter
        (fun T => T.card ≤ ⌊δ₁ * (n : ℝ)⌋₊)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    exact hle.trans hsmalln
  -- the exponent check: `(ε/2)·n + (n+1)/4 ≤ (1/4+ε)·n` for `n ≥ 1/(2ε)`
  have hN : (1 : ℝ) / (2 * ε) ≤ (n : ℝ) := Nat.ceil_le.mp hnN
  have hεn : (1 : ℝ) / 4 ≤ (ε / 2) * (n : ℝ) := by
    have h2ε : (0 : ℝ) < 2 * ε := by positivity
    have h := mul_le_mul_of_nonneg_right hN h2ε.le
    rw [div_mul_cancel₀ 1 (ne_of_gt h2ε)] at h
    linarith
  calc (((maxSumFreeSets n).filter (· ⊆ C)).card : ℝ)
      ≤ (P.card : ℝ) * (2 : ℝ) ^ (((n : ℝ) + 1) / 4) := hsum
    _ ≤ (2 : ℝ) ^ ((ε / 2) * (n : ℝ)) * (2 : ℝ) ^ (((n : ℝ) + 1) / 4) :=
        mul_le_mul_of_nonneg_right hPcard
          (Real.rpow_nonneg (by norm_num) _)
    _ = (2 : ℝ) ^ ((ε / 2) * (n : ℝ) + ((n : ℝ) + 1) / 4) := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    _ ≤ (2 : ℝ) ^ ((1 / 4 + ε) * (n : ℝ)) := by
        refine Real.rpow_le_rpow_of_exponent_le
          (by norm_num : (1 : ℝ) ≤ 2) ?_
        nlinarith [hεn]

/-- **Prize path.**  `ContainerExistence` supplies the sparse containers and
`DeterminingFingerprint` counts the maximal sum-free sets inside each of
them: together they give `log₂ f(n) / n → 1/4`.  The residual hypotheses
are then symmetric — `SmallFingerprint` behind `ContainerExistence` and
`DeterminingFingerprint` behind `SparseFingerprintBound`. -/
theorem sharpAsymptotic_of_containerExistence_determiningFingerprint
    (hCE : ContainerExistence) (hDF : DeterminingFingerprint) :
    SharpAsymptotic :=
  sharpAsymptotic_of_sparse_container_fingerprint hCE
    (sparseFingerprintBound_of_determiningFingerprint hDF)

end JSP000728
