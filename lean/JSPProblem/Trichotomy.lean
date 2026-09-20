import JSPProblem.LinkSumFree
import JSPProblem.SparseCard

/-!
# JSP-000728 — the DFST trichotomy and the three counting lemmas

This file formalises the *structural* layer of the BLST upper bound
`f_max(n) = 2^{(1/4 + o(1))n}` (Balogh–Liu–Sharifzadeh–Treglown), packaging
the remaining mathematical content into three named hypotheses and proving
all conditional steps.

## Hypotheses (black boxes of the paper)

* `DFST` — the Deshouillers–Freiman–Sós–Temkin trichotomy (BLST Thm 2.2):
  every sum-free `S ⊆ {1,…,n}` satisfies (i) `|S| ≤ 2n/5 + 1`, or
  (ii) `S ⊆ odds n`, or (iii) `|S| ≤ min S`.
* `OddContainerBound` — the BLST Lemma 3.4 computation: for a sum-free
  fingerprint `S` of *even* numbers, the link graph `L_S[odds n]` has at
  most `2^{(1/4 + ε)n}` maximal independent sets (the `n^{1/4}` split into
  the almost-regular Sapozhenko regime and the almost-triangle-free
  Hujter–Tuza regime).
* `SchurRemoval` (in `Removal.lean`) — Green's arithmetic removal lemma.

## Proved statements

* `container_trichotomy` — BLST Lemma 2.4: under `SchurRemoval` + `DFST`,
  every `δn²`-sparse container `C ⊆ {1,…,n}` is small
  (`|C| ≤ (1/2 − 1/11)n`), interval-type
  (`|C ∩ [1, ⌊n/2⌋]| ≤ n/2 − |C| + εn`), or odd-type (`|C ∖ odds n| ≤ εn`).
* `maxSumFreeCount_filter_le_of_small_container` — BLST Lemma 3.2: a
  container inside `A ∪ B` with `A` sum-free, `|A| ≤ 9n/20`, houses at most
  `2^{|B| + n/4}` maximal sum-free sets (Moon–Moser; `log₂ 3 ≤ 5/3` since
  `27 ≤ 32`).
* `maxSumFreeCount_filter_le_of_interval_container` — BLST Lemma 3.3: any
  `C ⊆ {1,…,n}` houses at most `2^{(|C| + |C ∩ [1,⌊n/2⌋]|)/2}` maximal
  sum-free sets (fingerprint on the lower half, Hujter–Tuza on the upper
  half, which is automatically sum-free and makes `L_S` triangle-free).
* `sparseFingerprintBound_of_removal_dfst_odd` — the master assembly
  `SchurRemoval → DFST → OddContainerBound → SparseFingerprintBound`.
* `sharpAsymptotic_of_containerExistence_removal_dfst_odd` — the headline
  `ContainerExistence → SchurRemoval → DFST → OddContainerBound →
  SharpAsymptotic`.

The key auxiliary observation is
`card_maxSumFreeSets_filter_union_le_sum_linkMaxSets_isSumFree`: the
fingerprint `M ∩ B` of a maximal sum-free `M` is itself sum-free, so the
sigma-count runs over *sum-free* fingerprints only — this is what makes the
Hujter–Tuza bound available in the interval case and the
`OddContainerBound` hypothesis applicable in the odd case.
-/

namespace JSP000728

/-! ## The DFST trichotomy hypothesis -/

/-- **DFST trichotomy** (hypothesis): eventually, every sum-free
`S ⊆ {1,…,n}` satisfies at least one of

* (i) `|S| ≤ 2n/5 + 1`;
* (ii) `S` consists only of odd numbers (`S ⊆ odds n`);
* (iii) every element of `S` is at least `|S|` (`S` lives above its own
  cardinality).

This is the Deshouillers–Freiman–Sós–Temkin structure theorem, used as a
black box in BLST (Theorem 2.2). -/
def DFST : Prop :=
  ∀ᶠ n : ℕ in Filter.atTop, ∀ S : Finset ℤ, S ⊆ interval n →
    IsSumFree S →
      (S.card : ℝ) ≤ (2 / 5 : ℝ) * (n : ℝ) + 1 ∨
        S ⊆ odds n ∨ ∀ x ∈ S, (S.card : ℤ) ≤ x

/-! ## Counting through sum-free fingerprints -/

/-- **Fingerprint/link-MIS counting, sum-free fingerprints only.**  The map
`M ↦ (M ∩ B, M ∩ A)` injects the maximal sum-free subsets of `{1,…,n}`
housed by `A ∪ B` into the sigma type of pairs `(S, t)` with `S ⊆ B`
*sum-free* (as `S = M ∩ B ⊆ M`) and `t ∈ linkMaxSets S A`.  Restricting to
sum-free fingerprints is what makes the Hujter–Tuza triangle-free bound
applicable in the interval-type and odd-type container cases. -/
theorem card_maxSumFreeSets_filter_union_le_sum_linkMaxSets_isSumFree
    {n : ℕ} {A B : Finset ℤ}
    (hAI : A ⊆ interval n) (hAsf : IsSumFree A) :
    ((maxSumFreeSets n).filter (· ⊆ A ∪ B)).card ≤
      ∑ S ∈ B.powerset.filter IsSumFree, (linkMaxSets S A).card := by
  classical
  have him : ∀ M ∈ (maxSumFreeSets n).filter (· ⊆ A ∪ B),
      (⟨M ∩ B, M ∩ A⟩ : Σ _ : Finset ℤ, Finset ℤ) ∈
        (B.powerset.filter IsSumFree).sigma fun S => linkMaxSets S A := by
    intro M hM
    obtain ⟨hMmem, hMC⟩ := Finset.mem_filter.mp hM
    have hMmax := mem_maxSumFreeSets.mp hMmem
    rw [Finset.mem_sigma]
    refine ⟨Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr Finset.inter_subset_right,
        hMmax.2.1.mono Finset.inter_subset_left⟩, ?_⟩
    rw [mem_linkMaxSets]
    exact ⟨Finset.inter_subset_right,
      linkMaxIndepSet_inter_of_isMaxSumFree hMmax hAI hAsf hMC⟩
  have hinj : Set.InjOn
      (fun M : Finset ℤ => (⟨M ∩ B, M ∩ A⟩ : Σ _ : Finset ℤ, Finset ℤ))
      ↑((maxSumFreeSets n).filter (· ⊆ A ∪ B)) := by
    intro M hM M' hM' heq
    obtain ⟨-, hMC⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hM)
    obtain ⟨-, hM'C⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hM')
    have h1 : M ∩ B = M' ∩ B := congrArg Sigma.fst heq
    have h2 : M ∩ A = M' ∩ A := congrArg Sigma.snd heq
    have e : M ∩ A ∪ M ∩ B = M := by
      ext y
      simp only [Finset.mem_union, Finset.mem_inter]
      constructor
      · rintro (⟨hy, -⟩ | ⟨hy, -⟩) <;> exact hy
      · intro hy
        rcases Finset.mem_union.mp (hMC hy) with h | h
        · exact Or.inl ⟨hy, h⟩
        · exact Or.inr ⟨hy, h⟩
    have e' : M' ∩ A ∪ M' ∩ B = M' := by
      ext y
      simp only [Finset.mem_union, Finset.mem_inter]
      constructor
      · rintro (⟨hy, -⟩ | ⟨hy, -⟩) <;> exact hy
      · intro hy
        rcases Finset.mem_union.mp (hM'C hy) with h | h
        · exact Or.inl ⟨hy, h⟩
        · exact Or.inr ⟨hy, h⟩
    calc M = M ∩ A ∪ M ∩ B := e.symm
      _ = M' ∩ A ∪ M' ∩ B := by rw [h1, h2]
      _ = M' := e'
  calc ((maxSumFreeSets n).filter (· ⊆ A ∪ B)).card
      ≤ ((B.powerset.filter IsSumFree).sigma
          fun S => linkMaxSets S A).card :=
        Finset.card_le_card_of_injOn _ him hinj
    _ = ∑ S ∈ B.powerset.filter IsSumFree, (linkMaxSets S A).card :=
        Finset.card_sigma _ _

/-- **Monotonicity of the housed-maximal-set count.** -/
private theorem card_filter_subset_mono {n : ℕ} {C D : Finset ℤ}
    (h : C ⊆ D) :
    ((maxSumFreeSets n).filter (· ⊆ C)).card ≤
      ((maxSumFreeSets n).filter (· ⊆ D)).card := by
  apply Finset.card_le_card
  intro M hM
  rw [Finset.mem_filter] at hM ⊢
  exact ⟨hM.1, hM.2.trans h⟩

/-- **Assembled bound with a per-fingerprint MIS bound.**  If every
sum-free fingerprint `S ⊆ B` admits at most `c` maximal link-independent
subsets of the sum-free ground `A ⊆ {1,…,n}`, then `A ∪ B` houses at most
`2^{|B|} · c` maximal sum-free sets of `{1,…,n}`. -/
theorem card_maxSumFreeSets_filter_union_le_two_pow_mul {n : ℕ}
    {A B : Finset ℤ} (hAI : A ⊆ interval n) (hAsf : IsSumFree A)
    {c : ℝ} (hc : 0 ≤ c)
    (hb : ∀ S : Finset ℤ, S ⊆ B → IsSumFree S →
      ((linkMaxSets S A).card : ℝ) ≤ c) :
    (((maxSumFreeSets n).filter (· ⊆ A ∪ B)).card : ℝ) ≤
      (2 : ℝ) ^ (B.card : ℝ) * c := by
  have hsum := card_maxSumFreeSets_filter_union_le_sum_linkMaxSets_isSumFree
    (B := B) hAI hAsf
  have hcard : ((B.powerset.filter IsSumFree).card : ℝ) ≤
      (2 : ℝ) ^ (B.card : ℝ) := by
    have h : (B.powerset.filter IsSumFree).card ≤ 2 ^ B.card := by
      calc (B.powerset.filter IsSumFree).card ≤ B.powerset.card :=
          Finset.card_le_card (Finset.filter_subset _ _)
        _ = 2 ^ B.card := Finset.card_powerset B
    calc ((B.powerset.filter IsSumFree).card : ℝ)
        ≤ ((2 ^ B.card : ℕ) : ℝ) := by exact_mod_cast h
      _ = (2 : ℝ) ^ (B.card : ℝ) := by norm_cast
  calc (((maxSumFreeSets n).filter (· ⊆ A ∪ B)).card : ℝ)
      ≤ ∑ S ∈ B.powerset.filter IsSumFree,
          ((linkMaxSets S A).card : ℝ) := by exact_mod_cast hsum
    _ ≤ ∑ _S ∈ B.powerset.filter IsSumFree, c :=
        Finset.sum_le_sum fun S hS =>
          hb S (Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1)
            (Finset.mem_filter.mp hS).2
    _ = ((B.powerset.filter IsSumFree).card : ℝ) * c := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 : ℝ) ^ (B.card : ℝ) * c :=
        mul_le_mul_of_nonneg_right hcard hc

/-! ## Case (a): small containers (BLST Lemma 3.2) -/

/-- `3 ≤ 2^{5/3}` (equivalently `log₂ 3 ≤ 5/3`), via `27 ≤ 32`. -/
private theorem three_le_two_rpow_five_thirds :
    (3 : ℝ) ≤ (2 : ℝ) ^ ((5 : ℝ) / 3) := by
  have h2 : ((2 : ℝ) ^ ((5 : ℝ) / 3)) ^ 3 = 32 := by
    have e : ((2 : ℝ) ^ ((5 : ℝ) / 3)) ^ 3 = (2 : ℝ) ^ ((5 : ℕ) : ℝ) := by
      rw [← Real.rpow_natCast _ 3,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      norm_num
    rw [e, Real.rpow_natCast]
    norm_num
  refine le_of_pow_le_pow_left₀ (by norm_num : (3 : ℕ) ≠ 0)
    (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _) ?_
  rw [h2]
  norm_num

/-- `3^t ≤ 2^{5t/3}` for `t ≥ 0`. -/
private theorem three_rpow_le_two_rpow_five_thirds (t : ℝ) (ht : 0 ≤ t) :
    (3 : ℝ) ^ t ≤ (2 : ℝ) ^ ((5 / 3 : ℝ) * t) := by
  have h1 : (3 : ℝ) ^ t ≤ ((2 : ℝ) ^ ((5 : ℝ) / 3)) ^ t :=
    Real.rpow_le_rpow (by norm_num) three_le_two_rpow_five_thirds ht
  have h2 : ((2 : ℝ) ^ ((5 : ℝ) / 3)) ^ t =
      (2 : ℝ) ^ ((5 / 3 : ℝ) * t) := by
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  exact h1.trans_eq h2

/-- **Small containers (BLST Lemma 3.2).**  If a container `C` sits inside
`A ∪ B` with `A ⊆ {1,…,n}` sum-free of size `|A| ≤ 9n/20`, then `C` houses
at most `2^{|B|} · 3^{|A|/3} ≤ 2^{|B| + n/4}` maximal sum-free sets: the
fingerprint `M ∩ B` is arbitrary (`2^{|B|}` choices) and the trace `M ∩ A`
is a maximal link-independent set, counted by Moon–Moser `3^{|A|/3}`; the
arithmetic `3^{9n/60} = 2^{(log₂ 3)·3n/20} ≤ 2^{(5/3)·3n/20} = 2^{n/4}`
closes the bound. -/
theorem maxSumFreeCount_filter_le_of_small_container {n : ℕ}
    {C A B : Finset ℤ}
    (hAI : A ⊆ interval n) (hAsf : IsSumFree A) (hcover : C ⊆ A ∪ B)
    (hA : (A.card : ℝ) ≤ (9 / 20 : ℝ) * (n : ℝ)) :
    (((maxSumFreeSets n).filter (· ⊆ C)).card : ℝ) ≤
      (2 : ℝ) ^ ((B.card : ℝ) + (1 / 4 : ℝ) * (n : ℝ)) := by
  have hmono : ((maxSumFreeSets n).filter (· ⊆ C)).card ≤
      ((maxSumFreeSets n).filter (· ⊆ A ∪ B)).card :=
    card_filter_subset_mono hcover
  have hmain := card_maxSumFreeSets_filter_union_le_two_pow_mul_three_rpow
    (B := B) hAI hAsf
  have h3le : (3 : ℝ) ^ ((A.card : ℝ) / 3) ≤
      (2 : ℝ) ^ ((1 / 4 : ℝ) * (n : ℝ)) := by
    refine (three_rpow_le_two_rpow_five_thirds _
      (by positivity)).trans ?_
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith [hA, hn]
  calc (((maxSumFreeSets n).filter (· ⊆ C)).card : ℝ)
      ≤ (((maxSumFreeSets n).filter (· ⊆ A ∪ B)).card : ℝ) := by
        exact_mod_cast hmono
    _ ≤ (2 : ℝ) ^ (B.card : ℕ) * (3 : ℝ) ^ ((A.card : ℝ) / 3) := hmain
    _ ≤ (2 : ℝ) ^ (B.card : ℕ) *
          (2 : ℝ) ^ ((1 / 4 : ℝ) * (n : ℝ)) :=
        mul_le_mul_of_nonneg_left h3le (pow_nonneg (by norm_num) _)
    _ = (2 : ℝ) ^ ((B.card : ℝ) + (1 / 4 : ℝ) * (n : ℝ)) := by
        rw [← Real.rpow_natCast,
          ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]

/-! ## Case (b): interval-type containers (BLST Lemma 3.3) -/

/-- **Interval-type containers (BLST Lemma 3.3).**  For `C ⊆ {1,…,n}` split
`C = A₁ ∪ A₂` at `⌊n/2⌋`.  The upper part `A₂ ⊆ (n/2, n]` is automatically
sum-free, and for every sum-free fingerprint `S ⊆ A₁ ⊆ [1, ⌊n/2⌋]` the
link graph `L_S[A₂]` is triangle-free (all edges are difference edges),
whence Hujter–Tuza gives `|linkMaxSets S A₂| ≤ 2^{|A₂|/2}`.  Assembling:

  `#{M ⊆ C} ≤ 2^{|A₁|} · 2^{|A₂|/2} = 2^{(|C| + |A₁|)/2}`.

Under the interval alternative of `container_trichotomy`,
`|A₁| ≤ n/2 − |C| + o(n)`, this is `2^{n/4 + o(n)}`. -/
theorem maxSumFreeCount_filter_le_of_interval_container {n : ℕ}
    {C : Finset ℤ} (hCI : C ⊆ interval n) :
    (((maxSumFreeSets n).filter (· ⊆ C)).card : ℝ) ≤
      (2 : ℝ) ^ (((C.card : ℝ) +
        ((C ∩ Finset.Icc 1 ((n / 2 : ℕ) : ℤ)).card : ℝ)) / 2) := by
  classical
  set K : ℤ := ((n / 2 : ℕ) : ℤ) with hK
  have hKbound : 2 * K ≤ (n : ℤ) ∧ (n : ℤ) < 2 * K + 2 := by
    have h1 : n / 2 * 2 ≤ n := Nat.div_mul_le_self n 2
    have h2 : n < 2 * (n / 2 + 1) := Nat.lt_mul_div_succ n two_pos
    omega
  have hKn : K ≤ (n : ℤ) := by omega
  have hCunion : C = (C ∩ Finset.Icc 1 K) ∪
      (C ∩ Finset.Icc (K + 1) (n : ℤ)) := by
    ext x
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_Icc]
    constructor
    · intro hx
      obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp (hCI hx)
      by_cases hxK : x ≤ K
      · exact Or.inl ⟨hx, h1, hxK⟩
      · exact Or.inr ⟨hx, by omega, h2⟩
    · rintro (⟨h, -, -⟩ | ⟨h, -, -⟩) <;> exact h
  have hdisj : Disjoint (C ∩ Finset.Icc 1 K)
      (C ∩ Finset.Icc (K + 1) (n : ℤ)) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    obtain ⟨-, hxIcc1⟩ := Finset.mem_inter.mp hx1
    obtain ⟨-, hxle⟩ := Finset.mem_Icc.mp hxIcc1
    obtain ⟨-, hxIcc2⟩ := Finset.mem_inter.mp hx2
    obtain ⟨hxge, -⟩ := Finset.mem_Icc.mp hxIcc2
    omega
  have hA₂sub : C ∩ Finset.Icc (K + 1) (n : ℤ) ⊆ interval n :=
    fun x hx => hCI (Finset.mem_inter.mp hx).1
  have hA₂sf : IsSumFree (C ∩ Finset.Icc (K + 1) (n : ℤ)) := by
    intro x hx y hy hxy
    obtain ⟨-, hxIcc⟩ := Finset.mem_inter.mp hx
    obtain ⟨hxge, -⟩ := Finset.mem_Icc.mp hxIcc
    obtain ⟨-, hyIcc⟩ := Finset.mem_inter.mp hy
    obtain ⟨hyge, -⟩ := Finset.mem_Icc.mp hyIcc
    obtain ⟨-, hxyIcc⟩ := Finset.mem_inter.mp hxy
    obtain ⟨-, hxyle⟩ := Finset.mem_Icc.mp hxyIcc
    omega
  have hb : ∀ S : Finset ℤ, S ⊆ C ∩ Finset.Icc 1 K → IsSumFree S →
      ((linkMaxSets S (C ∩ Finset.Icc (K + 1) (n : ℤ))).card : ℝ) ≤
        (2 : ℝ) ^
          (((C ∩ Finset.Icc (K + 1) (n : ℤ)).card : ℝ) / 2) := by
    intro S hS hSsf
    refine card_linkMaxSets_le_two_rpow (n := (n : ℤ)) ?_ hSsf ?_
    · intro x hx
      obtain ⟨-, hxIcc⟩ := Finset.mem_inter.mp (hS hx)
      obtain ⟨hx1, hxK⟩ := Finset.mem_Icc.mp hxIcc
      exact Finset.mem_Icc.mpr ⟨hx1, hxK.trans hKn⟩
    · intro x hx
      obtain ⟨-, hxIcc⟩ := Finset.mem_inter.mp hx
      obtain ⟨hxge, -⟩ := Finset.mem_Icc.mp hxIcc
      omega
  have hbound := card_maxSumFreeSets_filter_union_le_two_pow_mul
    (A := C ∩ Finset.Icc (K + 1) (n : ℤ)) (B := C ∩ Finset.Icc 1 K)
    hA₂sub hA₂sf (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _) hb
  have hmono : ((maxSumFreeSets n).filter (· ⊆ C)).card ≤
      ((maxSumFreeSets n).filter
        (· ⊆ (C ∩ Finset.Icc (K + 1) (n : ℤ)) ∪
          (C ∩ Finset.Icc 1 K))).card :=
    card_filter_subset_mono
      (Finset.subset_of_eq (hCunion.trans (Finset.union_comm _ _)))
  have hcardC : (C.card : ℝ) = ((C ∩ Finset.Icc 1 K).card : ℝ) +
      ((C ∩ Finset.Icc (K + 1) (n : ℤ)).card : ℝ) := by
    have h : C.card = (C ∩ Finset.Icc 1 K).card +
        (C ∩ Finset.Icc (K + 1) (n : ℤ)).card := by
      conv_lhs => rw [hCunion]
      exact Finset.card_union_of_disjoint hdisj
    exact_mod_cast h
  calc (((maxSumFreeSets n).filter (· ⊆ C)).card : ℝ)
      ≤ (((maxSumFreeSets n).filter
          (· ⊆ (C ∩ Finset.Icc (K + 1) (n : ℤ)) ∪
            (C ∩ Finset.Icc 1 K))).card : ℝ) := by
        exact_mod_cast hmono
    _ ≤ (2 : ℝ) ^ ((C ∩ Finset.Icc 1 K).card : ℝ) *
          (2 : ℝ) ^
            (((C ∩ Finset.Icc (K + 1) (n : ℤ)).card : ℝ) / 2) :=
        hbound
    _ = (2 : ℝ) ^ (((C ∩ Finset.Icc 1 K).card : ℝ) +
          ((C ∩ Finset.Icc (K + 1) (n : ℤ)).card : ℝ) / 2) := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    _ = (2 : ℝ) ^ (((C.card : ℝ) +
          ((C ∩ Finset.Icc 1 K).card : ℝ)) / 2) := by
        congr 1
        linarith [hcardC]

/-! ## The container trichotomy (BLST Lemma 2.4) -/

/-- **Container trichotomy (BLST Lemma 2.4).**  Under the Schur removal
lemma and the DFST trichotomy, for every `ε > 0` there is `δ > 0` such
that, eventually, every `C ⊆ {1,…,n}` with at most `δn²` Schur triples
satisfies one of

* (small) `|C| ≤ (1/2 − 1/11)·n`;
* (interval-type) `|C ∩ [1, ⌊n/2⌋]| ≤ n/2 − |C| + εn` — equivalently, all
  but `o(n)` elements of `C` lie in `[(1/2 − γ)n, n]` for
  `γ = 1/2 − |C|/n`;
* (odd-type) `|C ∖ odds n| ≤ εn`.

*Proof.*  Removal gives `t ⊆ C` sum-free with `|C ∖ t| ≤ ε₁n`, hence
`|t| ≥ |C| − ε₁n`.  If `|C| > (1/2 − 1/11)n` then `|t| > 2n/5 + 1` (using
`ε₁ ≤ 1/220`), killing DFST (i).  DFST (ii) gives `C ∖ odds ⊆ C ∖ t`,
whence `|C ∖ odds| ≤ ε₁n`.  DFST (iii) gives `t ⊆ [|t|, n]`, so the
elements of `C` below `|t|` all lie in `C ∖ t`, and
`|C ∩ [1, ⌊n/2⌋]| ≤ |C ∖ t| + |Icc |t| ⌊n/2⌋| ≤ ε₁n + n/2 − |t| + 1
≤ n/2 − |C| + εn`. -/
theorem container_trichotomy (hSR : SchurRemoval) (hDFST : DFST) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n : ℕ in Filter.atTop,
      ∀ C : Finset ℤ, C ⊆ interval n →
        (schurTripleCount C : ℝ) ≤ δ * (n : ℝ) ^ 2 →
        (C.card : ℝ) ≤ (1 / 2 - 1 / 11) * (n : ℝ) ∨
          ((C ∩ Finset.Icc 1 ((n / 2 : ℕ) : ℤ)).card : ℝ) ≤
            (n : ℝ) / 2 - (C.card : ℝ) + ε * (n : ℝ) ∨
          ((C \ odds n).card : ℝ) ≤ ε * (n : ℝ) := by
  set ε₁ : ℝ := min (ε / 4) (1 / 220) with hε₁
  have hε₁pos : 0 < ε₁ := lt_min (by linarith) (by norm_num)
  have hε₁ε : ε₁ ≤ ε / 4 := min_le_left _ _
  have hε₁2 : ε₁ ≤ 1 / 220 := min_le_right _ _
  obtain ⟨δ, hδ, hrem⟩ := hSR ε₁ hε₁pos
  refine ⟨δ, hδ, ?_⟩
  filter_upwards [hrem, hDFST, Filter.eventually_ge_atTop ⌈2 / ε⌉₊,
    Filter.eventually_ge_atTop 221] with n hremn hDFSTn hn2 hn221
  intro C hCI hsp
  rcases le_or_gt (C.card : ℝ) ((1 / 2 - 1 / 11) * (n : ℝ)) with
    hsmall | hbig
  · exact Or.inl hsmall
  obtain ⟨t, htC, htsf, htsd⟩ := hremn C hCI hsp
  have htI : t ⊆ interval n := htC.trans hCI
  have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hCt : (C.card : ℝ) ≤ (t.card : ℝ) + ((C \ t).card : ℝ) := by
    have h := Finset.card_union_le t (C \ t)
    rw [Finset.union_sdiff_of_subset htC] at h
    exact_mod_cast h
  -- `|t| > 2n/5 + 1`, killing DFST alternative (i):
  -- `|t| > (1/2 − 1/11 − ε₁)n ≥ (2/5 + 1/220)n ≥ 2n/5 + 221/220`.
  have htbig : (2 / 5 : ℝ) * (n : ℝ) + 1 < (t.card : ℝ) := by
    have hε₁n : ε₁ * (n : ℝ) ≤ (1 / 220) * (n : ℝ) :=
      mul_le_mul_of_nonneg_right hε₁2 hnn
    have hnn' : (221 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn221
    have h1 : (t.card : ℝ) > (1 / 2 - 1 / 11 - ε₁) * (n : ℝ) := by
      linarith [hCt, htsd, hbig]
    linarith [h1, hε₁n, hnn']
  rcases hDFSTn t htI htsf with h1 | h2 | h3
  · exact absurd h1 (not_le_of_gt htbig)
  · -- `t ⊆ odds n`: then `C ∖ odds n ⊆ C ∖ t`, so `|C ∖ odds| ≤ ε₁n ≤ εn`.
    refine Or.inr (Or.inr ?_)
    have hsub : C \ odds n ⊆ C \ t := by
      intro x hx
      rw [Finset.mem_sdiff] at hx ⊢
      exact ⟨hx.1, fun hxt => hx.2 (h2 hxt)⟩
    calc ((C \ odds n).card : ℝ) ≤ ((C \ t).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
      _ ≤ ε₁ * (n : ℝ) := htsd
      _ ≤ ε * (n : ℝ) :=
          mul_le_mul_of_nonneg_right (hε₁ε.trans (by linarith)) hnn
  · -- `∀ x ∈ t, |t| ≤ x`: the elements of `C` below `|t|` lie in `C ∖ t`,
    -- and `C ∩ [1, ⌊n/2⌋] ⊆ (C ∖ t) ∪ Icc |t| ⌊n/2⌋`.
    refine Or.inr (Or.inl ?_)
    set k : ℤ := ((n / 2 : ℕ) : ℤ) with hk
    have hsplit : C ∩ Finset.Icc 1 k ⊆
        (C \ t) ∪ Finset.Icc (t.card : ℤ) k := by
      intro x hx
      obtain ⟨hxC, hxIcc⟩ := Finset.mem_inter.mp hx
      obtain ⟨-, hxle⟩ := Finset.mem_Icc.mp hxIcc
      by_cases hxt : x ∈ t
      · exact Finset.mem_union.mpr
          (Or.inr (Finset.mem_Icc.mpr ⟨h3 x hxt, hxle⟩))
      · exact Finset.mem_union.mpr
          (Or.inl (Finset.mem_sdiff.mpr ⟨hxC, hxt⟩))
    have hcard1 : ((C ∩ Finset.Icc 1 k).card : ℝ) ≤
        ((C \ t).card : ℝ) + ((Finset.Icc (t.card : ℤ) k).card : ℝ) := by
      have h := (Finset.card_le_card hsplit).trans
        (Finset.card_union_le _ _)
      exact_mod_cast h
    have hIcc : (Finset.Icc (t.card : ℤ) k).card =
        (k + 1 - (t.card : ℤ)).toNat := Int.card_Icc _ _
    -- `|t| ≤ (n+1)/2` since `t` is sum-free.
    have htle : (t.card : ℝ) ≤ ((n : ℝ) + 1) / 2 := by
      have h : t.card ≤ (n + 1) / 2 := card_le_of_isSumFree htI htsf
      have h' : (t.card : ℝ) ≤ (((n + 1) / 2 : ℕ) : ℝ) := by
        exact_mod_cast h
      refine h'.trans ?_
      calc (((n + 1) / 2 : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) / 2 :=
          Nat.cast_div_le
        _ = ((n : ℝ) + 1) / 2 := by norm_cast
    have hkR : (k : ℝ) ≤ (n : ℝ) / 2 := by
      have h' : (((n / 2 : ℕ) : ℤ) : ℝ) ≤ (n : ℝ) / 2 := by
        calc (((n / 2 : ℕ) : ℤ) : ℝ) = ((n / 2 : ℕ) : ℝ) := by norm_cast
          _ ≤ (n : ℝ) / 2 := Nat.cast_div_le
      rw [hk]; exact h'
    have hIccR : ((Finset.Icc (t.card : ℤ) k).card : ℝ) ≤
        (n : ℝ) / 2 - (t.card : ℝ) + 1 := by
      rw [hIcc]
      rcases le_or_gt (0 : ℤ) (k + 1 - (t.card : ℤ)) with hz | hz
      · have hcast : (((k + 1 - (t.card : ℤ)).toNat : ℕ) : ℝ) =
            ((k + 1 - (t.card : ℤ)) : ℝ) := by
          exact_mod_cast Int.toNat_of_nonneg hz
        rw [hcast]
        push_cast
        linarith [hkR]
      · rw [Int.toNat_eq_zero.mpr hz.le]
        have hz0 : (0 : ℝ) ≤ (n : ℝ) / 2 - (t.card : ℝ) + 1 := by
          linarith [htle]
        exact_mod_cast hz0
    -- `|C∩[1,⌊n/2⌋]| ≤ |C∖t| + n/2 − |t| + 1 ≤ n/2 − |C| + 2ε₁n + 1 ≤ …`.
    have h2ε : 2 * ε₁ * (n : ℝ) + 1 ≤ ε * (n : ℝ) := by
      have h1' : ε₁ * (n : ℝ) ≤ (ε / 4) * (n : ℝ) :=
        mul_le_mul_of_nonneg_right hε₁ε hnn
      have h2' : (2 : ℝ) / ε ≤ (n : ℝ) := by
        have hceil : (2 / ε : ℝ) ≤ (⌈2 / ε⌉₊ : ℝ) := Nat.le_ceil _
        exact hceil.trans (by exact_mod_cast hn2)
      have h3' : (2 : ℝ) ≤ ε * (n : ℝ) := by
        rw [div_le_iff₀ hε] at h2'
        linarith [h2']
      linarith [h1', h3']
    calc ((C ∩ Finset.Icc 1 k).card : ℝ)
        ≤ ((C \ t).card : ℝ) +
            ((Finset.Icc (t.card : ℤ) k).card : ℝ) := hcard1
      _ ≤ ε₁ * (n : ℝ) + ((n : ℝ) / 2 - (t.card : ℝ) + 1) := by
          linarith [htsd, hIccR]
      _ ≤ (n : ℝ) / 2 - (C.card : ℝ) + (2 * ε₁ * (n : ℝ) + 1) := by
          linarith [hCt, htsd]
      _ ≤ (n : ℝ) / 2 - (C.card : ℝ) + ε * (n : ℝ) := by
          linarith [h2ε]

/-! ## Case (c): odd-type containers and the master assembly -/

/-- **Odd-container bound** (hypothesis): for every `ε > 0`, eventually,
every *even-elemented* sum-free fingerprint `S ⊆ {1,…,n}` has at most
`2^{(1/4 + ε)n}` maximal link-independent subsets of `odds n`.

This is the content of BLST Lemma 3.4: for `x, y ∈ odds n` and `s ∈ S ⊆ E`
the link edge `x ~ y` is a sum edge (`x + y ∈ S`, "red") or a difference
edge (`|x − y| ∈ S`, "blue"); one splits on `|S|`:

* `|S| ≥ n^{1/4}` — `L_S[odds n]` is almost regular
  (`δ(G) ≥ |S|/2`, `Δ(G) ≤ 2|S| + 2`), so the Sapozhenko-type almost-regular
  MIS bound gives `3^{n/7 + o(n)} = o(2^{n/4})`;
* `|S| ≤ n^{1/4}` — every triangle has 0 or 2 blue edges, and each triangle
  is forced by a multiset of at most `3!` orderings of a triple from `S`,
  so `#triangles ≤ 24|S|³ = o(n)`; deleting the `o(n)` triangle vertices
  leaves a triangle-free graph, whence `MIS ≤ 2^{n/4 + o(n)}`. -/
def OddContainerBound : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in Filter.atTop,
    ∀ S : Finset ℤ, S ⊆ interval n → IsSumFree S →
      (∀ x ∈ S, x % 2 = 0) →
      ((linkMaxSets S (odds n)).card : ℝ) ≤
        2 ^ ((1 / 4 + ε) * (n : ℝ))

/-- **Master assembly: `SparseFingerprintBound` from removal + DFST +
odd-container bound.**  For a `δn²`-sparse container `C ⊆ {1,…,n}`:

* if `|C| ≤ (1/2 − 1/11)n ≤ 9n/20`, removal gives `C ⊆ t ∪ (C ∖ t)` with
  `t` sum-free, `|t| ≤ |C| ≤ 9n/20`, `|C ∖ t| ≤ εn/8`, and the small
  container lemma gives `2^{εn/8 + n/4}`;
* otherwise `container_trichotomy` applies:
  * interval-type: `#{M ⊆ C} ≤ 2^{(|C| + |C∩[1,⌊n/2⌋]|)/2}
    ≤ 2^{(n/2 + εn/4)/2} = 2^{n/4 + εn/8}`;
  * odd-type: `C ⊆ odds n ∪ (C ∖ odds n)`, and over sum-free fingerprints
    `S ⊆ C ∖ odds n ⊆ E` the `OddContainerBound` gives
    `#{M ⊆ C} ≤ 2^{|C ∖ odds|} · 2^{(1/4 + ε/4)n} ≤ 2^{(1/4 + ε/2)n}`. -/
theorem sparseFingerprintBound_of_removal_dfst_odd
    (hSR : SchurRemoval) (hDFST : DFST) (hOCB : OddContainerBound) :
    SparseFingerprintBound := by
  intro ε hε
  have hε4 : 0 < ε / 4 := by linarith
  obtain ⟨δ₁, hδ₁, htr⟩ := container_trichotomy hSR hDFST hε4
  obtain ⟨δ₂, hδ₂, hrem⟩ := hSR (ε / 8) (by linarith)
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
  filter_upwards [htr, hrem, hOCB (ε / 4) hε4,
    Filter.eventually_ge_atTop 1] with n htrn hremn hOCBn hn1
  intro C hCI hsp
  have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hεn : (0 : ℝ) ≤ ε * (n : ℝ) := mul_nonneg hε.le hnn
  have hsp1 : (schurTripleCount C : ℝ) ≤ δ₁ * (n : ℝ) ^ 2 :=
    hsp.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg _))
  have hsp2 : (schurTripleCount C : ℝ) ≤ δ₂ * (n : ℝ) ^ 2 :=
    hsp.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg _))
  rcases le_or_gt (C.card : ℝ) ((1 / 2 - 1 / 11) * (n : ℝ)) with
    hsmall | hbig
  · -- Case (a): small container.
    obtain ⟨t, htC, htsf, htsd⟩ := hremn C hCI hsp2
    have hcover : C ⊆ t ∪ (C \ t) :=
      Finset.subset_of_eq (Finset.union_sdiff_of_subset htC).symm
    have htA : (t.card : ℝ) ≤ (9 / 20 : ℝ) * (n : ℝ) := by
      have hle : (t.card : ℝ) ≤ (C.card : ℝ) := by
        exact_mod_cast Finset.card_le_card htC
      linarith [hsmall, hle, hnn]
    calc (((maxSumFreeSets n).filter (· ⊆ C)).card : ℝ)
        ≤ (2 : ℝ) ^ (((C \ t).card : ℝ) + (1 / 4 : ℝ) * (n : ℝ)) :=
          maxSumFreeCount_filter_le_of_small_container (htC.trans hCI)
            htsf hcover htA
      _ ≤ (2 : ℝ) ^ ((1 / 4 + ε) * (n : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num)
            (by linarith [htsd, hεn])
  · rcases htrn C hCI hsp1 with h1 | h2 | h3
    · exact absurd h1 (not_le_of_gt hbig)
    · -- Case (b): interval-type container.
      calc (((maxSumFreeSets n).filter (· ⊆ C)).card : ℝ)
          ≤ (2 : ℝ) ^ (((C.card : ℝ) +
              ((C ∩ Finset.Icc 1 ((n / 2 : ℕ) : ℤ)).card : ℝ)) / 2) :=
            maxSumFreeCount_filter_le_of_interval_container hCI
        _ ≤ (2 : ℝ) ^ ((1 / 4 + ε) * (n : ℝ)) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num)
              (by linarith [h2, hεn])
    · -- Case (c): odd-type container.
      have hcover : C ⊆ odds n ∪ (C \ odds n) := by
        intro x hx
        rw [Finset.mem_union]
        by_cases hxo : x ∈ odds n
        · exact Or.inl hxo
        · exact Or.inr (Finset.mem_sdiff.mpr ⟨hx, hxo⟩)
      have hmono : ((maxSumFreeSets n).filter (· ⊆ C)).card ≤
          ((maxSumFreeSets n).filter
            (· ⊆ odds n ∪ (C \ odds n))).card :=
        card_filter_subset_mono hcover
      have hb : ∀ S : Finset ℤ, S ⊆ C \ odds n → IsSumFree S →
          ((linkMaxSets S (odds n)).card : ℝ) ≤
            (2 : ℝ) ^ ((1 / 4 + ε / 4) * (n : ℝ)) := by
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
      calc (((maxSumFreeSets n).filter (· ⊆ C)).card : ℝ)
          ≤ (((maxSumFreeSets n).filter
              (· ⊆ odds n ∪ (C \ odds n))).card : ℝ) := by
            exact_mod_cast hmono
        _ ≤ (2 : ℝ) ^ ((C \ odds n).card : ℝ) *
              (2 : ℝ) ^ ((1 / 4 + ε / 4) * (n : ℝ)) := hbound
        _ = (2 : ℝ) ^ (((C \ odds n).card : ℝ) +
              (1 / 4 + ε / 4) * (n : ℝ)) := by
            rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        _ ≤ (2 : ℝ) ^ ((1 / 4 + ε) * (n : ℝ)) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num)
              (by linarith [h3, hεn])

/-- **Conditional BLST headline.**  The full prize path is isolated as
`ContainerExistence → SchurRemoval → DFST → OddContainerBound →
SharpAsymptotic`: Green's container lemma supplies `2^{o(n)}` sparse
containers, removal + DFST classify each container as
small/interval-type/odd-type, and the three counting lemmas bound the
maximal sum-free sets housed by each. -/
theorem sharpAsymptotic_of_containerExistence_removal_dfst_odd
    (hCE : ContainerExistence) (hSR : SchurRemoval) (hDFST : DFST)
    (hOCB : OddContainerBound) : SharpAsymptotic :=
  sharpAsymptotic_of_sparse_container_fingerprint hCE
    (sparseFingerprintBound_of_removal_dfst_odd hSR hDFST hOCB)

end JSP000728
