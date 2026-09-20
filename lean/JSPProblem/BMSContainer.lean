import JSPProblem.Supersat3
import JSPProblem.ScanContainer
import JSPProblem.Removal
import JSPProblem.Prize
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# JSP-000728 — the BMS/Saxton–Thomason simple-container lemma

This file proves `containerExistence : ContainerExistence` — the
Green/Balogh–Morris–Samotij container lemma for sum-free subsets of
`{1,…,n}` — by formalizing the *simple containers* argument of
Saxton–Thomason (arXiv:1402.5400) specialized to the Schur 3-uniform
hypergraph.

## The construction in one paragraph

For a sum-free `I ⊆ A` (with `A` the current container), edges are the
3-subsets `{a, b, a+b} ⊆ A`.  Write `E_j(A')` for the edges of `A'` with at
least `j` elements in `I`, and let `P(j)` be the statement that every
`A' ⊇ I` of degree-measure `≥ 5/6 + j/18` satisfies `|E_j(A')| ≥ τ_j`.
`P(0)` is true (degree counting), `P(3)` is false (no edge lies inside `I`),
so there is a level `j ∈ {0,1,2}` with `P(j)` true and `P(j+1)` false, with
witness `A'`.  The vertices `D ⊆ A' ∖ I` carrying many `j`-edges have total
degree-measure `> 1/18`.  Sampling `W ⊆ A'` by including each element with
probability `p`, the "shadow" `Γ_j(W)` of vertices whose incident `j`-edge
lies in `W` covers half of `D` with positive probability while `W`, and the
trace `T = Γ_j(W) ∩ I`, stay small.  Recording `(j, R, S, T) = (j, W∩I,
W∩(A'∖I), Γ_j(W)∩I)` determines the container `C = (A ∖ Γ_j(R,S)) ∪ T ⊇ I`
with `e(C) ≤ (35/36)·e(A)`.  Iterating `Θ(log(1/δ))` rounds drives the edge
count below `δ n²`, and every round's fingerprint has size `O_δ(n^{3/4})`,
so the family has `2^{o(n)}` members.

## Contents

* `bernWt`, `bern_total`, `bern_mem`, `bern_subset`, `bern_card`,
  `bern_all_miss_disjoint`, `bern_markov` — the product measure on
  `powerset A` and its basic calculus.
* `schurEdges`, `schurEdgeCount`, `edgeDeg`, `degSum` — the Schur
  3-uniform hypergraph and degree measure.
* `exists_round_data` — the one-round lemma.
* `bmsStep`, `bmsContainer`, `bmsFamily` — the iteration and family.
* `containerExistence` — the headline theorem.
* `sharpAsymptotic_of_removal_dfst` — the conditional sharp asymptotic.
-/

namespace JSP000728

open Filter Finset
open scoped Topology

/-! ## The product measure on `powerset A`

For `p ∈ ℝ` and a finite set `A`, the weight
`bernWt A p W = p^{|W|}·(1−p)^{|A∖W|}` is a probability mass function on
`A.powerset` whenever `0 ≤ p ≤ 1`.  All the estimates we need are exact
algebraic identities on `Finset.sum`s. -/

/-- The Bernoulli weight of `W ⊆ A`: each element of `W` contributes `p` and
each element of `A ∖ W` contributes `1 − p`. -/
def bernWt (A : Finset ℤ) (p : ℝ) (W : Finset ℤ) : ℝ :=
  p ^ W.card * (1 - p) ^ (A \ W).card

theorem bernWt_nonneg {A : Finset ℤ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (W : Finset ℤ) : 0 ≤ bernWt A p W :=
  mul_nonneg (pow_nonneg hp0 _) (pow_nonneg (by linarith) _)

/-- Total mass is `1` (for any `p`): `∑_{W ⊆ A} p^{|W|}(1−p)^{|A∖W|} =
(p + (1−p))^{|A|} = 1`. -/
theorem bern_total (A : Finset ℤ) (p : ℝ) :
    ∑ W ∈ A.powerset, bernWt A p W = 1 := by
  have h := Finset.prod_add (fun _ : ℤ => p) (fun _ : ℤ => 1 - p) A
  simp only [Finset.prod_const] at h
  rw [show p + (1 - p) = 1 by ring, one_pow] at h
  simp only [bernWt]
  exact h.symm

/-- The weight splits along a subset: for `f ⊆ W ⊆ A`,
`wt_A(W) = p^{|f|} · wt_{A∖f}(W ∖ f)`. -/
theorem bernWt_split {A W f : Finset ℤ} {p : ℝ} (hf : f ⊆ W) (hW : W ⊆ A) :
    bernWt A p W = p ^ f.card * bernWt (A \ f) p (W \ f) := by
  unfold bernWt
  have h1 : W.card = f.card + (W \ f).card := by
    have hunion : (W \ f) ∪ f = W := Finset.sdiff_union_of_subset hf
    have hdisj : Disjoint (W \ f) f :=
      Finset.disjoint_left.mpr fun x hx => (Finset.mem_sdiff.mp hx).2
    have := Finset.card_union_of_disjoint hdisj
    rw [hunion] at this
    omega
  have h2 : A \ W = (A \ f) \ (W \ f) := by
    ext x
    simp only [Finset.mem_sdiff, not_and]
    constructor
    · rintro ⟨hxA, hxW⟩
      exact ⟨⟨hxA, fun hxf => hxW (hf hxf)⟩, fun hxW' => absurd hxW' hxW⟩
    · rintro ⟨⟨hxA, hxf⟩, hxWf⟩
      exact ⟨hxA, fun hxW => (hxWf hxW) hxf⟩
  rw [h2, h1, pow_add]
  ring

/-- **Containment probability.**  For `f ⊆ A`, the total weight of the sets
`W ⊆ A` containing `f` is exactly `p^{|f|}`: the map `W ↦ W ∖ f` is a
weight-rescaling bijection onto `powerset (A ∖ f)`. -/
theorem bern_subset {A f : Finset ℤ} {p : ℝ} (hf : f ⊆ A) :
    ∑ W ∈ A.powerset.filter (f ⊆ ·), bernWt A p W = p ^ f.card := by
  classical
  have hbij : (A.powerset.filter (f ⊆ ·)) =
      (A \ f).powerset.image (· ∪ f) := by
    ext W
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_image]
    constructor
    · rintro ⟨hWA, hfW⟩
      exact ⟨W \ f, Finset.sdiff_subset_sdiff hWA (Finset.Subset.refl _),
        Finset.sdiff_union_of_subset hfW⟩
    · rintro ⟨U, hU, rfl⟩
      exact ⟨Finset.union_subset (Finset.Subset.trans hU Finset.sdiff_subset)
        hf, Finset.subset_union_right⟩
  have hinj : Set.InjOn (· ∪ f)
      ((A \ f).powerset : Set (Finset ℤ)) := by
    intro U hU V hV hUV
    simp only [Finset.mem_coe, Finset.mem_powerset] at hU hV
    have hUV' : U ∪ f = V ∪ f := hUV
    ext x
    constructor
    · intro hx
      have hx' : x ∈ V ∪ f := hUV' ▸ Finset.mem_union_left f hx
      rcases Finset.mem_union.mp hx' with hx' | hx'
      · exact hx'
      · exact absurd hx' (Finset.mem_sdiff.mp (hU hx)).2
    · intro hx
      have hx' : x ∈ U ∪ f := hUV'.symm ▸ Finset.mem_union_left f hx
      rcases Finset.mem_union.mp hx' with hx' | hx'
      · exact hx'
      · exact absurd hx' (Finset.mem_sdiff.mp (hV hx)).2
  rw [hbij, Finset.sum_image hinj]
  rw [show p ^ f.card = p ^ f.card * 1 from (mul_one _).symm,
    ← bern_total (A \ f) p, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro U hU
  rw [Finset.mem_powerset] at hU
  have hsd : (U ∪ f) \ f = U := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_union]
    constructor
    · rintro ⟨hx | hx, hnf⟩
      · exact hx
      · exact absurd hx hnf
    · intro hx
      exact ⟨Or.inl hx, (Finset.mem_sdiff.mp (hU hx)).2⟩
  have hsub : f ⊆ U ∪ f := Finset.subset_union_right
  have hW : U ∪ f ⊆ A :=
    Finset.union_subset (Finset.Subset.trans hU Finset.sdiff_subset) hf
  rw [bernWt_split hsub hW, hsd]

/-- **Point probability.**  For `x ∈ A`, the total weight of `W ∋ x` is `p`. -/
theorem bern_mem {A : Finset ℤ} {p : ℝ} {x : ℤ} (hx : x ∈ A) :
    ∑ W ∈ A.powerset.filter (x ∈ ·), bernWt A p W = p := by
  have h := bern_subset (A := A) (f := {x}) (p := p)
    (Finset.singleton_subset_iff.mpr hx)
  rw [Finset.card_singleton, pow_one] at h
  convert h using 2
  ext W
  simp only [Finset.mem_filter, Finset.mem_powerset,
    Finset.singleton_subset_iff]

/-- **Expected size.**  `∑_W wt(W)·|W ∩ X| = p·|X|` for `X ⊆ A`. -/
theorem bern_card {A X : Finset ℤ} {p : ℝ} (hX : X ⊆ A) :
    ∑ W ∈ A.powerset, bernWt A p W * ((W ∩ X).card : ℝ) = p * X.card := by
  classical
  have hrewrite : ∀ W : Finset ℤ,
      ((W ∩ X).card : ℝ) = ∑ x ∈ X, if x ∈ W then (1 : ℝ) else 0 := by
    intro W
    have h : (W ∩ X).card = ∑ x ∈ X, (if x ∈ W then 1 else 0 : ℕ) := by
      rw [← Finset.card_filter]
      congr 1
      rw [Finset.filter_mem_eq_inter, Finset.inter_comm]
    exact_mod_cast h
  rw [Finset.sum_congr rfl fun W _ => congrArg (bernWt A p W * ·) (hrewrite W)]
  rw [Finset.sum_congr rfl fun W _ => Finset.mul_sum _ _ _]
  rw [Finset.sum_comm]
  rw [show (∑ x ∈ X, ∑ W ∈ A.powerset,
      bernWt A p W * (if x ∈ W then (1:ℝ) else 0)) =
      ∑ x ∈ X, p by
    apply Finset.sum_congr rfl
    intro x hx
    have hite : ∀ W : Finset ℤ,
        bernWt A p W * (if x ∈ W then (1:ℝ) else 0) =
          if x ∈ W then bernWt A p W else 0 := by
      intro W
      by_cases hW : x ∈ W
      · rw [if_pos hW, if_pos hW, mul_one]
      · rw [if_neg hW, if_neg hW, mul_zero]
    rw [Finset.sum_congr rfl fun W _ => hite W, ← Finset.sum_filter,
      bern_mem (hX hx)]]
  rw [Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- **Missing a fixed disjoint family.**  For a pairwise-disjoint family
`M` of subsets of `A`, the total weight of `W ⊆ A` containing no member of
`M` equals `∏_{s ∈ M} (1 − p^{|s|})`: inclusion–exclusion over the contained
subfamily, using disjointness for `|⋃| = Σ|·|`. -/
theorem bern_all_miss_disjoint {A : Finset ℤ} {p : ℝ} (M : Finset (Finset ℤ))
    (hsub : ∀ s ∈ M, s ⊆ A)
    (hdisj : ∀ s ∈ M, ∀ t ∈ M, s ≠ t → Disjoint s t) :
    ∑ W ∈ A.powerset.filter (fun W => ∀ s ∈ M, ¬ s ⊆ W), bernWt A p W =
      ∏ s ∈ M, (1 - p ^ s.card) := by
  classical
  -- The indicator of "W misses every s ∈ M" is a product of 0/1 factors.
  have hind : ∀ W : Finset ℤ,
      (if (∀ s ∈ M, ¬ s ⊆ W) then (1 : ℝ) else 0) =
        ∏ s ∈ M, (1 - if s ⊆ W then (1 : ℝ) else 0) := by
    intro W
    by_cases hW : ∀ s ∈ M, ¬ s ⊆ W
    · rw [if_pos hW]
      symm
      apply Finset.prod_eq_one
      intro s hs
      rw [if_neg (hW s hs), sub_zero]
    · rw [if_neg hW]
      symm
      push_neg at hW
      obtain ⟨s, hsM, hsW⟩ := hW
      apply Finset.prod_eq_zero hsM
      rw [if_pos hsW, sub_self]
  -- Expand the product via `prod_add` and resum over powerset.
  have hexpand : ∀ W : Finset ℤ,
      (∏ s ∈ M, (1 - if s ⊆ W then (1 : ℝ) else 0)) =
        ∑ J ∈ M.powerset,
          (-1 : ℝ) ^ J.card *
            (if (J.biUnion id) ⊆ W then (1 : ℝ) else 0) := by
    intro W
    have h := Finset.prod_add
      (fun s : Finset ℤ => - if s ⊆ W then (1 : ℝ) else 0)
      (fun _ : Finset ℤ => (1 : ℝ)) M
    rw [show (∏ s ∈ M, ((- if s ⊆ W then (1 : ℝ) else 0) + 1)) =
        ∏ s ∈ M, (1 - if s ⊆ W then (1 : ℝ) else 0) by
      apply Finset.prod_congr rfl
      intro s _; ring] at h
    rw [h]
    apply Finset.sum_congr rfl
    intro J hJ
    rw [Finset.mem_powerset] at hJ
    have hprod : (∏ s ∈ J, (- if s ⊆ W then (1 : ℝ) else 0)) =
        (-1 : ℝ) ^ J.card *
          (if (J.biUnion id) ⊆ W then (1 : ℝ) else 0) := by
      have hneg : ∀ s : Finset ℤ,
          (- if s ⊆ W then (1 : ℝ) else 0) =
            (-1) * (if s ⊆ W then (1 : ℝ) else 0) := fun s => by
        by_cases hs : s ⊆ W <;> simp [hs]
      rw [Finset.prod_congr rfl fun s _ => hneg s,
        Finset.prod_mul_distrib, Finset.prod_const]
      congr 1
      by_cases hall : ∀ s ∈ J, s ⊆ W
      · have hsup : J.biUnion id ⊆ W := by
          intro x hx
          rw [mem_biUnion] at hx
          obtain ⟨s, hsJ, hxs⟩ := hx
          exact hall s hsJ hxs
        rw [if_pos hsup]
        apply Finset.prod_eq_one
        intro s hs
        rw [if_pos (hall s hs)]
      · push_neg at hall
        obtain ⟨s, hsJ, hsW⟩ := hall
        have hnsup : ¬ J.biUnion id ⊆ W := by
          intro hsup
          exact hsW fun x hx => hsup (mem_biUnion.mpr ⟨s, hsJ, hx⟩)
        rw [if_neg hnsup]
        apply Finset.prod_eq_zero hsJ
        rw [if_neg hsW]
    rw [hprod, Finset.prod_const, one_pow, mul_one]
  -- Resum: the filtered sum equals the expansion.
  have hsum : ∑ W ∈ A.powerset.filter (fun W => ∀ s ∈ M, ¬ s ⊆ W),
      bernWt A p W =
      ∑ W ∈ A.powerset, bernWt A p W *
        (if (∀ s ∈ M, ¬ s ⊆ W) then (1 : ℝ) else 0) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro W _
    by_cases hW : ∀ s ∈ M, ¬ s ⊆ W
    · rw [if_pos hW, if_pos hW, mul_one]
    · rw [if_neg hW, if_neg hW, mul_zero]
  rw [hsum, Finset.sum_congr rfl fun W _ => congrArg (bernWt A p W * ·) (hind W)]
  rw [Finset.sum_congr rfl fun W _ =>
    (congrArg (bernWt A p W * ·) (hexpand W)).trans
      (Finset.mul_sum (a := bernWt A p W) (s := M.powerset)
        (f := fun J => (-1 : ℝ) ^ J.card *
          (if J.biUnion id ⊆ W then (1 : ℝ) else 0)))]
  -- Swap the sums and evaluate each `J`-term via `bern_subset`.
  rw [Finset.sum_comm]
  have hterm : ∀ J ∈ M.powerset,
      (∑ W ∈ A.powerset, bernWt A p W *
          ((-1 : ℝ) ^ J.card *
            (if (J.biUnion id) ⊆ W then (1 : ℝ) else 0))) =
        (-1 : ℝ) ^ J.card * p ^ (J.biUnion id).card := by
    intro J hJ
    rw [Finset.mem_powerset] at hJ
    have hJsub : J.biUnion id ⊆ A := by
      intro x hx
      rw [mem_biUnion] at hx
      obtain ⟨s, hsJ, hxs⟩ := hx
      exact hsub s (hJ hsJ) hxs
    have hfactor : ∀ W : Finset ℤ,
        bernWt A p W * ((-1 : ℝ) ^ J.card *
          (if (J.biUnion id) ⊆ W then (1 : ℝ) else 0)) =
          (-1 : ℝ) ^ J.card *
            (if (J.biUnion id) ⊆ W then bernWt A p W else 0) := by
      intro W
      by_cases hW : J.biUnion id ⊆ W
      · rw [if_pos hW, if_pos hW]; ring
      · rw [if_neg hW, if_neg hW]; ring
    rw [Finset.sum_congr rfl fun W _ => hfactor W, ← Finset.mul_sum,
      ← Finset.sum_filter, bern_subset hJsub]
  rw [Finset.sum_congr rfl hterm]
  -- Each `J`-term factors: `p^{|⋃J|} = ∏_{s∈J} p^{|s|}` by disjointness.
  have hcard : ∀ J ∈ M.powerset,
      (J.biUnion id).card = ∑ s ∈ J, s.card := by
    intro J hJ
    rw [Finset.mem_powerset] at hJ
    rw [Finset.card_biUnion (t := id)
      (by
        intro s hsJ t htJ hst
        exact hdisj s (hJ (Finset.mem_coe.mp hsJ)) t
          (hJ (Finset.mem_coe.mp htJ)) hst)]
    rfl
  rw [Finset.sum_congr rfl fun J hJ => by
    rw [hcard J hJ, ← Finset.prod_pow_eq_pow_sum]]
  -- Fold back with `prod_add`.
  have h := Finset.prod_add (fun s : Finset ℤ => - p ^ s.card)
    (fun _ : Finset ℤ => (1 : ℝ)) M
  rw [show (∏ s ∈ M, ((- p ^ s.card) + 1)) = ∏ s ∈ M, (1 - p ^ s.card) by
    apply Finset.prod_congr rfl
    intro s _; ring] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro J _
  rw [Finset.prod_const, one_pow, mul_one]
  have hneg : ∀ s : Finset ℤ, -p ^ s.card = (-1 : ℝ) * p ^ s.card :=
    fun s => by ring
  rw [Finset.prod_congr rfl fun s _ => hneg s, Finset.prod_mul_distrib,
    Finset.prod_const]

/-- **Markov's inequality.**  For a nonnegative `g` and `t > 0`, the weight of
`{W : t ≤ g W}` is at most `E[g]/t`. -/
theorem bern_markov {A : Finset ℤ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (g : Finset ℤ → ℝ) (hg : ∀ W, 0 ≤ g W) {t : ℝ} (ht : 0 < t) :
    ∑ W ∈ A.powerset.filter (fun W => t ≤ g W), bernWt A p W ≤
      (∑ W ∈ A.powerset, bernWt A p W * g W) / t := by
  rw [Finset.sum_filter, le_div_iff₀ ht, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro W _
  by_cases h : t ≤ g W
  · rw [if_pos h]
    exact mul_le_mul_of_nonneg_left h (bernWt_nonneg hp0 hp1 W)
  · rw [if_neg h, zero_mul]
    exact mul_nonneg (bernWt_nonneg hp0 hp1 W) (hg W)

/-- **Union bound.**  Bad events each of weight `≤ aᵢ` with `Σaᵢ < 1` leave a
good `W ⊆ A`. -/
theorem bern_exists_good {A : Finset ℤ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {k : ℕ} (bad : Fin k → (Finset ℤ → Prop))
    [∀ i, DecidablePred (bad i)]
    (a : Fin k → ℝ)
    (hb : ∀ i, ∑ W ∈ A.powerset.filter (fun W => bad i W), bernWt A p W ≤ a i)
    (hsum : ∑ i, a i < 1) :
    ∃ W ⊆ A, ∀ i, ¬ bad i W := by
  classical
  have hw : ∀ W, (if ∃ i, bad i W then (1 : ℝ) else 0) ≤
      ∑ i, (if bad i W then (1 : ℝ) else 0) := by
    intro W
    by_cases hW : ∃ i, bad i W
    · rw [if_pos hW]
      obtain ⟨i, hi⟩ := hW
      calc (1 : ℝ) = if bad i W then (1 : ℝ) else 0 := by
            rw [if_pos hi]
        _ ≤ ∑ j, (if bad j W then (1 : ℝ) else 0) :=
            Finset.single_le_sum (f := fun j =>
              if bad j W then (1 : ℝ) else 0)
              (fun j _ => by by_cases hj : bad j W <;> simp [hj])
              (Finset.mem_univ i)
    · rw [if_neg hW]
      exact Finset.sum_nonneg fun j _ => by
        by_cases hj : bad j W <;> simp [hj]
  have htot : ∑ W ∈ A.powerset, bernWt A p W *
      (if ∃ i, bad i W then (1 : ℝ) else 0) < 1 := by
    calc ∑ W ∈ A.powerset, bernWt A p W *
          (if ∃ i, bad i W then (1 : ℝ) else 0)
        ≤ ∑ W ∈ A.powerset, bernWt A p W *
            (∑ i, (if bad i W then (1 : ℝ) else 0)) :=
          Finset.sum_le_sum fun W _ =>
            mul_le_mul_of_nonneg_left (hw W) (bernWt_nonneg hp0 hp1 W)
      _ = ∑ i, ∑ W ∈ A.powerset,
            bernWt A p W * (if bad i W then (1 : ℝ) else 0) := by
          rw [Finset.sum_congr rfl fun W _ => Finset.mul_sum _ _ _]
          rw [Finset.sum_comm]
      _ = ∑ i, ∑ W ∈ A.powerset.filter (fun W => bad i W),
            bernWt A p W := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro W _
          by_cases hW : bad i W
          · rw [if_pos hW, if_pos hW, mul_one]
          · rw [if_neg hW, if_neg hW, mul_zero]
      _ ≤ ∑ i, a i := Finset.sum_le_sum fun i _ => hb i
      _ < 1 := hsum
  by_contra hcon
  push_neg at hcon
  have : ∀ W ∈ A.powerset, ∃ i, bad i W := by
    intro W hW
    rw [Finset.mem_powerset] at hW
    exact hcon W hW
  have hge : (1 : ℝ) ≤ ∑ W ∈ A.powerset, bernWt A p W *
      (if ∃ i, bad i W then (1 : ℝ) else 0) := by
    calc (1 : ℝ) = ∑ W ∈ A.powerset, bernWt A p W := (bern_total A p).symm
      _ ≤ ∑ W ∈ A.powerset, bernWt A p W *
            (if ∃ i, bad i W then (1 : ℝ) else 0) := by
          apply Finset.sum_le_sum
          intro W hW
          rw [if_pos (this W hW), mul_one]
  linarith [htot, hge]

/-! ## The Schur hypergraph on an ambient set

We work with the 3-uniform hypergraph of *strict* Schur edges: 3-element
subsets `{x,y,z} ⊆ A` containing two distinct elements `x ≠ y` with
`x + y ∈ {x,y,z}`.  Restricting to distinct witnesses keeps the co-degree of
every pair at most `3`, which is what makes the Saxton–Thomason independence
argument work. -/

/-- The strict Schur edges inside `A`: 3-element subsets `{x,y,z}` with
`x ≠ y` and `x + y = z` for some enumeration. -/
def schurEdges (A : Finset ℤ) : Finset (Finset ℤ) :=
  A.powerset.filter fun e =>
    e.card = 3 ∧ ∃ x ∈ e, ∃ y ∈ e, x ≠ y ∧ x + y ∈ e

theorem mem_schurEdges {A e : Finset ℤ} :
    e ∈ schurEdges A ↔ e ⊆ A ∧ e.card = 3 ∧
      ∃ x ∈ e, ∃ y ∈ e, x ≠ y ∧ x + y ∈ e := by
  rw [schurEdges, Finset.mem_filter, Finset.mem_powerset]

theorem schurEdges_subset {A : Finset ℤ} {e : Finset ℤ}
    (he : e ∈ schurEdges A) : e ⊆ A :=
  (Finset.mem_powerset.mp (Finset.mem_filter.mp he).1)

theorem schurEdge_card {A : Finset ℤ} {e : Finset ℤ}
    (he : e ∈ schurEdges A) : e.card = 3 :=
  (mem_schurEdges.mp he).2.1

/-- The number of Schur edges inside `A`. -/
def schurEdgeCount (A : Finset ℤ) : ℕ := (schurEdges A).card

/-- Every strict Schur edge inside `A` is a Schur triple of `A`. -/
theorem schurEdge_mem_schurTriples {A : Finset ℤ} {e : Finset ℤ}
    (he : e ∈ schurEdges A) :
    ∃ x ∈ A, ∃ y ∈ A, x + y ∈ A ∧ ({x, y, x + y} : Finset ℤ) ⊆ e := by
  obtain ⟨_, _, x, hx, y, hy, _, hxy⟩ := mem_schurEdges.mp he
  exact ⟨x, schurEdges_subset he hx, y, schurEdges_subset he hy,
    schurEdges_subset he hxy, by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl <;> assumption⟩

/-- A sum-free set contains no strict Schur edge. -/
theorem no_schurEdge_of_isSumFree {I : Finset ℤ} (hI : IsSumFree I) :
    ∀ e ∈ schurEdges I, False := by
  intro e he
  obtain ⟨_, _, x, hx, y, hy, _, hxy⟩ := mem_schurEdges.mp he
  exact hI x (schurEdges_subset he hx) y (schurEdges_subset he hy)
    (schurEdges_subset he hxy)

/-- Vertex degree in the hypergraph `schurEdges A`. -/
def edgeDeg (A : Finset ℤ) (v : ℤ) : ℕ :=
  ((schurEdges A).filter (v ∈ ·)).card

/-- Handshaking: `∑_{v ∈ A} d(v) = 3 e(A)`. -/
theorem sum_edgeDeg (A : Finset ℤ) :
    ∑ v ∈ A, edgeDeg A v = 3 * schurEdgeCount A := by
  classical
  have step : ∀ v : ℤ, ((schurEdges A).filter (v ∈ ·)).card =
      ∑ e ∈ schurEdges A, (if v ∈ e then (1 : ℕ) else 0) :=
    fun v => (Finset.sum_boole (v ∈ ·) (schurEdges A)).symm
  unfold edgeDeg schurEdgeCount
  rw [Finset.sum_congr rfl fun v _ => step v, Finset.sum_comm]
  rw [show (3 : ℕ) * (schurEdges A).card = ∑ e ∈ schurEdges A, 3 by
    rw [Finset.sum_const, nsmul_eq_mul, Nat.cast_id, mul_comm]]
  apply Finset.sum_congr rfl
  intro e he
  have hfilter : A.filter (· ∈ e) = e := by
    rw [Finset.filter_mem_eq_inter, Finset.inter_eq_right]
    exact schurEdges_subset he
  rw [Finset.sum_boole, hfilter, schurEdge_card he, Nat.cast_id]

/-- Co-degree bound: a pair `{v,w}`, `v ≠ w`, of positive integers lies in at
most three strict Schur edges: the third vertex is one of
`v + w`, `w − v`, `v − w`. -/
theorem schurEdges_pair_le_three {A : Finset ℤ} {v w : ℤ} (hvw : v ≠ w)
    (hA : ∀ x ∈ A, 0 < x) :
    ((schurEdges A).filter ({v, w} ⊆ ·)).card ≤ 3 := by
  classical
  have hsub : (schurEdges A).filter ({v, w} ⊆ ·) ⊆
      ({ {v, w, v + w}, {v, w, w - v}, {v, w, v - w} } :
        Finset (Finset ℤ)) := by
    intro e he
    rw [Finset.mem_filter] at he
    obtain ⟨heA, hpair⟩ := he
    obtain ⟨hesub, hcard, x, hx, y, hy, hxy, hsum⟩ := mem_schurEdges.mp heA
    -- `e` has exactly one element `z` outside `{v,w}`.
    have hcard2 : ({v, w} : Finset ℤ).card = 2 :=
      Finset.card_pair_eq_two_iff.mpr hvw
    have hdiff : (e \ {v, w}).card = 1 := by
      rw [Finset.card_sdiff_of_subset hpair, hcard, hcard2]
    obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hdiff
    have h1 : e \ {v, w} ∪ {v, w} = e := Finset.sdiff_union_of_subset hpair
    rw [hz] at h1
    have he_eq : e = {v, w, z} := by
      rw [← h1]
      ext t
      simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_insert]
      tauto
    have hpos : ∀ t ∈ e, 0 < t := fun t ht => hA t (hesub ht)
    have hve : v ∈ e := hpair (Finset.mem_insert_self _ _)
    have hwe : w ∈ e := hpair
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    have hze : z ∈ e := by rw [he_eq]; simp
    have hv := hpos v hve
    have hw' := hpos w hwe
    have hz' := hpos z hze
    rw [he_eq] at hx hy hsum
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy hsum
    have hzval : z = v + w ∨ z = w - v ∨ z = v - w := by
      rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
      · exact absurd rfl hxy
      · left; rcases hsum with h | h | h <;> omega
      · right; left; rcases hsum with h | h | h <;> omega
      · left; rcases hsum with h | h | h <;> omega
      · exact absurd rfl hxy
      · right; right; rcases hsum with h | h | h <;> omega
      · right; left; rcases hsum with h | h | h <;> omega
      · right; right; rcases hsum with h | h | h <;> omega
      · exact absurd rfl hxy
    rcases hzval with rfl | rfl | rfl
    · rw [he_eq]; exact Finset.mem_insert_self _ _
    · rw [he_eq]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    · rw [he_eq]; exact Finset.mem_insert_of_mem
        (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  calc ((schurEdges A).filter ({v, w} ⊆ ·)).card
      ≤ ({ {v, w, v + w}, {v, w, w - v}, {v, w, v - w} } :
          Finset (Finset ℤ)).card :=
        Finset.card_le_card hsub
    _ ≤ 3 := Finset.card_le_three

/-- Degree-sum of `S` against the ambient hypergraph `A₀`. -/
def degSum (A₀ S : Finset ℤ) : ℕ := ∑ v ∈ S, edgeDeg A₀ v

/-- `E_j(A)`: edges inside `A` meeting `I` in at least `j` vertices. -/
def EjSet (I A : Finset ℤ) (j : ℕ) : Finset (Finset ℤ) :=
  (schurEdges A).filter fun e => j ≤ (e ∩ I).card

theorem EjSet_subset_edges (I A : Finset ℤ) (j : ℕ) :
    EjSet I A j ⊆ schurEdges A :=
  Finset.filter_subset _ _

theorem EjSet_zero_eq (I A : Finset ℤ) : EjSet I A 0 = schurEdges A := by
  unfold EjSet
  rw [Finset.filter_true_of_mem]
  intro e _
  exact Nat.zero_le _

/-- Degree-sum over a disjoint union splits. -/
theorem degSum_union {A₀ s t : Finset ℤ} (h : Disjoint s t) :
    degSum A₀ (s ∪ t) = degSum A₀ s + degSum A₀ t := by
  unfold degSum
  rw [Finset.sum_union h]

/-- Edges inside `S ⊆ A₀` are counted at most `3` times by the degree-sum. -/
theorem schurEdgeCount_le_degSum {A₀ S : Finset ℤ} (hS : S ⊆ A₀) :
    3 * schurEdgeCount S ≤ degSum A₀ S := by
  classical
  have step : ∀ v : ℤ, ((schurEdges S).filter (v ∈ ·)).card =
      ∑ e ∈ schurEdges S, (if v ∈ e then (1 : ℕ) else 0) :=
    fun v => (Finset.sum_boole (v ∈ ·) (schurEdges S)).symm
  have hsub : schurEdges S ⊆ schurEdges A₀ := by
    intro e he
    rw [mem_schurEdges] at he ⊢
    exact ⟨Finset.Subset.trans he.1 hS, he.2⟩
  calc 3 * schurEdgeCount S
      = ∑ v ∈ S, ((schurEdges S).filter (v ∈ ·)).card := by
        have := sum_edgeDeg S
        unfold edgeDeg at this
        unfold schurEdgeCount
        exact this.symm
    _ ≤ ∑ v ∈ S, ((schurEdges A₀).filter (v ∈ ·)).card := by
        apply Finset.sum_le_sum
        intro v _
        exact Finset.card_le_card (Finset.filter_subset_filter _ hsub)
    _ = degSum A₀ S := rfl

/-- Complementary degree-sum: `degSum(S) + degSum(A₀∖S) = 3e(A₀)` for
`S ⊆ A₀`. -/
theorem degSum_add_compl {A₀ S : Finset ℤ} (hS : S ⊆ A₀) :
    degSum A₀ S + degSum A₀ (A₀ \ S) = 3 * schurEdgeCount A₀ := by
  unfold degSum
  rw [← Finset.sum_union (Finset.disjoint_sdiff)]
  rw [Finset.union_sdiff_of_subset hS]
  exact sum_edgeDeg A₀

/-- Each edge inside `A` contributes `|e ∩ A|` to `degSum_{A₀}(A)`. -/
theorem degSum_eq_sum_inter {A₀ A : Finset ℤ} :
    (degSum A₀ A : ℝ) =
      ∑ e ∈ schurEdges A₀, ((e ∩ A).card : ℝ) := by
  classical
  unfold degSum edgeDeg
  push_cast
  simp only [← Finset.sum_boole]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  rw [Finset.sum_boole]
  congr 1
  rw [Finset.filter_mem_eq_inter, Finset.inter_comm]

/-- **Degree measure lower bound** (equation (2) of Saxton–Thomason):
`e(G[A]) ≥ degSum_{A₀}(A) − 2e(A₀)` for `A ⊆ A₀`. -/
theorem schurEdgeCount_lower {A₀ A : Finset ℤ} (hA : A ⊆ A₀) :
    (degSum A₀ A : ℝ) - 2 * schurEdgeCount A₀ ≤ schurEdgeCount A := by
  classical
  have key : ∀ e ∈ schurEdges A₀,
      ((e ∩ A).card : ℝ) ≤
        (if e ⊆ A then (3 : ℝ) else 0) +
          2 * ((e ∩ (A₀ \ A)).card : ℝ) := by
    intro e he
    by_cases heA : e ⊆ A
    · rw [if_pos heA]
      have h1 : e ∩ A = e := Finset.inter_eq_left.mpr heA
      rw [h1, schurEdge_card he, show ((3 : ℕ) : ℝ) = 3 by norm_num]
      have : (0 : ℝ) ≤ 2 * ((e ∩ (A₀ \ A)).card : ℝ) := by positivity
      linarith
    · rw [if_neg heA, zero_add]
      have hsplit : e = (e ∩ A) ∪ (e ∩ (A₀ \ A)) := by
        rw [← Finset.inter_union_distrib_left,
          Finset.union_sdiff_of_subset hA]
        exact (Finset.inter_eq_left.mpr (schurEdges_subset he)).symm
      have hdisj : Disjoint (e ∩ A) (e ∩ (A₀ \ A)) :=
        Finset.disjoint_left.mpr fun x hx hx' =>
          (Finset.mem_sdiff.mp (Finset.mem_inter.mp hx').2).2
            (Finset.mem_inter.mp hx).2
      have hcard : (e ∩ A).card + (e ∩ (A₀ \ A)).card = 3 := by
        have hc := schurEdge_card he
        conv_rhs => rw [← hc, hsplit]
        exact (Finset.card_union_of_disjoint hdisj).symm
      have hpos : 0 < (e ∩ (A₀ \ A)).card := by
        rw [Finset.card_pos, Finset.nonempty_iff_ne_empty]
        intro hcon
        apply heA
        intro x hx
        by_contra hxA
        have hx' : x ∈ e ∩ (A₀ \ A) :=
          Finset.mem_inter.mpr ⟨hx, Finset.mem_sdiff.mpr
            ⟨schurEdges_subset he hx, hxA⟩⟩
        rw [hcon] at hx'
        exact Finset.notMem_empty _ hx'
      have h1 : (e ∩ A).card ≤ 2 := by omega
      exact_mod_cast (by omega : (e ∩ A).card ≤ 2 * (e ∩ (A₀ \ A)).card)
  have hsum : (degSum A₀ A : ℝ) ≤
      3 * schurEdgeCount A + 2 * degSum A₀ (A₀ \ A) := by
    rw [degSum_eq_sum_inter]
    push_cast
    calc (∑ e ∈ schurEdges A₀, ((e ∩ A).card : ℝ))
        ≤ ∑ e ∈ schurEdges A₀,
            ((if e ⊆ A then (3 : ℝ) else 0) +
              2 * ((e ∩ (A₀ \ A)).card : ℝ)) :=
          Finset.sum_le_sum key
      _ = (∑ e ∈ schurEdges A₀, (if e ⊆ A then (3 : ℝ) else 0)) +
            2 * (∑ e ∈ schurEdges A₀, ((e ∩ (A₀ \ A)).card : ℝ)) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      _ = 3 * schurEdgeCount A + 2 * degSum A₀ (A₀ \ A) := by
          congr 1
          · have hfilter : schurEdges A =
                (schurEdges A₀).filter (· ⊆ A) := by
              ext e
              simp only [mem_schurEdges, Finset.mem_filter]
              constructor
              · rintro ⟨hesub, hcard, x, hx, y, hy, hxy, hsum⟩
                exact ⟨⟨Finset.Subset.trans hesub hA, hcard, x, hx, y, hy,
                  hxy, hsum⟩, hesub⟩
              · rintro ⟨⟨-, hcard, x, hx, y, hy, hxy, hsum⟩, hesub⟩
                exact ⟨hesub, hcard, x, hx, y, hy, hxy, hsum⟩
            rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul,
              mul_comm, ← hfilter]
            rfl
          · rw [degSum_eq_sum_inter]
  have hcompl := degSum_add_compl hA
  have h7 : (degSum A₀ A : ℝ) + degSum A₀ (A₀ \ A) =
      3 * schurEdgeCount A₀ := by exact_mod_cast hcompl
  linarith [hsum]

/-- Degree measure of `S` with respect to ambient `A₀`:
`μ(S) = degSum(S) / 3e(A₀)`. -/
noncomputable def degMeasure (A₀ S : Finset ℤ) : ℝ :=
  (degSum A₀ S : ℝ) / (3 * schurEdgeCount A₀)

theorem degMeasure_le_one {A₀ S : Finset ℤ} (hS : S ⊆ A₀)
    (he0 : 0 < schurEdgeCount A₀) :
    degMeasure A₀ S ≤ 1 := by
  unfold degMeasure
  have hden : (0 : ℝ) < 3 * schurEdgeCount A₀ := by
    have : (0 : ℝ) < schurEdgeCount A₀ := by exact_mod_cast he0
    linarith
  rw [div_le_one hden]
  have := degSum_add_compl hS
  have h1 : (degSum A₀ S : ℝ) + degSum A₀ (A₀ \ S) =
      3 * schurEdgeCount A₀ := by exact_mod_cast this
  have h2 : (0 : ℝ) ≤ degSum A₀ (A₀ \ S) := by positivity
  linarith

theorem degMeasure_A₀ {A₀ : Finset ℤ} (he0 : 0 < schurEdgeCount A₀) :
    degMeasure A₀ A₀ = 1 := by
  unfold degMeasure
  have hden : (0 : ℝ) < 3 * schurEdgeCount A₀ := by
    have : (0 : ℝ) < schurEdgeCount A₀ := by exact_mod_cast he0
    linarith
  rw [div_eq_one_iff_eq hden.ne']
  have := sum_edgeDeg A₀
  unfold degSum
  exact_mod_cast this

theorem degMeasure_union {A₀ S T : Finset ℤ} (hdisj : Disjoint S T) :
    degMeasure A₀ (S ∪ T) = degMeasure A₀ S + degMeasure A₀ T := by
  unfold degMeasure
  rw [degSum_union hdisj]
  push_cast
  rw [add_div]

/-- The `F_j(v)` family: edges of `A` containing `v` and meeting `I` in
exactly `j` vertices. -/
def FjFamily (I A : Finset ℤ) (j : ℕ) (v : ℤ) : Finset (Finset ℤ) :=
  (schurEdges A).filter fun e => v ∈ e ∧ (e ∩ I).card = j

/-- ST density threshold `τ = e(A₀)·u^j·(1-u)/(2·|A₀|)`. -/
noncomputable def stThresh (A₀ : Finset ℤ) (u : ℝ) (j : ℕ) : ℝ :=
  schurEdgeCount A₀ * u ^ j * (1 - u) / (2 * A₀.card)

/-- The high-`F_j`-degree vertices of `A ∖ I`. -/
noncomputable def stD (I A₀ A : Finset ℤ) (u : ℝ) (j : ℕ) : Finset ℤ :=
  (A \ I).filter fun v =>
    stThresh A₀ u j ≤ ((FjFamily I A j v).card : ℝ)

theorem stD_subset (I A₀ A : Finset ℤ) (u : ℝ) (j : ℕ) :
    stD I A₀ A u j ⊆ A \ I :=
  Finset.filter_subset _ _

theorem stD_disj_I (I A₀ A : Finset ℤ) (u : ℝ) (j : ℕ) :
    Disjoint (stD I A₀ A u j) I :=
  Finset.disjoint_left.mpr fun x hx =>
    (Finset.mem_sdiff.mp (stD_subset I A₀ A u j hx)).2

/-- Every edge of `E_j(A∖D)` lies in `E_{j+1}(A)` or in some `F_j(v)`
with `v ∈ (A∖I)∖D`. -/
theorem EjSet_sdiff_stD_subset {I A₀ A : Finset ℤ} (u : ℝ) (j : ℕ)
    (hj : j < 3) :
    EjSet I (A \ stD I A₀ A u j) j ⊆
      EjSet I A (j + 1) ∪
        ((A \ I) \ stD I A₀ A u j).biUnion (FjFamily I A j) := by
  intro e he
  have heE : e ∈ schurEdges (A \ stD I A₀ A u j) :=
    (Finset.mem_filter.mp he).1
  have hcard : j ≤ (e ∩ I).card := (Finset.mem_filter.mp he).2
  obtain ⟨hesub, hce, x, hx, y, hy, hxy, hsum⟩ := mem_schurEdges.mp heE
  have hesubA : e ⊆ A :=
    Finset.Subset.trans hesub Finset.sdiff_subset
  have heEA : e ∈ schurEdges A :=
    mem_schurEdges.mpr ⟨hesubA, hce, x, hx, y, hy, hxy, hsum⟩
  by_cases h3 : (e ∩ I).card = j
  · rw [Finset.mem_union]
    right
    have hex : ∃ v ∈ e, v ∉ I := by
      by_contra hcon
      push_neg at hcon
      have heI : e ⊆ I := hcon
      have : (e ∩ I).card = 3 := by
        rw [Finset.inter_eq_left.mpr heI, hce]
      omega
    obtain ⟨v, hve, hvI⟩ := hex
    rw [Finset.mem_biUnion]
    refine ⟨v, ?_, ?_⟩
    · rw [Finset.mem_sdiff]
      exact ⟨Finset.mem_sdiff.mpr ⟨hesubA hve, hvI⟩,
        (Finset.mem_sdiff.mp (schurEdges_subset heE hve)).2⟩
    · rw [FjFamily, Finset.mem_filter]
      exact ⟨heEA, hve, h3⟩
  · rw [Finset.mem_union]
    left
    unfold EjSet
    rw [Finset.mem_filter]
    exact ⟨heEA, by omega⟩

/-- Cardinality bound: `|E_j(A∖D)| ≤ |E_{j+1}(A)| + |(A∖I)∖D|·τ`. -/
theorem EjSet_stD_bound {I A₀ A : Finset ℤ} (u : ℝ) {j : ℕ}
    (hj : j < 3) :
    ((EjSet I (A \ stD I A₀ A u j) j).card : ℝ) ≤
      ((EjSet I A (j + 1)).card : ℝ) +
        (((A \ I) \ stD I A₀ A u j).card : ℝ) * stThresh A₀ u j := by
  classical
  have h1 := Finset.card_le_card
    (EjSet_sdiff_stD_subset (I := I) (A₀ := A₀) (A := A) u j hj)
  have h2 : ((EjSet I A (j + 1) ∪
        ((A \ I) \ stD I A₀ A u j).biUnion (FjFamily I A j)).card : ℝ) ≤
      (EjSet I A (j + 1)).card +
        (((A \ I) \ stD I A₀ A u j).biUnion (FjFamily I A j)).card := by
    exact_mod_cast Finset.card_union_le _ _
  have h3 : ((((A \ I) \ stD I A₀ A u j).biUnion
        (FjFamily I A j)).card : ℝ) ≤
      ∑ v ∈ (A \ I) \ stD I A₀ A u j,
        ((FjFamily I A j v).card : ℝ) := by
    exact_mod_cast Finset.card_biUnion_le
  have h4 : ∑ v ∈ (A \ I) \ stD I A₀ A u j,
        ((FjFamily I A j v).card : ℝ) ≤
      ((A \ I) \ stD I A₀ A u j).card * stThresh A₀ u j := by
    calc ∑ v ∈ (A \ I) \ stD I A₀ A u j,
          ((FjFamily I A j v).card : ℝ)
        ≤ ∑ v ∈ (A \ I) \ stD I A₀ A u j, stThresh A₀ u j := by
          apply Finset.sum_le_sum
          intro v hv
          have hvD : v ∉ stD I A₀ A u j := (Finset.mem_sdiff.mp hv).2
          have hvAI : v ∈ A \ I := (Finset.mem_sdiff.mp hv).1
          unfold stD at hvD
          rw [Finset.mem_filter] at hvD
          push_neg at hvD
          exact le_of_lt (hvD hvAI)
      _ = ((A \ I) \ stD I A₀ A u j).card * stThresh A₀ u j := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have h1r : ((EjSet I (A \ stD I A₀ A u j) j).card : ℝ) ≤
      ((EjSet I A (j + 1) ∪
        ((A \ I) \ stD I A₀ A u j).biUnion (FjFamily I A j)).card : ℝ) := by
    exact_mod_cast h1
  linarith [h1r, h2, h3, h4]

/-- `τ ≥ 0` when `0 ≤ u ≤ 1`. -/
theorem stThresh_nonneg (A₀ : Finset ℤ) (u : ℝ) (j : ℕ)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    0 ≤ stThresh A₀ u j := by
  unfold stThresh
  apply div_nonneg
  · exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _)
      (pow_nonneg hu0 _)) (by linarith)
  · positivity

/-- **ST measure amplification.** If `P(j)` holds and `A` satisfies the
level `j+1` conditions, the high-`F_j`-degree set `D` has degree measure
exceeding `1/18`. -/
theorem stD_measure {I A₀ A : Finset ℤ} (hA : A ⊆ A₀) (hIA : I ⊆ A)
    (u : ℝ) (hu0 : 0 < u) (hu1 : u < 1) {j : ℕ} (hj : j < 3)
    (he0 : 0 < schurEdgeCount A₀) (hA0 : 0 < A₀.card)
    (hμA : 1 - 1/6 + ((j:ℝ) + 1)/18 ≤ degMeasure A₀ A)
    (hEj : ((EjSet I A (j+1)).card : ℝ) <
      schurEdgeCount A₀ * u^(j+1)/2)
    (hPj : ∀ B : Finset ℤ, B ⊆ A₀ → I ⊆ B →
      1 - 1/6 + (j:ℝ)/18 ≤ degMeasure A₀ B →
      schurEdgeCount A₀ * u^j/2 ≤ ((EjSet I B j).card : ℝ)) :
    1/18 < degMeasure A₀ (stD I A₀ A u j) := by
  classical
  have hDA : stD I A₀ A u j ⊆ A :=
    Finset.Subset.trans (stD_subset I A₀ A u j) Finset.sdiff_subset
  have hIAD : I ⊆ A \ stD I A₀ A u j := by
    intro x hx
    rw [Finset.mem_sdiff]
    exact ⟨hIA hx, fun hxD =>
      (Finset.mem_sdiff.mp (stD_subset I A₀ A u j hxD)).2 hx⟩
  have hAD0 : A \ stD I A₀ A u j ⊆ A₀ :=
    Finset.Subset.trans Finset.sdiff_subset hA
  have hcard : (((A \ I) \ stD I A₀ A u j).card : ℝ) ≤ A₀.card := by
    exact_mod_cast Finset.card_le_card
      (Finset.Subset.trans Finset.sdiff_subset
        (Finset.Subset.trans Finset.sdiff_subset hA))
  have hτ : (A₀.card : ℝ) * stThresh A₀ u j =
      schurEdgeCount A₀ * u^j * (1-u)/2 := by
    unfold stThresh
    rw [mul_div_assoc', mul_comm (A₀.card : ℝ),
      mul_div_mul_right _ _ (Nat.cast_ne_zero.mpr (ne_of_gt hA0))]
  have hbound : ((EjSet I (A \ stD I A₀ A u j) j).card : ℝ) <
      schurEdgeCount A₀ * u^j / 2 := by
    have hb := EjSet_stD_bound (I := I) (A₀ := A₀) (A := A) u hj
    have hτnn := stThresh_nonneg A₀ u j hu0.le hu1.le
    calc ((EjSet I (A \ stD I A₀ A u j) j).card : ℝ)
        ≤ ((EjSet I A (j+1)).card:ℝ) +
            (((A\I) \ stD I A₀ A u j).card:ℝ) * stThresh A₀ u j := hb
      _ < schurEdgeCount A₀ * u^(j+1)/2 +
            schurEdgeCount A₀ * u^j * (1-u)/2 := by
          apply add_lt_add_of_lt_of_le hEj
          calc (((A\I) \ stD I A₀ A u j).card:ℝ) * stThresh A₀ u j
              ≤ A₀.card * stThresh A₀ u j :=
                mul_le_mul_of_nonneg_right hcard hτnn
            _ = schurEdgeCount A₀ * u^j * (1-u)/2 := hτ
      _ = schurEdgeCount A₀ * u^j/2 := by
          rw [pow_succ]
          ring
  by_cases hμ : 1 - 1/6 + (j:ℝ)/18 ≤
      degMeasure A₀ (A \ stD I A₀ A u j)
  · have hge := hPj (A \ stD I A₀ A u j) hAD0 hIAD hμ
    linarith [hge, hbound]
  · push_neg at hμ
    have hsplit : degMeasure A₀ A =
        degMeasure A₀ (A \ stD I A₀ A u j) +
          degMeasure A₀ (stD I A₀ A u j) := by
      have hdisj : Disjoint (A \ stD I A₀ A u j) (stD I A₀ A u j) :=
        Finset.disjoint_left.mpr fun x hx hx' =>
          (Finset.mem_sdiff.mp hx).2 hx'
      rw [← degMeasure_union hdisj, Finset.sdiff_union_of_subset hDA]
    rw [hsplit] at hμA
    linarith [hμA, hμ]

/-- The `P(j)` predicate of Saxton–Thomason: every high-measure
`B ⊇ I` contains at least `e(A₀)·u^j/2` edges meeting `I` in `≥ j`
vertices. -/
def stP (I A₀ : Finset ℤ) (u : ℝ) (j : ℕ) : Prop :=
  ∀ B : Finset ℤ, B ⊆ A₀ → I ⊆ B →
    1 - 1/6 + (j:ℝ)/18 ≤ degMeasure A₀ B →
    schurEdgeCount A₀ * u^j/2 ≤ ((EjSet I B j).card : ℝ)

/-- `P(0)` holds: `E_0(B)` is all of `schurEdges B` and the measure
bound gives `e(B) ≥ e(A₀)/2`. -/
theorem stP_zero (I A₀ : Finset ℤ) (u : ℝ)
    (he0 : 0 < schurEdgeCount A₀) :
    stP I A₀ u 0 := by
  intro B hB _ hμ
  have hden : (0:ℝ) < 3 * schurEdgeCount A₀ := by
    have : (0:ℝ) < schurEdgeCount A₀ := by exact_mod_cast he0
    linarith
  rw [EjSet_zero_eq, pow_zero, mul_one]
  show (schurEdgeCount A₀ : ℝ) / 2 ≤ (schurEdgeCount B : ℝ)
  have hμ' : (5/6) * (3 * schurEdgeCount A₀) ≤ (degSum A₀ B : ℝ) := by
    rw [degMeasure, le_div_iff₀ hden] at hμ
    push_cast at hμ
    linarith [hμ]
  have h1 := schurEdgeCount_lower hB
  linarith [hμ', h1]

/-- `P(3)` fails: no edge can meet the sum-free `I` in three vertices. -/
theorem not_stP_three {I A₀ : Finset ℤ} (hI : I ⊆ A₀)
    (hIsf : IsSumFree I) (u : ℝ) (hu : 0 < u)
    (he0 : 0 < schurEdgeCount A₀) :
    ¬ stP I A₀ u 3 := by
  intro hP
  have hE3 : EjSet I A₀ 3 = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro e he
    have hcard : 3 ≤ (e ∩ I).card := (Finset.mem_filter.mp he).2
    have heE : e ∈ schurEdges A₀ := (Finset.mem_filter.mp he).1
    have hce := schurEdge_card heE
    have heI : e ∩ I = e :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_left
        (by omega)
    have heIsub : e ⊆ I := Finset.inter_eq_left.mp heI
    obtain ⟨_, hce2, x, hx, y, hy, hxy, hsum⟩ := mem_schurEdges.mp heE
    have : e ∈ schurEdges I :=
      mem_schurEdges.mpr ⟨heIsub, hce2, x, hx, y, hy, hxy, hsum⟩
    exact no_schurEdge_of_isSumFree hIsf e this
  have hμ : 1 - 1/6 + (3:ℝ)/18 ≤ degMeasure A₀ A₀ := by
    rw [degMeasure_A₀ he0]
    norm_num
  have hge := hP A₀ (Finset.Subset.refl _) hI hμ
  rw [hE3, Finset.card_empty] at hge
  push_cast at hge
  have hpos : (0:ℝ) < schurEdgeCount A₀ * u^3 / 2 := by
    apply div_pos
    · exact mul_pos (by exact_mod_cast he0) (pow_pos hu 3)
    · norm_num
  linarith [hge]

/-- **Level selection.** There exists `j ∈ {0,1,2}` and `A` satisfying
the level `j+1` conditions while `P(j)` still holds. -/
theorem st_level_exists {I A₀ : Finset ℤ} (hI : I ⊆ A₀)
    (hIsf : IsSumFree I) (u : ℝ) (hu : 0 < u)
    (he0 : 0 < schurEdgeCount A₀) :
    ∃ j : ℕ, j ≤ 2 ∧ ∃ A : Finset ℤ, A ⊆ A₀ ∧ I ⊆ A ∧
      1 - 1/6 + ((j:ℝ)+1)/18 ≤ degMeasure A₀ A ∧
      ((EjSet I A (j+1)).card : ℝ) <
        schurEdgeCount A₀ * u^(j+1)/2 ∧
      stP I A₀ u j := by
  classical
  have hne : ∃ j : ℕ, ¬ stP I A₀ u j :=
    ⟨3, not_stP_three hI hIsf u hu he0⟩
  set m := Nat.find hne with hm
  have hm3 : m ≤ 3 :=
    Nat.find_le (not_stP_three hI hIsf u hu he0)
  have hspec : ¬ stP I A₀ u m := Nat.find_spec hne
  have hmpos : 0 < m := by
    by_contra h
    have hm0 : m = 0 := Nat.eq_zero_of_le_zero (le_of_not_gt h)
    rw [hm0] at hspec
    exact hspec (stP_zero I A₀ u he0)
  have hP : stP I A₀ u (m - 1) :=
    of_not_not (Nat.find_min hne (Nat.sub_lt hmpos zero_lt_one))
  unfold stP at hspec
  push_neg at hspec
  obtain ⟨A, hA0, hIA, hμ, hEj⟩ := hspec
  have hcast : ((m - 1 : ℕ) : ℝ) + 1 = m := by
    exact_mod_cast Nat.sub_add_cancel hmpos
  refine ⟨m - 1, by omega, A, hA0, hIA, ?_, ?_, hP⟩
  · rw [hcast]
    exact hμ
  · have : m - 1 + 1 = m := Nat.sub_add_cancel hmpos
    rw [this]
    exact hEj

/-- `E^{=}_k(A)`: edges inside `A` meeting `I` in exactly `k` vertices. -/
def EjEq (I A : Finset ℤ) (k : ℕ) : Finset (Finset ℤ) :=
  (schurEdges A).filter fun e => (e ∩ I).card = k

/-- `Γ_j(R,S)`: vertices `v` of the ambient `A₀` such that some ambient
edge decomposes as `{v} ∪ f ∪ g` with `f ∈ R^{(j)}`, `g ∈ S^{(2-j)}`,
`v ∉ f ∪ g`. -/
noncomputable def stGamma (A₀ : Finset ℤ) (j : ℕ) (R S : Finset ℤ) :
    Finset ℤ := by
  classical
  exact A₀.filter fun v =>
    ∃ e ∈ schurEdges A₀, ∃ f g : Finset ℤ,
      e = insert v (f ∪ g) ∧ v ∉ f ∪ g ∧ f ⊆ R ∧ f.card = j ∧
        g ⊆ S ∧ g.card = 2 - j

theorem stGamma_subset (A₀ : Finset ℤ) (j : ℕ) (R S : Finset ℤ) :
    stGamma A₀ j R S ⊆ A₀ := by
  classical
  unfold stGamma
  exact Finset.filter_subset _ _

theorem mem_stGamma {A₀ : Finset ℤ} {j : ℕ} {R S : Finset ℤ} {v : ℤ} :
    v ∈ stGamma A₀ j R S ↔ v ∈ A₀ ∧ ∃ e ∈ schurEdges A₀,
      ∃ f g : Finset ℤ,
        e = insert v (f ∪ g) ∧ v ∉ f ∪ g ∧ f ⊆ R ∧ f.card = j ∧
          g ⊆ S ∧ g.card = 2 - j := by
  classical
  unfold stGamma
  exact Finset.mem_filter

/-- Vertices of `Γ_j(W∩I, W∩(A∖I))` lying in `I` are covered by edges of
`E^{=}_{j+1}(A)` whose `e ∖ {v}` lands inside `W`. -/
theorem stGamma_inter_subset {I A₀ A W : Finset ℤ} (j : ℕ)
    (hA : A ⊆ A₀) (hIA : I ⊆ A) (hW : W ⊆ A₀) :
    stGamma A₀ j (W ∩ I) (W ∩ (A \ I)) ∩ I ⊆
      (EjEq I A (j + 1)).biUnion fun e =>
        (e ∩ I).filter fun v => e \ {v} ⊆ W := by
  intro v hv
  obtain ⟨hvΓ, hvI⟩ := Finset.mem_inter.mp hv
  obtain ⟨hvA₀, e, heE, f, g, heq, hvfg, hfR, hfj, hgS, hgj⟩ :=
    mem_stGamma.mp hvΓ
  -- `f ⊆ I`, `g ⊆ A ∖ I`, `v ∈ I` give `e ∩ I = {v} ∪ f`.
  have hfI : f ⊆ I := Finset.Subset.trans hfR Finset.inter_subset_right
  have hgAI : g ⊆ A \ I :=
    Finset.Subset.trans hgS Finset.inter_subset_right
  have hgI : Disjoint g I :=
    Finset.disjoint_left.mpr fun x hx hxI =>
      (Finset.mem_sdiff.mp (hgAI hx)).2 hxI
  have hvf : v ∉ f := fun h => hvfg (Finset.mem_union_left _ h)
  have hvg : v ∉ g := fun h => hvfg (Finset.mem_union_right _ h)
  have heiI : e ∩ I = insert v f := by
    ext x
    rw [heq]
    simp only [Finset.mem_inter, Finset.mem_union, Finset.insert_eq,
      Finset.mem_singleton, Finset.mem_insert]
    constructor
    · rintro ⟨(rfl | hxf | hxg), hxI⟩
      · exact Or.inl rfl
      · exact Or.inr hxf
      · exact absurd hxI (Finset.disjoint_left.mp hgI hxg)
    · rintro (rfl | hxf)
      · exact ⟨Or.inl rfl, hvI⟩
      · exact ⟨Or.inr (Or.inl hxf), hfI hxf⟩
  have hesubA : e ⊆ A := by
    rw [heq]
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hxfg
    · exact hIA hvI
    · rcases Finset.mem_union.mp hxfg with hxf | hxg
      · exact hIA (hfI hxf)
      · exact Finset.mem_sdiff.mp (hgAI hxg) |>.1
  have heEA : e ∈ schurEdges A := by
    obtain ⟨_, hce, x, hx, y, hy, hxy, hsum⟩ := mem_schurEdges.mp heE
    exact mem_schurEdges.mpr ⟨hesubA, hce, x, hx, y, hy, hxy, hsum⟩
  rw [Finset.mem_biUnion]
  refine ⟨e, ?_, ?_⟩
  · rw [EjEq, Finset.mem_filter]
    refine ⟨heEA, ?_⟩
    rw [heiI, Finset.card_insert_of_notMem hvf, hfj]
  · rw [Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · rw [heiI]
      exact Finset.mem_insert_self _ _
    · -- `e \ {v} = f ∪ g ⊆ W`
      have h1 : e \ {v} = f ∪ g := by
        rw [heq, Finset.sdiff_singleton_eq_erase,
          Finset.erase_insert hvfg]
      rw [h1]
      intro x hx
      rcases Finset.mem_union.mp hx with hxf | hxg
      · exact Finset.mem_inter.mp (hfR hxf) |>.1
      · exact Finset.mem_inter.mp (hgS hxg) |>.1

/-- The pair family `P_v`: sets `e ∖ {v}` for `e ∈ F_j(v)`. -/
noncomputable def stPairs (I A : Finset ℤ) (j : ℕ) (v : ℤ) :
    Finset (Finset ℤ) :=
  (FjFamily I A j v).image (· \ {v})

theorem stPairs_card_le (I A : Finset ℤ) (j : ℕ) (v : ℤ) :
    (stPairs I A j v).card ≤ (FjFamily I A j v).card :=
  Finset.card_image_le

theorem mem_stPairs {I A : Finset ℤ} {j : ℕ} {v : ℤ} {pair : Finset ℤ} :
    pair ∈ stPairs I A j v ↔
      ∃ e ∈ FjFamily I A j v, e \ {v} = pair :=
  Finset.mem_image

theorem stPairs_mem_card {I A : Finset ℤ} {j : ℕ} {v : ℤ}
    {pair : Finset ℤ} (hp : pair ∈ stPairs I A j v) : pair.card = 2 := by
  obtain ⟨e, he, rfl⟩ := mem_stPairs.mp hp
  have hv : v ∈ e := (Finset.mem_filter.mp he).2.1
  have hce := schurEdge_card (Finset.mem_filter.mp he).1
  rw [Finset.sdiff_singleton_eq_erase,
    Finset.card_erase_of_mem hv, hce]

theorem stPairs_mem_subset {I A : Finset ℤ} {j : ℕ} {v : ℤ}
    {pair : Finset ℤ} (hp : pair ∈ stPairs I A j v) : pair ⊆ A := by
  obtain ⟨e, he, rfl⟩ := mem_stPairs.mp hp
  exact Finset.Subset.trans Finset.sdiff_subset
    (schurEdges_subset (Finset.mem_filter.mp he).1)

theorem stPairs_mem_notMem {I A : Finset ℤ} {j : ℕ} {v : ℤ}
    {pair : Finset ℤ} (hp : pair ∈ stPairs I A j v) : v ∉ pair := by
  obtain ⟨e, he, rfl⟩ := mem_stPairs.mp hp
  rw [Finset.sdiff_singleton_eq_erase]
  exact fun h => (Finset.mem_erase.mp h).1 rfl

/-- Vertex-degree bound in `P_v`: at most three pairs contain a given
vertex `x ≠ v`, by the pair co-degree bound. -/
theorem stPairs_deg_le_three {I A₀ A : Finset ℤ} (hA : A ⊆ A₀)
    (hpos : ∀ x ∈ A₀, 0 < x) {v x : ℤ} (hvx : v ≠ x) (j : ℕ) :
    ((stPairs I A j v).filter (x ∈ ·)).card ≤ 3 := by
  classical
  have hinj : Set.InjOn (insert v)
      ((stPairs I A j v).filter (x ∈ ·) : Set (Finset ℤ)) := by
    intro p hp q hq h
    rw [Finset.mem_coe, Finset.mem_filter] at hp hq
    have hvp : v ∉ p := stPairs_mem_notMem hp.1
    have hvq : v ∉ q := stPairs_mem_notMem hq.1
    have hp' : p = (insert v p).erase v := (Finset.erase_insert hvp).symm
    rw [hp', h, Finset.erase_insert hvq]
  have himg : ∀ p ∈ (stPairs I A j v).filter (x ∈ ·),
      insert v p ∈ (schurEdges A₀).filter ({v, x} ⊆ ·) := by
    intro p hp
    rw [Finset.mem_filter] at hp
    obtain ⟨e, he, rfl⟩ := mem_stPairs.mp hp.1
    have hve : v ∈ e := (Finset.mem_filter.mp he).2.1
    have hxp : x ∈ e \ {v} := hp.2
    have hxe : x ∈ e := (Finset.mem_sdiff.mp hxp).1
    have heq : insert v (e \ {v}) = e := by
      rw [Finset.insert_eq]
      exact Finset.union_sdiff_of_subset
        (Finset.singleton_subset_iff.mpr hve)
    rw [Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · rw [heq]
      obtain ⟨hesub, hce, a, ha, b, hb, hab, hsum⟩ :=
        mem_schurEdges.mp (Finset.mem_filter.mp he).1
      exact mem_schurEdges.mpr ⟨Finset.Subset.trans hesub hA, hce,
        a, ha, b, hb, hab, hsum⟩
    · rw [heq]
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact hve
      · exact hxe
  calc ((stPairs I A j v).filter (x ∈ ·)).card
      ≤ ((schurEdges A₀).filter ({v, x} ⊆ ·)).card :=
        Finset.card_le_card_of_injOn (insert v) himg hinj
    _ ≤ 3 := schurEdges_pair_le_three hvx hpos

/-- A maximum-cardinality pairwise-disjoint subfamily exists and covers
the family by conflicts. -/
theorem exists_disjoint_subfamily {P : Finset (Finset ℤ)}
    (hp2 : ∀ p ∈ P, p.card = 2)
    (hκ : ∀ x : ℤ, (P.filter (x ∈ ·)).card ≤ 3) :
    ∃ M : Finset (Finset ℤ), M ⊆ P ∧
      (∀ q ∈ M, ∀ r ∈ M, q ≠ r → Disjoint q r) ∧
      P.card ≤ 6 * M.card := by
  classical
  set Q := P.powerset.filter fun M =>
    ∀ q ∈ M, ∀ r ∈ M, q ≠ r → Disjoint q r with hQ
  have hQne : Q.Nonempty :=
    ⟨∅, Finset.mem_filter.mpr ⟨Finset.empty_mem_powerset _,
      fun q hq => (Finset.notMem_empty _ hq).elim⟩⟩
  set c := (Q.image Finset.card).max' (hQne.image _) with hc
  obtain ⟨M, hM, hMc⟩ : ∃ M ∈ Q, M.card = c := by
    have : c ∈ Q.image Finset.card :=
      (Q.image Finset.card).max'_mem (hQne.image _)
    obtain ⟨M, hM, hMc⟩ := Finset.mem_image.mp this
    exact ⟨M, hM, hMc⟩
  have hMP : M ⊆ P :=
    Finset.mem_powerset.mp (Finset.mem_filter.mp hM).1
  have hMd : ∀ q ∈ M, ∀ r ∈ M, q ≠ r → Disjoint q r :=
    (Finset.mem_filter.mp hM).2
  refine ⟨M, hMP, hMd, ?_⟩
  -- Every `p ∈ P` conflicts with some `q ∈ M`.
  have hcov : ∀ p ∈ P, ∃ q ∈ M, ¬ Disjoint p q := by
    intro p hp
    by_contra hcon
    push_neg at hcon
    -- `M ∪ {p}` is a larger disjoint family.
    have hmem : insert p M ∈ Q := by
      rw [hQ, Finset.mem_filter]
      refine ⟨Finset.mem_powerset.mpr
        (Finset.insert_subset_iff.mpr ⟨hp, hMP⟩), ?_⟩
      intro q hq r hr hqr
      rcases Finset.mem_insert.mp hq with rfl | hqM
      · rcases Finset.mem_insert.mp hr with rfl | hrM
        · exact absurd rfl hqr
        · exact hcon r hrM
      · rcases Finset.mem_insert.mp hr with rfl | hrM
        · exact (hcon q hqM).symm
        · exact hMd q hqM r hrM hqr
    have hcard : (insert p M).card ≤ c := by
      have : (insert p M).card ∈ Q.image Finset.card :=
        Finset.mem_image.mpr ⟨insert p M, hmem, rfl⟩
      exact (Q.image Finset.card).le_max' _ this
    by_cases hpM : p ∈ M
    · have := hcon p hpM
      rw [Finset.disjoint_self_iff_empty] at this
      have h2 := hp2 p hp
      rw [this, Finset.card_empty] at h2
      omega
    · rw [Finset.card_insert_of_notMem hpM, hMc] at hcard
      omega
  -- `P ⊆ ⋃_{q ∈ M} ⋃_{x ∈ q} (P.filter (x ∈ ·))`.
  have hsub : P ⊆ M.biUnion fun q =>
      q.biUnion fun x => P.filter (x ∈ ·) := by
    intro p hp
    obtain ⟨q, hqM, hqd⟩ := hcov p hp
    rw [Finset.mem_biUnion]
    refine ⟨q, hqM, ?_⟩
    rw [Finset.mem_biUnion]
    have hne : (p ∩ q).Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr fun h =>
        hqd (Finset.disjoint_iff_inter_eq_empty.mpr h)
    obtain ⟨x, hx⟩ := hne
    obtain ⟨hxp, hxq⟩ := Finset.mem_inter.mp hx
    exact ⟨x, hxq, Finset.mem_filter.mpr ⟨hp, hxp⟩⟩
  calc P.card
      ≤ (M.biUnion fun q => q.biUnion fun x =>
          P.filter (x ∈ ·)).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ q ∈ M, (q.biUnion fun x => P.filter (x ∈ ·)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ q ∈ M, ∑ x ∈ q, (P.filter (x ∈ ·)).card := by
        apply Finset.sum_le_sum
        intro q _
        exact Finset.card_biUnion_le
    _ ≤ ∑ q ∈ M, ∑ x ∈ q, 3 := by
        apply Finset.sum_le_sum
        intro q hq
        apply Finset.sum_le_sum
        intro x _
        exact hκ x
    _ = ∑ q ∈ M, 2 * 3 := by
        apply Finset.sum_congr rfl
        intro q hq
        rw [Finset.sum_const, smul_eq_mul, hp2 q (hMP hq)]
    _ = 6 * M.card := by
        rw [Finset.sum_const, smul_eq_mul]
        ring

/-- If `v ∈ A ∖ I` and some pair `p ∈ P_v` lands inside `W`, then
`v ∈ Γ_j(W ∩ I, W ∩ (A ∖ I))`. -/
theorem mem_stGamma_of_pair {I A₀ A W : Finset ℤ} (j : ℕ)
    (hA : A ⊆ A₀) (hIA : I ⊆ A) (hW : W ⊆ A₀) {v : ℤ}
    (hv : v ∈ A \ I) {pair : Finset ℤ}
    (hp : pair ∈ stPairs I A j v) (hpW : pair ⊆ W) :
    v ∈ stGamma A₀ j (W ∩ I) (W ∩ (A \ I)) := by
  obtain ⟨e, he, rfl⟩ := mem_stPairs.mp hp
  obtain ⟨heE, hve, hcard⟩ := Finset.mem_filter.mp he
  obtain ⟨hesubA, hce, x, hx, y, hy, hxy, hsum⟩ := mem_schurEdges.mp heE
  have hvI : v ∉ I := (Finset.mem_sdiff.mp hv).2
  have he0 : e ∈ schurEdges A₀ :=
    mem_schurEdges.mpr ⟨Finset.Subset.trans hesubA hA, hce,
      x, hx, y, hy, hxy, hsum⟩
  rw [mem_stGamma]
  refine ⟨hA ((Finset.mem_sdiff.mp hv).1), e, he0,
    e ∩ I, (e \ {v}) ∩ (A \ I), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `e = insert v ((e∩I) ∪ (e\{v}∩(A\I)))`
    have ha : (e \ {v}) ∩ I = e ∩ I := by
      ext z
      simp only [Finset.mem_inter, Finset.mem_sdiff,
        Finset.mem_singleton]
      constructor
      · rintro ⟨⟨hze, -⟩, hzI⟩
        exact ⟨hze, hzI⟩
      · rintro ⟨hze, hzI⟩
        exact ⟨⟨hze, fun h => hvI (h ▸ hzI)⟩, hzI⟩
    have hb : (e \ {v}) \ I = (e \ {v}) ∩ (A \ I) := by
      ext z
      simp only [Finset.mem_sdiff, Finset.mem_inter]
      constructor
      · rintro ⟨⟨hze, hzv⟩, hzI⟩
        exact ⟨⟨hze, hzv⟩, ⟨hesubA hze, hzI⟩⟩
      · rintro ⟨⟨hze, hzv⟩, -, hzI⟩
        exact ⟨⟨hze, hzv⟩, hzI⟩
    have h1 : (e ∩ I) ∪ ((e \ {v}) ∩ (A \ I)) = e \ {v} := by
      rw [← ha, ← hb, Finset.union_comm, Finset.sdiff_union_inter]
    rw [h1, Finset.sdiff_singleton_eq_erase]
    exact (Finset.insert_erase hve).symm
  · rw [Finset.mem_union]
    push_neg
    refine ⟨fun h => hvI (Finset.mem_inter.mp h).2, fun h => ?_⟩
    have h1 : v ∈ e \ {v} := (Finset.mem_inter.mp h).1
    exact (Finset.mem_sdiff.mp h1).2 (Finset.mem_singleton_self _)
  · intro z hz
    obtain ⟨hze, hzI⟩ := Finset.mem_inter.mp hz
    have hzv : z ∉ ({v} : Finset ℤ) := fun h =>
      hvI ((Finset.mem_singleton.mp h) ▸ hzI)
    have hzW : z ∈ W := hpW (Finset.mem_sdiff.mpr ⟨hze, hzv⟩)
    exact Finset.mem_inter.mpr ⟨hzW, hzI⟩
  · exact hcard
  · intro z hz
    obtain ⟨hz1, hzAI⟩ := Finset.mem_inter.mp hz
    obtain ⟨hze, hzv⟩ := Finset.mem_sdiff.mp hz1
    have hzW : z ∈ W := hpW (Finset.mem_sdiff.mpr ⟨hze, hzv⟩)
    exact Finset.mem_inter.mpr ⟨hzW, hzAI⟩
  · -- `|(e\{v}) ∩ (A\I)| = 2 - j`
    have hdisj : Disjoint (e ∩ I) ((e \ {v}) ∩ (A \ I)) :=
      Finset.disjoint_left.mpr fun z hz hz' =>
        (Finset.mem_sdiff.mp (Finset.mem_inter.mp hz').2).2
          (Finset.mem_inter.mp hz).2
    have ha : (e \ {v}) ∩ I = e ∩ I := by
      ext z
      simp only [Finset.mem_inter, Finset.mem_sdiff,
        Finset.mem_singleton]
      constructor
      · rintro ⟨⟨hze, -⟩, hzI⟩
        exact ⟨hze, hzI⟩
      · rintro ⟨hze, hzI⟩
        exact ⟨⟨hze, fun h => hvI (h ▸ hzI)⟩, hzI⟩
    have hb : (e \ {v}) \ I = (e \ {v}) ∩ (A \ I) := by
      ext z
      simp only [Finset.mem_sdiff, Finset.mem_inter]
      constructor
      · rintro ⟨⟨hze, hzv⟩, hzI⟩
        exact ⟨⟨hze, hzv⟩, ⟨hesubA hze, hzI⟩⟩
      · rintro ⟨⟨hze, hzv⟩, -, hzI⟩
        exact ⟨⟨hze, hzv⟩, hzI⟩
    have h1 : (e ∩ I) ∪ ((e \ {v}) ∩ (A \ I)) = e \ {v} := by
      rw [← ha, ← hb, Finset.union_comm, Finset.sdiff_union_inter]
    have hcard2 : (e \ {v}).card = 2 := by
      rw [Finset.sdiff_singleton_eq_erase,
        Finset.card_erase_of_mem hve, hce]
    have hunion : (e \ {v}).card =
        (e ∩ I).card + ((e \ {v}) ∩ (A \ I)).card := by
      nth_rewrite 1 [← h1]
      exact Finset.card_union_of_disjoint hdisj
    rw [hcard2, hcard] at hunion
    omega

/-- **Expected trace size.** `E|Γ ∩ I| ≤ (j+1)·p²·|E^{=}_{j+1}(A)|`. -/
theorem stGamma_trace_expected {I A₀ A : Finset ℤ} (hA : A ⊆ A₀)
    (hIA : I ⊆ A) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (j : ℕ) :
    ∑ W ∈ A₀.powerset,
      bernWt A₀ p W *
        ((stGamma A₀ j (W ∩ I) (W ∩ (A \ I)) ∩ I).card : ℝ) ≤
      ((EjEq I A (j + 1)).card : ℝ) * ((j + 1) * p ^ 2) := by
  classical
  have hpt : ∀ W : Finset ℤ, W ⊆ A₀ →
      ((stGamma A₀ j (W ∩ I) (W ∩ (A \ I)) ∩ I).card : ℝ) ≤
        ∑ e ∈ EjEq I A (j + 1),
          (((e ∩ I).filter fun v => e \ {v} ⊆ W).card : ℝ) := by
    intro W hW
    calc ((stGamma A₀ j (W ∩ I) (W ∩ (A \ I)) ∩ I).card : ℝ)
        ≤ (((EjEq I A (j + 1)).biUnion fun e =>
              (e ∩ I).filter fun v => e \ {v} ⊆ W).card : ℝ) := by
          exact_mod_cast Finset.card_le_card
            (stGamma_inter_subset j hA hIA hW)
      _ ≤ ∑ e ∈ EjEq I A (j + 1),
            (((e ∩ I).filter fun v => e \ {v} ⊆ W).card : ℝ) := by
          exact_mod_cast Finset.card_biUnion_le
  calc ∑ W ∈ A₀.powerset,
        bernWt A₀ p W *
          ((stGamma A₀ j (W ∩ I) (W ∩ (A \ I)) ∩ I).card : ℝ)
      ≤ ∑ W ∈ A₀.powerset, bernWt A₀ p W *
          (∑ e ∈ EjEq I A (j + 1),
            (((e ∩ I).filter fun v => e \ {v} ⊆ W).card : ℝ)) := by
        apply Finset.sum_le_sum
        intro W hW
        exact mul_le_mul_of_nonneg_left
          (hpt W (Finset.mem_powerset.mp hW))
          (bernWt_nonneg hp0 hp1 W)
    _ = ∑ e ∈ EjEq I A (j + 1),
          ∑ W ∈ A₀.powerset, bernWt A₀ p W *
            (((e ∩ I).filter fun v => e \ {v} ⊆ W).card : ℝ) := by
        rw [Finset.sum_congr rfl fun W _ => Finset.mul_sum _ _ _]
        exact Finset.sum_comm
    _ = ∑ e ∈ EjEq I A (j + 1), ∑ v ∈ e ∩ I,
          ∑ W ∈ A₀.powerset.filter (fun W => e \ {v} ⊆ W),
            bernWt A₀ p W := by
        apply Finset.sum_congr rfl
        intro e _
        have key : ∀ W : Finset ℤ,
            bernWt A₀ p W *
              (((e ∩ I).filter fun v => e \ {v} ⊆ W).card : ℝ) =
            ∑ v ∈ e ∩ I,
              (if e \ {v} ⊆ W then bernWt A₀ p W else 0) := by
          intro W
          conv_rhs => rw [← Finset.sum_filter]
          rw [Finset.sum_const, nsmul_eq_mul]
          exact mul_comm _ _
        rw [Finset.sum_congr rfl fun W _ => key W]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro v _
        rw [← Finset.sum_filter]
    _ = ∑ e ∈ EjEq I A (j + 1), ∑ v ∈ e ∩ I,
          p ^ (e \ {v}).card := by
        apply Finset.sum_congr rfl
        intro e he
        apply Finset.sum_congr rfl
        intro v hv
        exact bern_subset
          (Finset.Subset.trans Finset.sdiff_subset
            (Finset.Subset.trans
              (schurEdges_subset (Finset.mem_filter.mp he).1) hA))
    _ ≤ ∑ e ∈ EjEq I A (j + 1), ∑ v ∈ e ∩ I, p ^ 2 := by
        apply Finset.sum_le_sum
        intro e he
        apply Finset.sum_le_sum
        intro v hv
        have hv2 : (e \ {v}).card = 2 := by
          rw [Finset.sdiff_singleton_eq_erase,
            Finset.card_erase_of_mem (Finset.mem_inter.mp hv).1,
            schurEdge_card (Finset.mem_filter.mp he).1]
        rw [hv2]
    _ = ((EjEq I A (j + 1)).card : ℝ) * ((j + 1) * p ^ 2) := by
        calc ∑ e ∈ EjEq I A (j + 1), ∑ v ∈ e ∩ I, p ^ 2
            = ∑ e ∈ EjEq I A (j + 1), ((j : ℝ) + 1) * p ^ 2 := by
              apply Finset.sum_congr rfl
              intro e he
              rw [Finset.sum_const, nsmul_eq_mul,
                (Finset.mem_filter.mp he).2]
              push_cast
              ring
          _ = ((EjEq I A (j + 1)).card : ℝ) * ((j + 1) * p ^ 2) := by
              rw [Finset.sum_const, nsmul_eq_mul]

/-- Bernoulli-type bound: `(1 - x)^k ≤ 1 / (1 + k·x)` for `0 ≤ x`. -/
theorem one_sub_pow_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (k : ℕ) :
    (1 - x)^k ≤ 1 / (1 + k * x) := by
  have hk : (0:ℝ) < 1 + k * x := by
    have : (0:ℝ) ≤ k * x := mul_nonneg (Nat.cast_nonneg _) hx0
    linarith
  rw [le_div_iff₀ hk]
  calc (1 - x)^k * (1 + k * x)
      ≤ (1 - x)^k * (1 + x)^k := by
        apply mul_le_mul_of_nonneg_left _
          (pow_nonneg (by linarith : (0:ℝ) ≤ 1 - x) _)
        exact one_add_mul_le_pow (by linarith) k
    _ = ((1 - x) * (1 + x))^k := (mul_pow _ _ _).symm
    _ ≤ (1:ℝ)^k := by
        apply pow_le_pow_left₀ (by nlinarith [sq_nonneg x])
          (by nlinarith [sq_nonneg x]) k
    _ = 1 := one_pow k

/-- **Miss bound.** For `v ∈ A ∖ I` and a pairwise-disjoint family
`M ⊆ P_v`, the probability that `v ∉ Γ` is at most `(1 - p²)^|M|`. -/
theorem stGamma_miss_le {I A₀ A : Finset ℤ} (hA : A ⊆ A₀) (hIA : I ⊆ A)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (j : ℕ) {v : ℤ}
    (hv : v ∈ A \ I) {M : Finset (Finset ℤ)}
    (hM : M ⊆ stPairs I A j v)
    (hMd : ∀ q ∈ M, ∀ r ∈ M, q ≠ r → Disjoint q r) :
    ∑ W ∈ A₀.powerset.filter (fun W =>
        v ∉ stGamma A₀ j (W ∩ I) (W ∩ (A \ I))),
      bernWt A₀ p W ≤
      (1 - p^2) ^ M.card := by
  classical
  have hsub : A₀.powerset.filter (fun W =>
        v ∉ stGamma A₀ j (W ∩ I) (W ∩ (A \ I))) ⊆
      A₀.powerset.filter (fun W => ∀ s ∈ M, ¬ s ⊆ W) := by
    intro W hW
    rw [Finset.mem_filter] at hW ⊢
    refine ⟨hW.1, fun s hs hsW => hW.2 ?_⟩
    exact mem_stGamma_of_pair j hA hIA
      (Finset.mem_powerset.mp hW.1) hv (hM hs) hsW
  calc ∑ W ∈ A₀.powerset.filter (fun W =>
        v ∉ stGamma A₀ j (W ∩ I) (W ∩ (A \ I))), bernWt A₀ p W
      ≤ ∑ W ∈ A₀.powerset.filter (fun W => ∀ s ∈ M, ¬ s ⊆ W),
          bernWt A₀ p W :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun W _ _ =>
          bernWt_nonneg hp0 hp1 W
    _ = ∏ s ∈ M, (1 - p ^ s.card) :=
        bern_all_miss_disjoint M
          (fun s hs => Finset.Subset.trans
            (stPairs_mem_subset (hM hs)) hA)
          hMd
    _ = ∏ s ∈ M, (1 - p ^ 2) :=
        Finset.prod_congr rfl fun s hs => by
          rw [stPairs_mem_card (hM hs)]
    _ = (1 - p ^ 2) ^ M.card := Finset.prod_const _

/-- **Expected missed degree.** If every `v ∈ D` carries a
pairwise-disjoint `M v ⊆ P_v` with `|M v|·p² ≥ 10`, then
`E[degSum(D ∖ Γ)] ≤ degSum(D)/10`. -/
theorem degSum_miss_expected {I A₀ A : Finset ℤ} (hA : A ⊆ A₀)
    (hIA : I ⊆ A) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (j : ℕ)
    {D : Finset ℤ} (hD : D ⊆ A \ I)
    (M : ℤ → Finset (Finset ℤ))
    (hM : ∀ v ∈ D, M v ⊆ stPairs I A j v)
    (hMd : ∀ v ∈ D, ∀ q ∈ M v, ∀ r ∈ M v, q ≠ r → Disjoint q r)
    (hMsize : ∀ v ∈ D, (10:ℝ) ≤ (M v).card * p^2) :
    ∑ W ∈ A₀.powerset,
      bernWt A₀ p W *
        (degSum A₀ (D \ stGamma A₀ j (W ∩ I) (W ∩ (A \ I))) : ℝ) ≤
      (degSum A₀ D : ℝ) / 10 := by
  classical
  have hsplit : ∀ W : Finset ℤ,
      (degSum A₀ (D \ stGamma A₀ j (W ∩ I) (W ∩ (A \ I))) : ℝ) =
        ∑ v ∈ D, (edgeDeg A₀ v : ℝ) *
          (if v ∉ stGamma A₀ j (W ∩ I) (W ∩ (A \ I))
            then (1:ℝ) else 0) := by
    intro W
    unfold degSum
    rw [Finset.sdiff_eq_filter]
    rw [Finset.sum_filter]
    push_cast
    apply Finset.sum_congr rfl
    intro v _
    by_cases h : v ∉ stGamma A₀ j (W ∩ I) (W ∩ (A \ I)) <;> simp [h]
  calc ∑ W ∈ A₀.powerset,
        bernWt A₀ p W *
          (degSum A₀ (D \ stGamma A₀ j (W ∩ I) (W ∩ (A \ I))) : ℝ)
      = ∑ v ∈ D, (edgeDeg A₀ v : ℝ) *
          ∑ W ∈ A₀.powerset.filter (fun W =>
            v ∉ stGamma A₀ j (W ∩ I) (W ∩ (A \ I))),
            bernWt A₀ p W := by
        have key : ∀ W : Finset ℤ,
            bernWt A₀ p W *
              (degSum A₀ (D \ stGamma A₀ j (W ∩ I) (W ∩ (A \ I))) : ℝ) =
            ∑ v ∈ D, (edgeDeg A₀ v : ℝ) *
              (if v ∉ stGamma A₀ j (W ∩ I) (W ∩ (A \ I))
                then bernWt A₀ p W else 0) := by
          intro W
          rw [hsplit W, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro v _
          by_cases h : v ∉ stGamma A₀ j (W ∩ I) (W ∩ (A \ I)) <;>
            simp [h, mul_comm]
        rw [Finset.sum_congr rfl fun W _ => key W]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro v _
        rw [← Finset.mul_sum, ← Finset.sum_filter]
    _ ≤ ∑ v ∈ D, (edgeDeg A₀ v : ℝ) * (1/10) := by
        apply Finset.sum_le_sum
        intro v hv
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        calc ∑ W ∈ A₀.powerset.filter (fun W =>
              v ∉ stGamma A₀ j (W ∩ I) (W ∩ (A \ I))),
              bernWt A₀ p W
            ≤ (1 - p^2) ^ (M v).card :=
              stGamma_miss_le hA hIA p hp0 hp1 j (hD hv) (hM v hv)
                (hMd v hv)
          _ ≤ 1 / (1 + (M v).card * p^2) :=
              one_sub_pow_le (pow_nonneg hp0 _)
                (pow_le_one₀ hp0 hp1) _
          _ ≤ 1/10 :=
              one_div_le_one_div_of_le (by norm_num) (by
                have := hMsize v hv
                linarith)
    _ = (degSum A₀ D : ℝ) / 10 := by
        rw [← Finset.sum_mul]
        unfold degSum
        push_cast
        ring



/-! ## The one-round random choice

A single normalized expectation combines the four quantities: the sizes of
`W ∩ I` and `W ∩ (A ∖ I)` (expectation `p·|·|`), the trace `Γ ∩ I`
(expectation `≤ (j+1)·p²·|E^{=}_{j+1}(A)|`), and the missed degree
`degSum(D ∖ Γ)` (expectation `≤ degSum(D)/10`).  Normalizing each by five
times its expectation bound gives a variable of expectation `≤ 4/5`, so some
`W` beats all four cutoffs. -/

/-- `E^{=}_k(A) ⊆ E_k(A)`: equality of the intersection size implies the
inequality. -/
theorem EjEq_subset_EjSet (I A : Finset ℤ) (k : ℕ) :
    EjEq I A k ⊆ EjSet I A k := by
  intro e he
  rw [EjEq, Finset.mem_filter] at he
  rw [EjSet, Finset.mem_filter]
  exact ⟨he.1, le_of_eq he.2.symm⟩

/-- The pair-family `P_v` has the same cardinality as `F_j(v)`: the map
`e ↦ e ∖ {v}` is injective on `F_j(v)` since `v` lies in every member. -/
theorem stPairs_card_eq (I A : Finset ℤ) (j : ℕ) (v : ℤ) :
    (stPairs I A j v).card = (FjFamily I A j v).card := by
  classical
  unfold stPairs
  apply Finset.card_image_of_injOn
  intro e he f hf h
  rw [Finset.mem_coe] at he hf
  have hve : v ∈ e := (Finset.mem_filter.mp he).2.1
  have hvf : v ∈ f := (Finset.mem_filter.mp hf).2.1
  have h' : e \ {v} = f \ {v} := h
  have key : ∀ g : Finset ℤ, v ∈ g → g = insert v (g \ {v}) := by
    intro g hg
    rw [Finset.insert_eq]
    exact (Finset.union_sdiff_of_subset
      (Finset.singleton_subset_iff.mpr hg)).symm
  rw [key e hve, key f hvf, h']

/-- **Below-expectation point.**  There is always a `W ⊆ A` attaining at
most the weighted mean of `g`. -/
theorem bern_exists_le_exp {A : Finset ℤ} {p : ℝ} (hp0 : 0 < p)
    (hp1 : p ≤ 1) (g : Finset ℤ → ℝ) :
    ∃ W ⊆ A, g W ≤ ∑ W' ∈ A.powerset, bernWt A p W' * g W' := by
  classical
  by_contra hcon
  push_neg at hcon
  set E := ∑ W' ∈ A.powerset, bernWt A p W' * g W' with hE
  have hlt : E < E := calc
    E = ∑ W ∈ A.powerset, bernWt A p W * E := by
        rw [← Finset.sum_mul, bern_total, one_mul]
    _ < ∑ W ∈ A.powerset, bernWt A p W * g W := by
        apply Finset.sum_lt_sum
        · intro W hW
          exact mul_le_mul_of_nonneg_left (le_of_lt (hcon W
            (Finset.mem_powerset.mp hW)))
            (bernWt_nonneg hp0.le hp1 W)
        · refine ⟨A, Finset.mem_powerset.mpr (Finset.Subset.refl _), ?_⟩
          apply mul_lt_mul_of_pos_left (hcon A (Finset.Subset.refl _))
          unfold bernWt
          rw [Finset.sdiff_self, Finset.card_empty, pow_zero, mul_one]
          exact pow_pos hp0 _
  exact lt_irrefl _ hlt

/-- **The one-round choice.**  Given the level `j` ST data for `I ⊆ A ⊆ A₀`
and a probability `p` with `120·|A₀| ≤ e(A₀)·u^j·(1−u)·p²`, there is a
deterministic `W ⊆ A₀` with small `W ∩ I`, `W ∩ (A ∖ I)`, small trace
`Γ ∩ I`, and with `Γ` capturing at least three fifths of the
`D`-degree. -/
theorem exists_round_W {I A₀ A : Finset ℤ}
    (hA : A ⊆ A₀) (hIA : I ⊆ A)
    (hpos : ∀ x ∈ A₀, 0 < x)
    (u : ℝ) (hu0 : 0 < u) (hu1 : u < 1)
    (j : ℕ) (hj : j < 3)
    (he0 : 0 < schurEdgeCount A₀) (hN : 0 < A₀.card)
    (hμA : 1 - 1/6 + ((j:ℝ)+1)/18 ≤ degMeasure A₀ A)
    (hEj : ((EjSet I A (j+1)).card : ℝ) <
      schurEdgeCount A₀ * u^(j+1)/2)
    (hPj : stP I A₀ u j)
    (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1)
    (hpτ : 120 * A₀.card ≤
      schurEdgeCount A₀ * u^j * (1-u) * p^2) :
    ∃ W : Finset ℤ, W ⊆ A₀ ∧
      ((W ∩ I).card : ℝ) ≤ 4 * p * A₀.card ∧
      ((W ∩ (A \ I)).card : ℝ) ≤ 4 * p * A₀.card ∧
      ((stGamma A₀ j (W ∩ I) (W ∩ (A \ I)) ∩ I).card : ℝ) ≤
        2 * (j+1) * p^2 * schurEdgeCount A₀ * u^(j+1) ∧
      (degSum A₀ (stD I A₀ A u j \
        stGamma A₀ j (W ∩ I) (W ∩ (A \ I))) : ℝ) ≤
        (2/5) * degSum A₀ (stD I A₀ A u j) := by
  classical
  set D := stD I A₀ A u j with hDdef
  set Γ : Finset ℤ → Finset ℤ := fun W =>
    stGamma A₀ j (W ∩ I) (W ∩ (A \ I)) with hΓdef
  have hI0 : I ⊆ A₀ := Finset.Subset.trans hIA hA
  have hp0' : 0 ≤ p := hp0.le
  have hIAI : A \ I ⊆ A₀ := Finset.Subset.trans Finset.sdiff_subset hA
  -- The disjoint subfamilies `M v ⊆ P_v` for `v ∈ D`.
  have hDsub : D ⊆ A \ I := stD_subset I A₀ A u j
  have hM : ∀ v : ℤ, ∃ M : Finset (Finset ℤ),
      M ⊆ stPairs I A j v ∧
      (∀ q ∈ M, ∀ r ∈ M, q ≠ r → Disjoint q r) ∧
      (stPairs I A j v).card ≤ 6 * M.card := by
    intro v
    apply exists_disjoint_subfamily
    · exact fun q hq => stPairs_mem_card hq
    · intro x
      by_cases hvx : v = x
      · have : (stPairs I A j v).filter (x ∈ ·) = ∅ := by
          rw [Finset.eq_empty_iff_forall_notMem]
          intro q hq
          obtain ⟨hq1, hq2⟩ := Finset.mem_filter.mp hq
          exact (hvx ▸ stPairs_mem_notMem hq1) hq2
        rw [this, Finset.card_empty]
        exact Nat.zero_le _
      · exact stPairs_deg_le_three hA hpos hvx j
  choose M hMsub hMdij hMcard using hM
  have hMsize : ∀ v ∈ D, (10:ℝ) ≤ (M v).card * p^2 := by
    intro v hv
    have hvτ : stThresh A₀ u j ≤ ((FjFamily I A j v).card : ℝ) :=
      (Finset.mem_filter.mp hv).2
    have hcard : (stPairs I A j v).card = (FjFamily I A j v).card :=
      stPairs_card_eq I A j v
    have h6 : ((stPairs I A j v).card : ℝ) ≤ 6 * (M v).card := by
      exact_mod_cast hMcard v
    have hτ : stThresh A₀ u j / 6 ≤ (M v).card := by
      rw [hcard] at h6
      linarith
    have hτval : stThresh A₀ u j =
        schurEdgeCount A₀ * u^j * (1-u) / (2 * A₀.card) := rfl
    have hN' : (0:ℝ) < A₀.card := Nat.cast_pos.mpr hN
    calc (10:ℝ) = 120 / 12 := by norm_num
      _ = 120 * A₀.card / (12 * A₀.card) := by
          rw [mul_div_mul_right _ _ hN'.ne']
      _ ≤ (schurEdgeCount A₀ * u^j * (1-u) * p^2) /
            (12 * A₀.card) := by
          have hc : (0:ℝ) < 12 * A₀.card := by positivity
          rw [div_le_iff₀ hc]
          calc 120 * A₀.card ≤
              schurEdgeCount A₀ * u^j * (1-u) * p^2 := hpτ
            _ = schurEdgeCount A₀ * u^j * (1-u) * p^2 / (12 * A₀.card) *
                (12 * A₀.card) := by
              rw [div_mul_cancel₀ _ hc.ne']
      _ = stThresh A₀ u j * p^2 / 6 := by
          rw [hτval]
          field_simp
          ring
      _ ≤ (M v).card * p^2 := by
          have hp2 : (0:ℝ) ≤ p^2 := pow_nonneg hp0' _
          calc stThresh A₀ u j * p^2 / 6
              = (stThresh A₀ u j / 6) * p^2 := by ring
            _ ≤ (M v).card * p^2 :=
                mul_le_mul_of_nonneg_right hτ hp2
  -- Expectation bounds.
  have hE1 : ∑ W ∈ A₀.powerset, bernWt A₀ p W *
      ((W ∩ I).card : ℝ) ≤ p * A₀.card := by
    rw [bern_card hI0]
    exact mul_le_mul_of_nonneg_left
      (by exact_mod_cast Finset.card_le_card hI0) hp0'
  have hE2 : ∑ W ∈ A₀.powerset, bernWt A₀ p W *
      ((W ∩ (A \ I)).card : ℝ) ≤ p * A₀.card := by
    rw [bern_card hIAI]
    exact mul_le_mul_of_nonneg_left
      (by exact_mod_cast Finset.card_le_card hIAI) hp0'
  have hE3 : ∑ W ∈ A₀.powerset, bernWt A₀ p W *
      ((Γ W ∩ I).card : ℝ) ≤
      (j+1) * p^2 * schurEdgeCount A₀ * u^(j+1) / 2 := by
    calc ∑ W ∈ A₀.powerset, bernWt A₀ p W * ((Γ W ∩ I).card : ℝ)
        ≤ ((EjEq I A (j + 1)).card : ℝ) * ((j + 1) * p ^ 2) :=
          stGamma_trace_expected hA hIA p hp0' hp1 j
      _ ≤ (schurEdgeCount A₀ * u^(j+1)/2) * ((j + 1) * p ^ 2) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          have hsub : (EjEq I A (j+1)).card ≤
              (EjSet I A (j+1)).card :=
            Finset.card_le_card (EjEq_subset_EjSet I A (j+1))
          have : ((EjEq I A (j+1)).card : ℝ) ≤
              (EjSet I A (j+1)).card := by exact_mod_cast hsub
          linarith
      _ = (j+1) * p^2 * schurEdgeCount A₀ * u^(j+1) / 2 := by ring
  have hE4 : ∑ W ∈ A₀.powerset, bernWt A₀ p W *
      (degSum A₀ (D \ Γ W) : ℝ) ≤
      (degSum A₀ D : ℝ) / 10 :=
    degSum_miss_expected hA hIA p hp0' hp1 j hDsub M
      (fun v _ => hMsub v) (fun v _ => hMdij v) hMsize
  -- Cutoffs and positivity facts.
  have hN' : (0:ℝ) < A₀.card := Nat.cast_pos.mpr hN
  have hc1 : (0:ℝ) < 5 * p * A₀.card := by positivity
  have he0' : (0:ℝ) < schurEdgeCount A₀ := by exact_mod_cast he0
  have hc3 : (0:ℝ) <
      (5/2) * (j+1) * p^2 * schurEdgeCount A₀ * u^(j+1) := by
    positivity
  have hDmeas : 1/18 < degMeasure A₀ D :=
    stD_measure hA hIA u hu0 hu1 hj he0 hN hμA hEj hPj
  have hc4 : (0:ℝ) < (degSum A₀ D : ℝ) / 2 := by
    have hpos' : (0:ℝ) < degSum A₀ D := by
      unfold degMeasure at hDmeas
      have hden : (0:ℝ) < 3 * schurEdgeCount A₀ := by positivity
      have := (lt_div_iff₀ hden).mp hDmeas
      linarith
    positivity
  -- The normalized variable and its expectation.
  set g : Finset ℤ → ℝ := fun W =>
    ((W ∩ I).card : ℝ) / (5 * p * A₀.card) +
    ((W ∩ (A \ I)).card : ℝ) / (5 * p * A₀.card) +
    ((Γ W ∩ I).card : ℝ) /
      ((5/2) * (j+1) * p^2 * schurEdgeCount A₀ * u^(j+1)) +
    (degSum A₀ (D \ Γ W) : ℝ) / ((degSum A₀ D : ℝ) / 2) with hgdef
  have hEW : ∑ W ∈ A₀.powerset, bernWt A₀ p W * g W ≤ 4/5 := by
    have hgx : ∀ W : Finset ℤ, bernWt A₀ p W * g W =
        (5 * p * A₀.card)⁻¹ *
          (bernWt A₀ p W * ((W ∩ I).card : ℝ)) +
        (5 * p * A₀.card)⁻¹ *
          (bernWt A₀ p W * ((W ∩ (A \ I)).card : ℝ)) +
        ((5/2) * (j+1) * p^2 * schurEdgeCount A₀ * u^(j+1))⁻¹ *
          (bernWt A₀ p W * ((Γ W ∩ I).card : ℝ)) +
        ((degSum A₀ D : ℝ) / 2)⁻¹ *
          (bernWt A₀ p W * (degSum A₀ (D \ Γ W) : ℝ)) := by
      intro W
      show bernWt A₀ p W *
          (((W ∩ I).card : ℝ) / (5 * p * A₀.card) +
          ((W ∩ (A \ I)).card : ℝ) / (5 * p * A₀.card) +
          ((Γ W ∩ I).card : ℝ) /
            ((5/2) * (j+1) * p^2 * schurEdgeCount A₀ * u^(j+1)) +
          (degSum A₀ (D \ Γ W) : ℝ) / ((degSum A₀ D : ℝ) / 2)) = _
      ring
    rw [Finset.sum_congr rfl fun W _ => hgx W]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_add_distrib]
    rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
      ← Finset.mul_sum]
    have hb1 : (5 * p * A₀.card)⁻¹ * (∑ W ∈ A₀.powerset,
        bernWt A₀ p W * ((W ∩ I).card : ℝ)) ≤ 1/5 := by
      calc (5 * p * A₀.card)⁻¹ * (∑ W ∈ A₀.powerset,
            bernWt A₀ p W * ((W ∩ I).card : ℝ))
          ≤ (5 * p * A₀.card)⁻¹ * ((5 * p * A₀.card) / 5) := by
            apply mul_le_mul_of_nonneg_left _
              (inv_nonneg.mpr hc1.le)
            calc ∑ W ∈ A₀.powerset, bernWt A₀ p W * ((W ∩ I).card : ℝ)
                ≤ p * A₀.card := hE1
              _ = (5 * p * A₀.card) / 5 := by ring
        _ = 1/5 := by field_simp
    have hb2 : (5 * p * A₀.card)⁻¹ * (∑ W ∈ A₀.powerset,
        bernWt A₀ p W * ((W ∩ (A \ I)).card : ℝ)) ≤ 1/5 := by
      calc (5 * p * A₀.card)⁻¹ * (∑ W ∈ A₀.powerset,
            bernWt A₀ p W * ((W ∩ (A \ I)).card : ℝ))
          ≤ (5 * p * A₀.card)⁻¹ * ((5 * p * A₀.card) / 5) := by
            apply mul_le_mul_of_nonneg_left _
              (inv_nonneg.mpr hc1.le)
            calc ∑ W ∈ A₀.powerset, bernWt A₀ p W *
                  ((W ∩ (A \ I)).card : ℝ)
                ≤ p * A₀.card := hE2
              _ = (5 * p * A₀.card) / 5 := by ring
        _ = 1/5 := by field_simp
    have hb3 : ((5/2) * (j+1) * p^2 * schurEdgeCount A₀ * u^(j+1))⁻¹ *
        (∑ W ∈ A₀.powerset, bernWt A₀ p W * ((Γ W ∩ I).card : ℝ)) ≤
        1/5 := by
      calc ((5/2) * (j+1) * p^2 * schurEdgeCount A₀ * u^(j+1))⁻¹ *
            (∑ W ∈ A₀.powerset, bernWt A₀ p W * ((Γ W ∩ I).card : ℝ))
          ≤ ((5/2) * (j+1) * p^2 * schurEdgeCount A₀ * u^(j+1))⁻¹ *
            (((5/2) * (j+1) * p^2 * schurEdgeCount A₀ * u^(j+1)) / 5) := by
            apply mul_le_mul_of_nonneg_left _
              (inv_nonneg.mpr hc3.le)
            calc ∑ W ∈ A₀.powerset, bernWt A₀ p W * ((Γ W ∩ I).card : ℝ)
                ≤ (j+1) * p^2 * schurEdgeCount A₀ * u^(j+1) / 2 := hE3
              _ = ((5/2) * (j+1) * p^2 * schurEdgeCount A₀ * u^(j+1)) / 5
                  := by ring
        _ = 1/5 := by field_simp
    have hb4 : ((degSum A₀ D : ℝ) / 2)⁻¹ * (∑ W ∈ A₀.powerset,
        bernWt A₀ p W * (degSum A₀ (D \ Γ W) : ℝ)) ≤ 1/5 := by
      calc ((degSum A₀ D : ℝ) / 2)⁻¹ * (∑ W ∈ A₀.powerset,
            bernWt A₀ p W * (degSum A₀ (D \ Γ W) : ℝ))
          ≤ ((degSum A₀ D : ℝ) / 2)⁻¹ *
            (((degSum A₀ D : ℝ) / 2) / 5) := by
            apply mul_le_mul_of_nonneg_left _
              (inv_nonneg.mpr hc4.le)
            calc ∑ W ∈ A₀.powerset, bernWt A₀ p W *
                  (degSum A₀ (D \ Γ W) : ℝ)
                ≤ (degSum A₀ D : ℝ) / 10 := hE4
              _ = ((degSum A₀ D : ℝ) / 2) / 5 := by ring
        _ = 1/5 := by
          have hdne : (degSum A₀ D : ℝ) ≠ 0 :=
            ne_of_gt (by linarith : (0:ℝ) < degSum A₀ D)
          field_simp
    linarith [hb1, hb2, hb3, hb4]
  obtain ⟨W, hW, hWle⟩ := bern_exists_le_exp hp0 hp1 g
  have hterms : ((W ∩ I).card : ℝ) / (5 * p * A₀.card) ≤ g W ∧
      ((W ∩ (A \ I)).card : ℝ) / (5 * p * A₀.card) ≤ g W ∧
      ((Γ W ∩ I).card : ℝ) /
        ((5/2) * (j+1) * p^2 * schurEdgeCount A₀ * u^(j+1)) ≤ g W ∧
      (degSum A₀ (D \ Γ W) : ℝ) / ((degSum A₀ D : ℝ) / 2) ≤ g W := by
    rw [show g W = ((W ∩ I).card : ℝ) / (5 * p * A₀.card) +
        ((W ∩ (A \ I)).card : ℝ) / (5 * p * A₀.card) +
        ((Γ W ∩ I).card : ℝ) /
          ((5/2) * (j+1) * p^2 * schurEdgeCount A₀ * u^(j+1)) +
        (degSum A₀ (D \ Γ W) : ℝ) / ((degSum A₀ D : ℝ) / 2) from rfl]
    refine ⟨?_, ?_, ?_, ?_⟩
    · have h2 : (0:ℝ) ≤ (W ∩ (A \ I)).card / (5 * p * A₀.card) :=
        div_nonneg (Nat.cast_nonneg _) hc1.le
      have h3 : (0:ℝ) ≤ (Γ W ∩ I).card /
          ((5/2) * (j+1) * p^2 * schurEdgeCount A₀ * u^(j+1)) :=
        div_nonneg (Nat.cast_nonneg _) hc3.le
      have h4 : (0:ℝ) ≤ (degSum A₀ (D \ Γ W) : ℝ) /
          ((degSum A₀ D : ℝ) / 2) :=
        div_nonneg (Nat.cast_nonneg _) hc4.le
      calc ((W ∩ I).card : ℝ) / (5 * p * A₀.card)
          ≤ (W ∩ I).card / (5 * p * A₀.card) +
              (W ∩ (A \ I)).card / (5 * p * A₀.card) :=
            le_add_of_nonneg_right h2
        _ ≤ ((W ∩ I).card / (5 * p * A₀.card) +
              (W ∩ (A \ I)).card / (5 * p * A₀.card)) +
              (Γ W ∩ I).card /
                ((5/2) * (j+1) * p^2 * schurEdgeCount A₀ * u^(j+1)) :=
            le_add_of_nonneg_right h3
        _ ≤ ((W ∩ I).card / (5 * p * A₀.card) +
              (W ∩ (A \ I)).card / (5 * p * A₀.card) +
              (Γ W ∩ I).card /
                ((5/2) * (j+1) * p^2 * schurEdgeCount A₀ * u^(j+1))) +
              (degSum A₀ (D \ Γ W) : ℝ) /
                ((degSum A₀ D : ℝ) / 2) :=
            le_add_of_nonneg_right h4
    · have h1 : (0:ℝ) ≤ (W ∩ I).card / (5 * p * A₀.card) :=
        div_nonneg (Nat.cast_nonneg _) hc1.le
      have h3 : (0:ℝ) ≤ (Γ W ∩ I).card /
          ((5/2) * (j+1) * p^2 * schurEdgeCount A₀ * u^(j+1)) :=
        div_nonneg (Nat.cast_nonneg _) hc3.le
      have h4 : (0:ℝ) ≤ (degSum A₀ (D \ Γ W) : ℝ) /
          ((degSum A₀ D : ℝ) / 2) :=
        div_nonneg (Nat.cast_nonneg _) hc4.le
      calc ((W ∩ (A \ I)).card : ℝ) / (5 * p * A₀.card)
          ≤ (W ∩ I).card / (5 * p * A₀.card) +
              (W ∩ (A \ I)).card / (5 * p * A₀.card) :=
            le_add_of_nonneg_left h1
        _ ≤ ((W ∩ I).card / (5 * p * A₀.card) +
              (W ∩ (A \ I)).card / (5 * p * A₀.card)) +
              (Γ W ∩ I).card /
                ((5/2) * (j+1) * p^2 * schurEdgeCount A₀ * u^(j+1)) :=
            le_add_of_nonneg_right h3
        _ ≤ ((W ∩ I).card / (5 * p * A₀.card) +
              (W ∩ (A \ I)).card / (5 * p * A₀.card) +
              (Γ W ∩ I).card /
                ((5/2) * (j+1) * p^2 * schurEdgeCount A₀ * u^(j+1))) +
              (degSum A₀ (D \ Γ W) : ℝ) /
                ((degSum A₀ D : ℝ) / 2) :=
            le_add_of_nonneg_right h4
    · have h1 : (0:ℝ) ≤ (W ∩ I).card / (5 * p * A₀.card) :=
        div_nonneg (Nat.cast_nonneg _) hc1.le
      have h2 : (0:ℝ) ≤ (W ∩ (A \ I)).card / (5 * p * A₀.card) :=
        div_nonneg (Nat.cast_nonneg _) hc1.le
      have h4 : (0:ℝ) ≤ (degSum A₀ (D \ Γ W) : ℝ) /
          ((degSum A₀ D : ℝ) / 2) :=
        div_nonneg (Nat.cast_nonneg _) hc4.le
      calc ((Γ W ∩ I).card : ℝ) /
            ((5/2) * (j+1) * p^2 * schurEdgeCount A₀ * u^(j+1))
          ≤ ((W ∩ I).card / (5 * p * A₀.card) +
              (W ∩ (A \ I)).card / (5 * p * A₀.card)) +
              (Γ W ∩ I).card /
                ((5/2) * (j+1) * p^2 * schurEdgeCount A₀ * u^(j+1)) :=
            le_add_of_nonneg_left (add_nonneg h1 h2)
        _ ≤ ((W ∩ I).card / (5 * p * A₀.card) +
              (W ∩ (A \ I)).card / (5 * p * A₀.card) +
              (Γ W ∩ I).card /
                ((5/2) * (j+1) * p^2 * schurEdgeCount A₀ * u^(j+1))) +
              (degSum A₀ (D \ Γ W) : ℝ) /
                ((degSum A₀ D : ℝ) / 2) :=
            le_add_of_nonneg_right h4
    · have h1 : (0:ℝ) ≤ (W ∩ I).card / (5 * p * A₀.card) :=
        div_nonneg (Nat.cast_nonneg _) hc1.le
      have h2 : (0:ℝ) ≤ (W ∩ (A \ I)).card / (5 * p * A₀.card) :=
        div_nonneg (Nat.cast_nonneg _) hc1.le
      have h3 : (0:ℝ) ≤ (Γ W ∩ I).card /
          ((5/2) * (j+1) * p^2 * schurEdgeCount A₀ * u^(j+1)) :=
        div_nonneg (Nat.cast_nonneg _) hc3.le
      exact le_add_of_nonneg_left (add_nonneg (add_nonneg h1 h2) h3)
  obtain ⟨ht1, ht2, ht3, ht4⟩ := hterms
  have hWle' : g W ≤ 4/5 := le_trans hWle hEW
  refine ⟨W, hW, ?_, ?_, ?_, ?_⟩
  · have := (div_le_iff₀ hc1).mp (le_trans ht1 hWle')
    calc ((W ∩ I).card : ℝ) ≤ (4/5) * (5 * p * A₀.card) := by
          linarith [this]
    _ = 4 * p * A₀.card := by ring
  · have := (div_le_iff₀ hc1).mp (le_trans ht2 hWle')
    calc ((W ∩ (A \ I)).card : ℝ) ≤ (4/5) * (5 * p * A₀.card) := by
          linarith [this]
    _ = 4 * p * A₀.card := by ring
  · have := (div_le_iff₀ hc3).mp (le_trans ht3 hWle')
    calc ((Γ W ∩ I).card : ℝ) ≤
          (4/5) * ((5/2) * (j+1) * p^2 * schurEdgeCount A₀ * u^(j+1)) :=
        by linarith [this]
    _ = 2 * (j+1) * p^2 * schurEdgeCount A₀ * u^(j+1) := by ring
  · have := (div_le_iff₀ hc4).mp (le_trans ht4 hWle')
    calc (degSum A₀ (D \ Γ W) : ℝ) ≤
          (4/5) * ((degSum A₀ D : ℝ) / 2) := by
          linarith [this]
    _ = (2/5) * degSum A₀ D := by ring

/-! ## The one-round container

`roundContainer A₀ j R S' T = (A₀ ∖ Γ_j(R,S')) ∪ T`.  Combining
`st_level_exists` with `exists_round_W` gives `j ≤ 2` and recorded sets
`R = W ∩ I`, `S' = W ∩ (A ∖ I)`, `T = Γ ∩ I` such that the container covers
`I` and has at most `29/30` of the ambient edge count, while `R`, `S'`, `T`
are small. -/

/-- The one-round container. -/
noncomputable def roundContainer (A₀ : Finset ℤ) (j : ℕ)
    (R S' T : Finset ℤ) : Finset ℤ :=
  (A₀ \ stGamma A₀ j R S') ∪ T

/-- **One-round container lemma.**  There exist `j ≤ 2` and recorded
`R, S', T ⊆ A₀` of bounded size with `I ⊆ roundContainer A₀ j R S' T` and
`e(roundContainer) ≤ (29/30)·e(A₀)`. -/
theorem one_round {I A₀ : Finset ℤ} (hI : I ⊆ A₀) (hIsf : IsSumFree I)
    (hpos : ∀ x ∈ A₀, 0 < x)
    (u : ℝ) (hu0 : 0 < u) (hu1 : u < 1)
    (he0 : 0 < schurEdgeCount A₀) (hN : 0 < A₀.card)
    (p : ℕ → ℝ)
    (hp : ∀ j, j ≤ 2 → 0 < p j)
    (hp1 : ∀ j, j ≤ 2 → p j ≤ 1)
    (hpτ : ∀ j, j ≤ 2 → 120 * A₀.card ≤
      schurEdgeCount A₀ * u^j * (1-u) * (p j)^2) :
    ∃ j : ℕ, j ≤ 2 ∧ ∃ R S' T : Finset ℤ,
      R ⊆ A₀ ∧ S' ⊆ A₀ ∧ T ⊆ A₀ ∧
      I ⊆ roundContainer A₀ j R S' T ∧
      roundContainer A₀ j R S' T ⊆ A₀ ∧
      (schurEdgeCount (roundContainer A₀ j R S' T) : ℝ) ≤
        (29/30) * schurEdgeCount A₀ ∧
      (R.card : ℝ) ≤ 4 * p j * A₀.card ∧
      (S'.card : ℝ) ≤ 4 * p j * A₀.card ∧
      (T.card : ℝ) ≤
        2 * (j+1) * (p j)^2 * schurEdgeCount A₀ * u^(j+1) := by
  classical
  obtain ⟨j, hj, A, hA, hIA, hμA, hEj, hPj⟩ :=
    st_level_exists hI hIsf u hu0 he0
  obtain ⟨W, hW, hR, hS, hT, hD⟩ := exists_round_W hA hIA hpos u hu0
    hu1 j (by omega) he0 hN hμA hEj hPj (p j) (hp j hj) (hp1 j hj) (hpτ j hj)
  set Γ := stGamma A₀ j (W ∩ I) (W ∩ (A \ I)) with hΓ
  set R := W ∩ I with hRdef
  set S' := W ∩ (A \ I) with hSdef
  set T := Γ ∩ I with hTdef
  refine ⟨j, hj, R, S', T, ?_, ?_, ?_, ?_, ?_, ?_, hR, hS, hT⟩
  · exact Finset.Subset.trans Finset.inter_subset_left hW
  · exact Finset.Subset.trans Finset.inter_subset_left hW
  · exact Finset.Subset.trans Finset.inter_subset_right hI
  · -- `I ⊆ (A₀ ∖ Γ) ∪ T`: a vertex of `I` is either outside `Γ` or in `T`.
    intro v hv
    rw [roundContainer, Finset.mem_union]
    by_cases hvΓ : v ∈ Γ
    · right
      rw [hTdef]
      exact Finset.mem_inter.mpr ⟨hvΓ, hv⟩
    · left
      exact Finset.mem_sdiff.mpr ⟨hI hv, hvΓ⟩
  · -- `(A₀ ∖ Γ) ∪ T ⊆ A₀`.
    rw [roundContainer]
    exact Finset.union_subset Finset.sdiff_subset
      (Finset.Subset.trans Finset.inter_subset_right hI)
  · -- The edge count drops by `29/30`.
    set C := roundContainer A₀ j R S' T with hC
    have hCsub : C ⊆ A₀ := by
      rw [hC, roundContainer]
      exact Finset.union_subset Finset.sdiff_subset
        (Finset.Subset.trans Finset.inter_subset_right hI)
    set D := stD I A₀ A u j with hDdef
    -- `A₀ ∖ C = Γ ∖ I`.
    have hcompl : A₀ \ C = Γ \ I := by
      have hΓsub : Γ ⊆ A₀ := stGamma_subset _ _ _ _
      have hΓT : Γ ∩ (A₀ \ T) = Γ \ T := by
        ext v
        simp only [Finset.mem_inter, Finset.mem_sdiff]
        constructor
        · rintro ⟨hvΓ, -, hvT⟩
          exact ⟨hvΓ, hvT⟩
        · rintro ⟨hvΓ, hvT⟩
          exact ⟨hvΓ, hΓsub hvΓ, hvT⟩
      show A₀ \ ((A₀ \ Γ) ∪ T) = Γ \ I
      rw [Finset.sdiff_union_distrib, Finset.sdiff_sdiff_self_left,
        Finset.inter_eq_right.mpr hΓsub, hΓT, hTdef,
        Finset.sdiff_inter_self_left]
    -- `Γ ∩ D ⊆ Γ ∖ I`, and `D` has measure `> 1/18`.
    have hDmeas : 1/18 < degMeasure A₀ D :=
      stD_measure hA hIA u hu0 hu1 (by omega) he0 hN hμA hEj hPj
    have hGD : Γ ∩ D ⊆ Γ \ I := by
      intro v hv
      rw [Finset.mem_sdiff]
      exact ⟨Finset.mem_inter.mp hv |>.1,
        fun hvI => (Finset.mem_sdiff.mp
          (stD_subset I A₀ A u j (Finset.mem_inter.mp hv |>.2))).2 hvI⟩
    have hsplit : degSum A₀ (Γ ∩ D) + degSum A₀ (D \ Γ) = degSum A₀ D := by
      have hdisj : Disjoint (Γ ∩ D) (D \ Γ) :=
        Finset.disjoint_left.mpr fun x hx hx' =>
          (Finset.mem_sdiff.mp hx').2 (Finset.mem_inter.mp hx).1
      rw [← degSum_union hdisj]
      congr 1
      ext v
      simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
      constructor
      · rintro (⟨hvΓ, hvD⟩ | ⟨hvD, -⟩) <;> exact hvD
      · intro hvD
        by_cases hvΓ : v ∈ Γ
        · exact Or.inl ⟨hvΓ, hvD⟩
        · exact Or.inr ⟨hvD, hvΓ⟩
    have hcompl' : degSum A₀ (A₀ \ C) + degSum A₀ C =
        3 * schurEdgeCount A₀ := by
      have h := degSum_add_compl hCsub
      linarith [h]
    have h3e : 3 * schurEdgeCount C ≤ degSum A₀ C :=
      schurEdgeCount_le_degSum hCsub
    -- Assemble the inequality.
    have hcap : (degSum A₀ D : ℝ) - degSum A₀ (D \ Γ) ≥
        (3/5) * degSum A₀ D := by linarith [hD]
    have hdeg : (degSum A₀ (A₀ \ C) : ℝ) ≥ (3/5) * degSum A₀ D := by
      rw [hcompl]
      have hmono : degSum A₀ (Γ ∩ D) ≤ degSum A₀ (Γ \ I) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hGD
        intro v _ _
        exact Nat.zero_le _
      have hsplit' : (degSum A₀ (Γ ∩ D) : ℝ) + degSum A₀ (D \ Γ) =
          degSum A₀ D := by exact_mod_cast hsplit
      have h1 : (degSum A₀ (Γ \ I) : ℝ) ≥ degSum A₀ (Γ ∩ D) := by
        exact_mod_cast hmono
      linarith [hcap]
    have hDlb : (1/18) * (3 * schurEdgeCount A₀ : ℝ) < degSum A₀ D := by
      unfold degMeasure at hDmeas
      have hden : (0:ℝ) < 3 * schurEdgeCount A₀ := by
        have : (0:ℝ) < schurEdgeCount A₀ := by exact_mod_cast he0
        linarith
      rw [lt_div_iff₀ hden] at hDmeas
      linarith [hDmeas]
    have hcomplr : (degSum A₀ (A₀ \ C) : ℝ) + degSum A₀ C =
        3 * schurEdgeCount A₀ := by exact_mod_cast hcompl'
    have h3er : (3:ℝ) * schurEdgeCount C ≤ degSum A₀ C := by
      exact_mod_cast h3e
    have he0' : (0:ℝ) < schurEdgeCount A₀ := by exact_mod_cast he0
    linarith [hdeg, hDlb, hcomplr, h3er]

/-! ## Iteration: fingerprint entries, bridge lemmas -/

/-- `Γ_0(∅, ∅) = ∅`: a decomposition would need `g ⊆ ∅` of size `2`. -/
theorem stGamma_zero_empty (A₀ : Finset ℤ) :
    stGamma A₀ 0 ∅ ∅ = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro v hv
  obtain ⟨_, e, heE, f, g, heq, hvfg, hfR, hfj, hgS, hgj⟩ :=
    mem_stGamma.mp hv
  rw [Finset.subset_empty] at hgS
  rw [hgS, Finset.card_empty] at hgj
  omega

/-- A single round of fingerprint data `(j, R, S', T)`. -/
abbrev RoundEntry := Fin 3 × Finset ℤ × Finset ℤ × Finset ℤ

/-- Apply one round to the ambient set. -/
noncomputable def applyEntry (A : Finset ℤ) (e : RoundEntry) : Finset ℤ :=
  roundContainer A (e.1 : ℕ) e.2.1 e.2.2.1 e.2.2.2

/-- The identity entry `(0, ∅, ∅, ∅)` leaves `A` unchanged. -/
theorem applyEntry_id (A : Finset ℤ) :
    applyEntry A (⟨0, by omega⟩, ∅, ∅, ∅) = A := by
  unfold applyEntry roundContainer
  rw [show ((⟨0, by omega⟩ : Fin 3) : ℕ) = 0 from rfl, stGamma_zero_empty,
    Finset.sdiff_empty, Finset.union_empty]

/-- `schurEdges A ⊆ A.powersetCard 3`. -/
theorem schurEdges_subset_powersetCard (A : Finset ℤ) :
    schurEdges A ⊆ A.powersetCard 3 := by
  intro e he
  rw [Finset.mem_powersetCard]
  exact ⟨schurEdges_subset he, schurEdge_card he⟩

theorem schurEdgeCount_le_choose (A : Finset ℤ) :
    schurEdgeCount A ≤ A.card.choose 3 := by
  unfold schurEdgeCount
  calc (schurEdges A).card ≤ (A.powersetCard 3).card :=
        Finset.card_le_card (schurEdges_subset_powersetCard A)
    _ = A.card.choose 3 := Finset.card_powersetCard _ _

/-- Weak Schur triples are bounded by strict edges plus the diagonal:
`schurTripleCount C ≤ 9·schurEdgeCount C + n`. -/
theorem schurTripleCount_le_edge_card {n : ℕ} {C : Finset ℤ}
    (hC : C ⊆ interval n) :
    schurTripleCount C ≤ 9 * schurEdgeCount C + n := by
  classical
  have hpos : ∀ x ∈ C, 0 < x := by
    intro x hx
    have := hC hx
    rw [interval, Finset.mem_Icc] at this
    linarith [this.1]
  -- Map each triple `(x, y, x+y)` to its ordered pair `(x, y)`.
  have hinj : Set.InjOn (fun t : ℤ × ℤ × ℤ => (t.1, t.2.1))
      (schurTriples C : Set (ℤ × ℤ × ℤ)) := by
    intro t ht s' hs' hts
    rw [Finset.mem_coe, schurTriples, Finset.mem_filter] at ht hs'
    rcases t with ⟨x, y, z⟩
    rcases s' with ⟨x', y', z'⟩
    obtain ⟨-, hsum⟩ := ht
    obtain ⟨-, hsum'⟩ := hs'
    dsimp only at hsum hsum'
    simp only [] at hts
    simp only [Prod.mk.injEq] at hts ⊢
    exact ⟨hts.1, hts.2, by rw [← hsum, ← hsum', hts.1, hts.2]⟩
  have himg : (schurTriples C).image (fun t => (t.1, t.2.1)) ⊆
      (C ×ˢ C).filter (fun p => p.1 + p.2 ∈ C) := by
    intro p hp
    rw [Finset.mem_image] at hp
    obtain ⟨t, ht, rfl⟩ := hp
    rw [schurTriples, Finset.mem_filter, Finset.mem_product,
      Finset.mem_product] at ht
    obtain ⟨⟨hx, hy, hz⟩, hsum⟩ := ht
    rw [Finset.mem_filter, Finset.mem_product]
    refine ⟨⟨hx, hy⟩, ?_⟩
    show t.1 + t.2.1 ∈ C
    rw [hsum]
    exact hz
  have hcard : schurTripleCount C ≤
      ((C ×ˢ C).filter (fun p => p.1 + p.2 ∈ C)).card := by
    unfold schurTripleCount
    calc (schurTriples C).card =
          ((schurTriples C).image (fun t => (t.1, t.2.1))).card :=
          (Finset.card_image_of_injOn hinj).symm
      _ ≤ ((C ×ˢ C).filter (fun p => p.1 + p.2 ∈ C)).card :=
          Finset.card_le_card himg
  -- Split the pair set on `x = y`.
  set offdiag := (C ×ˢ C).filter fun p => p.1 + p.2 ∈ C ∧ p.1 ≠ p.2
  set diag := (C ×ˢ C).filter fun p => p.1 + p.2 ∈ C ∧ p.1 = p.2
  have hsplit : (C ×ˢ C).filter (fun p => p.1 + p.2 ∈ C) ⊆
      offdiag ∪ diag := by
    intro p hp
    rw [Finset.mem_filter] at hp
    by_cases hxy : p.1 = p.2
    · exact Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨hp.1, hp.2, hxy⟩)
    · exact Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨hp.1, hp.2, hxy⟩)
  have hunion : ((C ×ˢ C).filter (fun p => p.1 + p.2 ∈ C)).card ≤
      offdiag.card + diag.card :=
    (Finset.card_le_card hsplit).trans (Finset.card_union_le _ _)
  have hdiag : diag.card ≤ n := by
    calc diag.card ≤ (diag.image Prod.fst).card := by
          apply Finset.card_le_card_of_injOn Prod.fst
          · intro p hp
            exact Finset.mem_image_of_mem _ hp
          · intro p hp q hq hpq
            rw [Finset.mem_coe, Finset.mem_filter] at hp hq
            exact Prod.ext hpq (hp.2.2.symm.trans (hpq.trans hq.2.2))
      _ ≤ C.card :=
          Finset.card_le_card (by
            intro x hx
            rw [Finset.mem_image] at hx
            obtain ⟨p, hp, rfl⟩ := hx
            exact (Finset.mem_product.mp
              (Finset.mem_filter.mp hp).1).1)
      _ ≤ n := by
          have := Finset.card_le_card hC
          rwa [card_interval] at this
  -- `(x,y) ↦ {x,y,x+y}` maps `offdiag` into `schurEdges C` with
  -- fibers of size at most `9`.
  have hoff : offdiag.card ≤ 9 * schurEdgeCount C := by
    have hmaps : ∀ p ∈ offdiag,
        ({p.1, p.2, p.1 + p.2} : Finset ℤ) ∈ schurEdges C := by
      intro p hp
      rw [Finset.mem_filter, Finset.mem_product] at hp
      obtain ⟨⟨hx, hy⟩, hsum, hxy⟩ := hp
      have hxp := hpos p.1 hx
      have hyp := hpos p.2 hy
      rw [mem_schurEdges]
      refine ⟨?_, ?_, p.1, ?_, p.2, ?_, hxy, ?_⟩
      · intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl | rfl
        · exact hx
        · exact hy
        · exact hsum
      · have hp2 : ({p.2, p.1 + p.2} : Finset ℤ).card = 2 :=
          Finset.card_pair
            (ne_of_lt (by linarith : p.2 < p.1 + p.2))
        have hnot : p.1 ∉ ({p.2, p.1 + p.2} : Finset ℤ) := by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨hxy, ne_of_lt (by linarith : p.1 < p.1 + p.2)⟩
        rw [Finset.card_insert_of_notMem hnot, hp2]
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
      · exact Finset.mem_insert_of_mem
          (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    have hfiber : ∀ e ∈ offdiag.image (fun p => {p.1, p.2, p.1 + p.2}),
        (offdiag.filter fun p =>
          ({p.1, p.2, p.1 + p.2} : Finset ℤ) = e).card ≤ 9 := by
      intro e he
      calc (offdiag.filter fun p =>
            ({p.1, p.2, p.1 + p.2} : Finset ℤ) = e).card
          ≤ (e ×ˢ e).card := by
            apply Finset.card_le_card
            intro p hp
            rw [Finset.mem_filter] at hp
            rw [Finset.mem_product]
            constructor
            · rw [← hp.2]
              exact Finset.mem_insert_self _ _
            · rw [← hp.2]
              exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
        _ = e.card * e.card := Finset.card_product _ _
        _ ≤ 9 := by
            have hce : e.card = 3 := by
              rw [Finset.mem_image] at he
              obtain ⟨p, hp, rfl⟩ := he
              exact schurEdge_card (hmaps p hp)
            rw [hce]
    calc offdiag.card ≤ 9 * (offdiag.image
          (fun p => {p.1, p.2, p.1 + p.2})).card :=
        Finset.card_le_mul_card_image _ 9 hfiber
      _ ≤ 9 * schurEdgeCount C :=
        Nat.mul_le_mul_left _
          (Finset.card_le_card (by
            intro e he
            rw [Finset.mem_image] at he
            obtain ⟨p, hp, rfl⟩ := he
            exact hmaps p hp))
  calc schurTripleCount C ≤ offdiag.card + diag.card :=
        hcard.trans hunion
    _ ≤ 9 * schurEdgeCount C + n := Nat.add_le_add hoff hdiag

/-! ## Iteration infrastructure -/

theorem schurEdges_mono {C A : Finset ℤ} (h : C ⊆ A) :
    schurEdges C ⊆ schurEdges A := by
  intro e he
  rw [mem_schurEdges] at he ⊢
  obtain ⟨heC, hcard, x, hx, y, hy, hxy, hsum⟩ := he
  exact ⟨heC.trans h, hcard, x, hx, y, hy, hxy, hsum⟩

theorem schurEdgeCount_mono {C A : Finset ℤ} (h : C ⊆ A) :
    schurEdgeCount C ≤ schurEdgeCount A :=
  Finset.card_le_card (schurEdges_mono h)

/-- Every edge of `schurEdges (interval n)` has the form `{x, y, x+y}` with
`x, y` positive and distinct, and `e.erase (∑e/2) = {x, y}`. -/
theorem schurEdges_interval_normal {n : ℕ} {e : Finset ℤ}
    (he : e ∈ schurEdges (interval n)) :
    ∃ x y : ℤ, x ≠ y ∧ 0 < x ∧ 0 < y ∧
      e = {x, y, x + y} ∧ e.erase ((∑ z ∈ e, z) / 2) = {x, y} := by
  obtain ⟨heA, hcard, x, hx, y, hy, hxy, hsum⟩ := mem_schurEdges.mp he
  have hxpos : 0 < x := by
    have := heA hx
    rw [interval, Finset.mem_Icc] at this; linarith [this.1]
  have hypos : 0 < y := by
    have := heA hy
    rw [interval, Finset.mem_Icc] at this; linarith [this.1]
  have hnot : x ∉ ({y, x + y} : Finset ℤ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hxy, by omega⟩
  have heq : e = {x, y, x + y} := by
    have hsub : ({x, y, x + y} : Finset ℤ) ⊆ e := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl
      · exact hx
      · exact hy
      · exact hsum
    have hcard3 : ({x, y, x + y} : Finset ℤ).card = 3 := by
      rw [Finset.card_insert_of_notMem hnot, Finset.card_pair (by omega)]
    exact (Finset.eq_of_subset_of_card_le hsub
      (by rw [hcard, hcard3])).symm
  refine ⟨x, y, hxy, hxpos, hypos, heq, ?_⟩
  have hsum2 : (∑ z ∈ e, z) = 2 * (x + y) := by
    rw [heq, Finset.sum_insert hnot, Finset.sum_pair (by omega : y ≠ x + y)]
    ring
  rw [hsum2, show 2 * (x + y) / 2 = x + y by omega, heq]
  ext z
  simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hzne, hz⟩
    rcases hz with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact absurd rfl hzne
  · intro hz
    rcases hz with rfl | rfl
    · exact ⟨by omega, Or.inl rfl⟩
    · exact ⟨by omega, Or.inr (Or.inl rfl)⟩

/-- `schurEdgeCount (interval n) ≤ n²`: the map `e ↦ e.erase (∑e/2)` sends
each strict edge `{x, y, x+y}` to its summand pair `{x, y}`, injectively
into `powersetCard 2`. -/
theorem schurEdgeCount_interval_le (n : ℕ) :
    schurEdgeCount (interval n) ≤ n ^ 2 := by
  classical
  have hmaps : ∀ e ∈ schurEdges (interval n),
      e.erase ((∑ z ∈ e, z) / 2) ∈ (interval n).powersetCard 2 := by
    intro e he
    obtain ⟨x, y, hxy, hxpos, hypos, heq, hφ⟩ :=
      schurEdges_interval_normal he
    rw [Finset.mem_powersetCard, hφ]
    obtain ⟨heA, _, _⟩ := mem_schurEdges.mp he
    refine ⟨?_, Finset.card_pair hxy⟩
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact heA (by rw [heq]; exact Finset.mem_insert_self _ _)
    · exact heA (by
        rw [heq]
        exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have hinj : Set.InjOn (fun e => e.erase ((∑ z ∈ e, z) / 2))
      (schurEdges (interval n) : Set (Finset ℤ)) := by
    intro e he e' he' hφ
    rw [Finset.mem_coe] at he he'
    obtain ⟨x, y, hxy, hxpos, hypos, heq, hφe⟩ :=
      schurEdges_interval_normal he
    obtain ⟨x', y', hxy', hxpos', hypos', heq', hφe'⟩ :=
      schurEdges_interval_normal he'
    dsimp only at hφ
    rw [hφe, hφe'] at hφ
    have hxmem : x ∈ ({x', y'} : Finset ℤ) :=
      hφ ▸ Finset.mem_insert_self _ _
    have hymem : y ∈ ({x', y'} : Finset ℤ) :=
      hφ ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    rw [Finset.mem_insert, Finset.mem_singleton] at hxmem hymem
    rcases hxmem with hxx | hxy'
    · rcases hymem with hyx | hyy
      · exact absurd (hxx.trans hyx.symm) hxy
      · rw [heq, heq', hxx, hyy]
    · rcases hymem with hyx | hyy
      · have hswap : ({x, y, x + y} : Finset ℤ) = {y, x, y + x} := by
          rw [add_comm y x]
          exact Finset.insert_comm x y _
        rw [heq, heq', hxy', hyx] at *
        exact hswap
      · exact absurd (hxy'.trans hyy.symm) hxy
  calc schurEdgeCount (interval n)
      ≤ ((interval n).powersetCard 2).card := by
        unfold schurEdgeCount
        exact Finset.card_le_card_of_injOn _ hmaps hinj
    _ = n.choose 2 := by
        rw [Finset.card_powersetCard, card_interval]
    _ ≤ n ^ 2 := by
        rw [Nat.choose_two_right]
        calc n * (n - 1) / 2 ≤ n * (n - 1) := Nat.div_le_self _ _
          _ ≤ n * n := Nat.mul_le_mul (le_refl n) (Nat.sub_le n 1)
          _ = n ^ 2 := by ring

/-! ## Round entries, bounded powersets, iteration -/

/-- Subsets of `A` of cardinality at most `b`. -/
def boundedPow (A : Finset ℤ) (b : ℕ) : Finset (Finset ℤ) :=
  A.powerset.filter fun s => s.card ≤ b

theorem mem_boundedPow {A s : Finset ℤ} {b : ℕ} :
    s ∈ boundedPow A b ↔ s ⊆ A ∧ s.card ≤ b := by
  rw [boundedPow, Finset.mem_filter, Finset.mem_powerset]

/-- For `A ⊆ interval n` and `1 ≤ b ≤ n`,
`(boundedPow A b).card ≤ (e·n/b)^b`. -/
theorem boundedPow_card_le_exp {n : ℕ} {A : Finset ℤ} {b : ℕ}
    (hA : A ⊆ interval n) (hb1 : 1 ≤ b) (hbn : b ≤ n) :
    ((boundedPow A b).card : ℝ) ≤ ((n : ℝ) * Real.exp 1 / b) ^ b := by
  have hAn : A.card ≤ n := by
    have h := Finset.card_le_card hA
    rwa [card_interval] at h
  have h1 : (boundedPow A b).card ≤
      ∑ i ∈ Finset.range (b + 1), A.card.choose i :=
    card_powerset_filter_card_le A b
  have h2 : (∑ i ∈ Finset.range (b + 1), (A.card.choose i : ℝ)) ≤
      ∑ i ∈ Finset.range (b + 1), (n.choose i : ℝ) := by
    apply Finset.sum_le_sum
    intro i _
    exact_mod_cast Nat.choose_le_choose i hAn
  have h3 := sum_choose_le_exp_mul_pow (N := n) (k := b) hb1 hbn
  calc ((boundedPow A b).card : ℝ)
      ≤ ∑ i ∈ Finset.range (b + 1), (A.card.choose i : ℝ) := by
        exact_mod_cast h1
    _ ≤ ∑ i ∈ Finset.range (b + 1), (n.choose i : ℝ) := h2
    _ ≤ ((n : ℝ) * Real.exp 1 / b) ^ b := h3

/-- The sampling probability used at level `j` when the current ambient set
has `eA` Schur edges: the smallest value allowed by `hpτ`. -/
noncomputable def pjOf (n : ℕ) (u : ℝ) (eA : ℕ) (j : ℕ) : ℝ :=
  Real.sqrt (120 * n / ((eA : ℝ) * u ^ j * (1 - u)))

/-- The identity round entry `(0, ∅, ∅, ∅)`. -/
def idEntry : RoundEntry := ((0 : Fin 3), ∅, ∅, ∅)

/-- The size conditions for a big-`e` round entry. -/
def validEntryCond (n : ℕ) (u : ℝ) (A : Finset ℤ)
    (e : Fin 3 × Finset ℤ × Finset ℤ × Finset ℤ) : Prop :=
  let j := (e.1 : ℕ)
  let pj := pjOf n u (schurEdgeCount A) j
  (e.2.1.card : ℝ) ≤ 4 * pj * (n : ℝ) ∧
  (e.2.2.1.card : ℝ) ≤ 4 * pj * (n : ℝ) ∧
  (e.2.2.2.card : ℝ) ≤
    2 * ((j : ℝ) + 1) * pj ^ 2 * schurEdgeCount A * u ^ (j + 1)

noncomputable instance decidableValidEntryCond (n : ℕ) (u : ℝ) (A : Finset ℤ) :
    DecidablePred (validEntryCond n u A) := by
  unfold validEntryCond
  infer_instance

/-- The entries admissible at ambient `A`: when `e(A)` is already at most
`δ' n²` only the identity is allowed; otherwise triples `(j, R, S', T)` of
subsets of `A` satisfying the size bounds from `one_round`. -/
noncomputable def validEntries (n : ℕ) (u δ' : ℝ) (B : ℕ)
    (A : Finset ℤ) : Finset RoundEntry :=
  if (schurEdgeCount A : ℝ) ≤ δ' * (n : ℝ) ^ 2 then {idEntry}
  else
    ((Finset.univ : Finset (Fin 3)) ×ˢ boundedPow A B ×ˢ
      boundedPow A B ×ˢ boundedPow A B).filter
      (validEntryCond n u A)

theorem idEntry_mem_validEntries {n : ℕ} {u δ' : ℝ} {B : ℕ}
    (hu0 : 0 < u) (A : Finset ℤ) :
    idEntry ∈ validEntries n u δ' B A := by
  rw [validEntries]
  split
  · exact Finset.mem_singleton_self _
  · rw [Finset.mem_filter, Finset.mem_product, Finset.mem_product,
      Finset.mem_product]
    have hpj : 0 ≤ pjOf n u (schurEdgeCount A) ((0 : Fin 3) : ℕ) :=
      Real.sqrt_nonneg _
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
    refine ⟨⟨Finset.mem_univ _, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
    · show (∅ : Finset ℤ) ∈ boundedPow A B
      rw [mem_boundedPow]
      exact ⟨Finset.empty_subset _, Nat.zero_le _⟩
    · show (∅ : Finset ℤ) ∈ boundedPow A B
      rw [mem_boundedPow]
      exact ⟨Finset.empty_subset _, Nat.zero_le _⟩
    · show (∅ : Finset ℤ) ∈ boundedPow A B
      rw [mem_boundedPow]
      exact ⟨Finset.empty_subset _, Nat.zero_le _⟩
    · show ((∅ : Finset ℤ).card : ℝ) ≤
          4 * pjOf n u (schurEdgeCount A) ((0 : Fin 3) : ℕ) * n
      rw [Finset.card_empty, Nat.cast_zero]
      exact mul_nonneg (mul_nonneg (by norm_num) hpj) hn
    · show ((∅ : Finset ℤ).card : ℝ) ≤
          4 * pjOf n u (schurEdgeCount A) ((0 : Fin 3) : ℕ) * n
      rw [Finset.card_empty, Nat.cast_zero]
      exact mul_nonneg (mul_nonneg (by norm_num) hpj) hn
    · show ((∅ : Finset ℤ).card : ℝ) ≤
          2 * (((0 : Fin 3) : ℕ) + 1 : ℝ) *
            pjOf n u (schurEdgeCount A) ((0 : Fin 3) : ℕ) ^ 2 *
            schurEdgeCount A * u ^ (((0 : Fin 3) : ℕ) + 1)
      rw [Finset.card_empty, Nat.cast_zero]
      refine mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
        (by norm_num) (by positivity)) (pow_nonneg hpj _))
        (Nat.cast_nonneg _)) (pow_nonneg hu0.le _)

/-- Entries preserve the ambient set: `applyEntry A e ⊆ A` and the edge
count does not increase. -/
theorem applyEntry_subset {A : Finset ℤ} {e : RoundEntry}
    (he : e ∈ ((Finset.univ : Finset (Fin 3)) ×ˢ
        A.powerset ×ˢ A.powerset ×ˢ A.powerset)) :
    applyEntry A e ⊆ A := by
  rw [Finset.mem_product, Finset.mem_product, Finset.mem_product,
    Finset.mem_powerset, Finset.mem_powerset, Finset.mem_powerset] at he
  unfold applyEntry roundContainer
  exact Finset.union_subset Finset.sdiff_subset he.2.2.2

theorem applyEntry_edgeCount_le {A : Finset ℤ} {e : RoundEntry}
    (he : e ∈ ((Finset.univ : Finset (Fin 3)) ×ˢ
        A.powerset ×ˢ A.powerset ×ˢ A.powerset)) :
    schurEdgeCount (applyEntry A e) ≤ schurEdgeCount A :=
  schurEdgeCount_mono (applyEntry_subset he)

/-- One step of the container iteration: apply every admissible entry to
every ambient set in `F`. -/
noncomputable def Fstep (n : ℕ) (u δ' : ℝ) (B : ℕ)
    (F : Finset (Finset ℤ)) : Finset (Finset ℤ) :=
  F.biUnion fun A => (validEntries n u δ' B A).image (applyEntry A)

/-- The `k`-fold iteration of `Fstep` starting from `{interval n}`. -/
noncomputable def Fiter (n : ℕ) (u δ' : ℝ) (B : ℕ) :
    ℕ → Finset (Finset ℤ)
  | 0 => {interval n}
  | k + 1 => Fstep n u δ' B (Fiter n u δ' B k)

theorem Fiter_subset_interval {n : ℕ} {u δ' : ℝ} {B : ℕ} (k : ℕ) :
    ∀ C ∈ Fiter n u δ' B k, C ⊆ interval n := by
  induction k with
  | zero =>
      intro C hC
      rw [Fiter, Finset.mem_singleton] at hC
      subst hC
      exact fun _ hx => hx
  | succ k ih =>
      intro C hC
      rw [Fiter, Fstep] at hC
      obtain ⟨A, hAF, hC'⟩ := Finset.mem_biUnion.mp hC
      obtain ⟨e, heE, rfl⟩ := Finset.mem_image.mp hC'
      have hsub : applyEntry A e ⊆ A := by
        apply applyEntry_subset
        rw [validEntries] at heE
        split at heE
        · rw [Finset.mem_singleton] at heE
          subst heE
          rw [Finset.mem_product, Finset.mem_product, Finset.mem_product]
          exact ⟨Finset.mem_univ _, Finset.mem_powerset.mpr
            (Finset.empty_subset _), Finset.mem_powerset.mpr
            (Finset.empty_subset _), Finset.mem_powerset.mpr
            (Finset.empty_subset _)⟩
        · rw [Finset.mem_filter] at heE
          obtain ⟨he1, -⟩ := heE
          rw [Finset.mem_product, Finset.mem_product,
            Finset.mem_product] at he1
          obtain ⟨hj, hR, hS, hT⟩ := he1
          rw [mem_boundedPow] at hR hS hT
          rw [Finset.mem_product, Finset.mem_product, Finset.mem_product]
          exact ⟨hj, Finset.mem_powerset.mpr hR.1,
            Finset.mem_powerset.mpr hS.1, Finset.mem_powerset.mpr hT.1⟩
      exact Finset.Subset.trans hsub (ih A hAF)

theorem pjOf_arg_pos {n : ℕ} {u : ℝ} {eA : ℕ} (heA : 0 < eA)
    (hn : 0 < n) (hu0 : 0 < u) (hu1 : u < 1) (j : ℕ) :
    0 < 120 * n / ((eA : ℝ) * u ^ j * (1 - u)) := by
  apply div_pos (by positivity)
  exact mul_pos (mul_pos (by exact_mod_cast heA) (pow_pos hu0 _))
    (by linarith)

theorem pjOf_sq {n : ℕ} {u : ℝ} {eA : ℕ} (heA : 0 < eA)
    (hu0 : 0 < u) (hu1 : u < 1) (j : ℕ) :
    (pjOf n u eA j) ^ 2 = 120 * n / ((eA : ℝ) * u ^ j * (1 - u)) := by
  rw [pjOf, Real.sq_sqrt (div_nonneg (by positivity)
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg _)
      (pow_nonneg hu0.le _)) (by linarith)))]

theorem pjOf_pos {n : ℕ} {u : ℝ} {eA : ℕ} (heA : 0 < eA)
    (hn : 0 < n) (hu0 : 0 < u) (hu1 : u < 1) (j : ℕ) :
    0 < pjOf n u eA j := by
  rw [pjOf, Real.sqrt_pos]
  exact pjOf_arg_pos heA hn hu0 hu1 j

theorem pjOf_le_one {n : ℕ} {u : ℝ} {eA : ℕ} (j : ℕ)
    (hd : 0 < (eA : ℝ) * u ^ j * (1 - u))
    (h : 120 * n ≤ (eA : ℝ) * u ^ j * (1 - u)) :
    pjOf n u eA j ≤ 1 := by
  rw [pjOf, Real.sqrt_le_iff]
  refine ⟨zero_le_one, ?_⟩
  rw [one_pow]
  exact (div_le_one hd).mpr h

/-- **Coverage by iteration.**  After `k` rounds, every sum-free
`I ⊆ interval n` is contained in some `C ∈ Fiter n u δ' B k` whose Schur
edge count is at most `max (δ' n²) ((29/30)^k n²)`. -/
theorem Fiter_covers {n : ℕ} {u δ' : ℝ} {B : ℕ} (k : ℕ)
    (hδ' : 0 < δ') (hu0 : 0 < u) (hu12 : u ≤ 1 / 2)
    (hn1 : 1 ≤ n)
    (hnu : 120 * (n : ℝ) ≤ δ' * (n : ℝ) ^ 2 * u ^ 2 * (1 - u))
    (hRB : 4 * Real.sqrt (120 * n / (δ' * u ^ 2 * (1 - u))) ≤ B)
    (hTB : 1440 * u * (n : ℝ) ≤ B)
    (I : Finset ℤ) (hI : I ⊆ interval n) (hIsf : IsSumFree I) :
    ∃ C ∈ Fiter n u δ' B k, I ⊆ C ∧
      (schurEdgeCount C : ℝ) ≤
        max (δ' * (n : ℝ) ^ 2) ((29 / 30) ^ k * (n : ℝ) ^ 2) := by
  have hu1 : u < 1 := by linarith
  induction k with
  | zero =>
      refine ⟨interval n, ?_, hI, ?_⟩
      · rw [Fiter]; exact Finset.mem_singleton_self _
      · rw [pow_zero, one_mul]
        have h : (schurEdgeCount (interval n) : ℝ) ≤ (n : ℝ) ^ 2 := by
          exact_mod_cast schurEdgeCount_interval_le n
        exact h.trans (le_max_right _ _)
  | succ k ih =>
      obtain ⟨C, hCF, hIC, heC⟩ := ih
      have hCsub : C ⊆ interval n := Fiter_subset_interval k C hCF
      have hCcard : C.card ≤ n := by
        have h := Finset.card_le_card hCsub
        rwa [card_interval] at h
      by_cases hsmall : (schurEdgeCount C : ℝ) ≤ δ' * (n : ℝ) ^ 2
      · refine ⟨C, ?_, hIC, hsmall.trans (le_max_left _ _)⟩
        rw [Fiter, Fstep, Finset.mem_biUnion]
        exact ⟨C, hCF, Finset.mem_image.mpr
          ⟨idEntry, idEntry_mem_validEntries hu0 C, applyEntry_id C⟩⟩
      · -- Big edge count: apply `one_round`.
        have heClt : δ' * (n : ℝ) ^ 2 < schurEdgeCount C := lt_of_not_ge hsmall
        have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
        have hCpos : ∀ x ∈ C, 0 < x := by
          intro x hx
          have hx' := hCsub hx
          rw [interval, Finset.mem_Icc] at hx'
          linarith [hx'.1]
        have heC0 : 0 < schurEdgeCount C := by
          have h : (0 : ℝ) < schurEdgeCount C :=
            lt_of_le_of_lt (by positivity) heClt
          exact_mod_cast h
        have hN : 0 < C.card := by
          obtain ⟨e, he⟩ := Finset.card_pos.mp heC0
          have h3 := schurEdge_card he
          have hle := Finset.card_le_card (schurEdges_subset he)
          omega
        have hden : ∀ j ≤ 2,
            0 < (schurEdgeCount C : ℝ) * u ^ j * (1 - u) := by
          intro j hj
          exact mul_pos (mul_pos (by exact_mod_cast heC0) (pow_pos hu0 _))
            (by linarith)
        -- The uniform per-level estimate `eC · u^j · (1-u) ≥ δ'n²u²(1-u)`.
        have hdd : ∀ j ≤ 2, δ' * (n : ℝ) ^ 2 * u ^ 2 * (1 - u) ≤
            (schurEdgeCount C : ℝ) * u ^ j * (1 - u) := by
          intro j hj
          have huj : u ^ 2 ≤ u ^ j :=
            pow_le_pow_of_le_one hu0.le (by linarith) hj
          have h1 : δ' * (n : ℝ) ^ 2 * u ^ 2 ≤
              schurEdgeCount C * u ^ j :=
            mul_le_mul heClt.le huj (pow_nonneg hu0.le _)
              (by positivity)
          exact mul_le_mul h1 (le_refl _) (by linarith)
            (mul_nonneg (by positivity) (pow_nonneg hu0.le _))
        have h120 : ∀ j ≤ 2, 120 * (n : ℝ) ≤
            (schurEdgeCount C : ℝ) * u ^ j * (1 - u) :=
          fun j hj => hnu.trans (hdd j hj)
        have hpτ : ∀ j, j ≤ 2 → 120 * (C.card : ℝ) ≤
            schurEdgeCount C * u ^ j * (1 - u) *
              (pjOf n u (schurEdgeCount C) j) ^ 2 := by
          intro j hj
          rw [pjOf_sq heC0 hu0 hu1, ← mul_div_assoc,
            mul_div_cancel_left₀ _ (hden j hj).ne']
          have h : (C.card : ℝ) ≤ n := by exact_mod_cast hCcard
          nlinarith [h]
        obtain ⟨j, hj2, R, S', T, hRC, hSC, hTC, hI2, hC2sub, heC2,
          hRb, hSb, hTb⟩ :=
          one_round hIC hIsf hCpos u hu0 hu1 heC0 hN
            (fun j => pjOf n u (schurEdgeCount C) j)
            (fun j hj => pjOf_pos heC0 hn1 hu0 hu1 j)
            (fun j hj => pjOf_le_one j (hden j hj) (h120 j hj))
            hpτ
        -- `4·pj·n ≤ √(...)` — used for the `R`, `S'` size bounds.
        have hpjbound : pjOf n u (schurEdgeCount C) j * (n : ℝ) ≤
            Real.sqrt (120 * n / (δ' * u ^ 2 * (1 - u))) := by
          have hd2 : (0 : ℝ) < δ' * n ^ 2 * u ^ 2 * (1 - u) := by
            apply mul_pos (mul_pos (mul_pos hδ' (by positivity))
              (pow_pos hu0 _))
            linarith
          have h1 : pjOf n u (schurEdgeCount C) j ≤
              Real.sqrt (120 * n / (δ' * n ^ 2 * u ^ 2 * (1 - u))) := by
            apply Real.sqrt_le_sqrt
            apply div_le_div₀ (by positivity) (le_refl _) hd2 (hdd j hj2)
          calc pjOf n u (schurEdgeCount C) j * n
              ≤ Real.sqrt (120 * n / (δ' * n ^ 2 * u ^ 2 * (1 - u))) * n :=
                mul_le_mul_of_nonneg_right h1 hnpos.le
            _ = Real.sqrt ((120 * n / (δ' * n ^ 2 * u ^ 2 * (1 - u))) *
                  (n : ℝ) ^ 2) := by
                rw [Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq hnpos.le]
            _ = Real.sqrt (120 * n / (δ' * u ^ 2 * (1 - u))) := by
                congr 1
                have hn2 : (n : ℝ) ^ 2 ≠ 0 := by positivity
                field_simp <;> ring
        -- The entry `(j, R, S', T)` is admissible at `C`.
        have hent : ((⟨j, by omega⟩ : Fin 3), R, S', T) ∈
            validEntries n u δ' B C := by
          rw [validEntries, if_neg hsmall, Finset.mem_filter,
            Finset.mem_product, Finset.mem_product, Finset.mem_product]
          have hRB' : (R.card : ℝ) ≤ (B : ℝ) := by
            calc (R.card : ℝ) ≤ 4 * pjOf n u (schurEdgeCount C) j * C.card :=
                  hRb
              _ ≤ 4 * pjOf n u (schurEdgeCount C) j * n :=
                  mul_le_mul_of_nonneg_left (by exact_mod_cast hCcard)
                    (mul_nonneg (by norm_num)
                      (pjOf_pos heC0 hn1 hu0 hu1 j).le)
              _ ≤ 4 * Real.sqrt (120 * n / (δ' * u ^ 2 * (1 - u))) := by
                  rw [show 4 * pjOf n u (schurEdgeCount C) j * n =
                      4 * (pjOf n u (schurEdgeCount C) j * n) by ring]
                  exact mul_le_mul_of_nonneg_left hpjbound (by norm_num)
              _ ≤ B := hRB
          have hSB' : (S'.card : ℝ) ≤ (B : ℝ) := by
            calc (S'.card : ℝ) ≤ 4 * pjOf n u (schurEdgeCount C) j * C.card :=
                  hSb
              _ ≤ 4 * pjOf n u (schurEdgeCount C) j * n :=
                  mul_le_mul_of_nonneg_left (by exact_mod_cast hCcard)
                    (mul_nonneg (by norm_num)
                      (pjOf_pos heC0 hn1 hu0 hu1 j).le)
              _ ≤ 4 * Real.sqrt (120 * n / (δ' * u ^ 2 * (1 - u))) := by
                  rw [show 4 * pjOf n u (schurEdgeCount C) j * n =
                      4 * (pjOf n u (schurEdgeCount C) j * n) by ring]
                  exact mul_le_mul_of_nonneg_left hpjbound (by norm_num)
              _ ≤ B := hRB
          have hTB' : (T.card : ℝ) ≤ (B : ℝ) := by
            have hpje : (pjOf n u (schurEdgeCount C) j) ^ 2 *
                (schurEdgeCount C : ℝ) =
                120 * n / (u ^ j * (1 - u)) := by
              have hd1 : (schurEdgeCount C : ℝ) ≠ 0 := by positivity
              have hd2 : u ^ j * (1 - u) ≠ 0 :=
                mul_ne_zero (pow_ne_zero _ hu0.ne') (by linarith)
              rw [pjOf_sq heC0 hu0 hu1]
              field_simp <;> ring
            calc (T.card : ℝ) ≤ 2 * (j + 1 : ℝ) *
                  (pjOf n u (schurEdgeCount C) j) ^ 2 *
                  schurEdgeCount C * u ^ (j + 1) := hTb
              _ = 2 * (j + 1 : ℝ) *
                  ((pjOf n u (schurEdgeCount C) j) ^ 2 *
                    schurEdgeCount C) * u ^ (j + 1) := by ring
              _ = 2 * (j + 1 : ℝ) * (120 * n / (u ^ j * (1 - u))) *
                  u ^ (j + 1) := by rw [hpje]
              _ = 2 * (j + 1 : ℝ) * 120 * n * u / (1 - u) := by
                  have hd2 : u ^ j * (1 - u) ≠ 0 :=
                    mul_ne_zero (pow_ne_zero _ hu0.ne') (by linarith)
                  have hd3 : (1 - u) ≠ 0 := by linarith
                  rw [pow_succ]
                  field_simp <;> ring
              _ ≤ 720 * n * u / (1 - u) := by
                  have h21 : 2 * (j + 1 : ℝ) ≤ 6 := by
                    have : (j : ℝ) ≤ 2 := by exact_mod_cast hj2
                    linarith
                  have hbase : (0 : ℝ) ≤ 120 * n * u / (1 - u) :=
                    div_nonneg (by positivity) (by linarith)
                  calc 2 * (j + 1 : ℝ) * 120 * n * u / (1 - u)
                      = 2 * (j + 1 : ℝ) * (120 * n * u / (1 - u)) := by ring
                    _ ≤ 6 * (120 * n * u / (1 - u)) :=
                        mul_le_mul_of_nonneg_right h21 hbase
                    _ = 720 * n * u / (1 - u) := by ring
              _ ≤ 1440 * u * n := by
                  rw [div_le_iff₀ (by linarith : (0 : ℝ) < 1 - u)]
                  have h720 : (0 : ℝ) ≤ 720 * u * n * (1 - 2 * u) :=
                    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
                      hu0.le) hnpos.le) (by linarith)
                  nlinarith [h720]
              _ ≤ B := hTB
          refine ⟨⟨Finset.mem_univ _, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
          · rw [mem_boundedPow]
            exact ⟨hRC, by exact_mod_cast hRB'⟩
          · rw [mem_boundedPow]
            exact ⟨hSC, by exact_mod_cast hSB'⟩
          · rw [mem_boundedPow]
            exact ⟨hTC, by exact_mod_cast hTB'⟩
          · show (R.card : ℝ) ≤ 4 * pjOf n u (schurEdgeCount C)
                ((⟨j, by omega⟩ : Fin 3) : ℕ) * n
            exact hRb.trans (mul_le_mul_of_nonneg_left
              (by exact_mod_cast hCcard)
              (mul_nonneg (by norm_num)
                (pjOf_pos heC0 hn1 hu0 hu1 j).le))
          · show (S'.card : ℝ) ≤ 4 * pjOf n u (schurEdgeCount C)
                ((⟨j, by omega⟩ : Fin 3) : ℕ) * n
            exact hSb.trans (mul_le_mul_of_nonneg_left
              (by exact_mod_cast hCcard)
              (mul_nonneg (by norm_num)
                (pjOf_pos heC0 hn1 hu0 hu1 j).le))
          · show (T.card : ℝ) ≤ 2 *
                (((⟨j, by omega⟩ : Fin 3) : ℕ) + 1 : ℝ) *
                (pjOf n u (schurEdgeCount C)
                  ((⟨j, by omega⟩ : Fin 3) : ℕ)) ^ 2 *
                schurEdgeCount C * u ^ (((⟨j, by omega⟩ : Fin 3) : ℕ) + 1)
            exact hTb
        -- Assemble the step.
        refine ⟨applyEntry C ((⟨j, by omega⟩ : Fin 3), R, S', T), ?_, hI2, ?_⟩
        · rw [Fiter, Fstep, Finset.mem_biUnion]
          exact ⟨C, hCF, Finset.mem_image.mpr ⟨(_, R, S', T), hent, rfl⟩⟩
        · have heCle : (schurEdgeCount C : ℝ) ≤
              (29 / 30) ^ k * (n : ℝ) ^ 2 := by
            rcases le_max_iff.mp heC with h | h
            · exact absurd h hsmall
            · exact h
          calc (schurEdgeCount (applyEntry C ((⟨j, by omega⟩ : Fin 3), R, S', T)) : ℝ)
              ≤ (29 / 30) * schurEdgeCount C := heC2
            _ ≤ (29 / 30) * ((29 / 30) ^ k * (n : ℝ) ^ 2) :=
                mul_le_mul_of_nonneg_left heCle (by norm_num)
            _ = (29 / 30) ^ (k + 1) * (n : ℝ) ^ 2 := by
                rw [pow_succ]; ring
            _ ≤ max (δ' * (n : ℝ) ^ 2)
                ((29 / 30) ^ (k + 1) * (n : ℝ) ^ 2) := le_max_right _ _

/-- Uniform bound on the number of admissible entries at any `A ⊆
interval n`: at most `3·(e·n/B)^{3B}`. -/
theorem validEntries_card_le {n : ℕ} {u δ' : ℝ} {B : ℕ} {A : Finset ℤ}
    (hA : A ⊆ interval n) (hb1 : 1 ≤ B) (hbn : B ≤ n) :
    ((validEntries n u δ' B A).card : ℝ) ≤
      3 * ((n : ℝ) * Real.exp 1 / B) ^ (3 * B) := by
  classical
  have hbpos : (0 : ℝ) < B := by exact_mod_cast hb1
  have hbase : (1 : ℝ) ≤ (n : ℝ) * Real.exp 1 / B := by
    rw [one_le_div hbpos]
    have hB : (B : ℝ) ≤ n := by exact_mod_cast hbn
    have he : (1 : ℝ) ≤ Real.exp 1 :=
      le_trans (by norm_num : (1:ℝ) ≤ 1 + 1) (Real.add_one_le_exp 1)
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    calc (B : ℝ) ≤ n * 1 := by rw [mul_one]; exact hB
      _ ≤ n * Real.exp 1 :=
          mul_le_mul_of_nonneg_left he hn
  rw [validEntries]
  split
  · rw [Finset.card_singleton, Nat.cast_one]
    have h2 : (1 : ℝ) ≤ ((n : ℝ) * Real.exp 1 / B) ^ B :=
      one_le_pow₀ hbase
    have h3 : ((n : ℝ) * Real.exp 1 / B) ^ B ≤
        ((n : ℝ) * Real.exp 1 / B) ^ (3 * B) :=
      pow_le_pow_right₀ hbase (by omega)
    have h4 : (0 : ℝ) ≤ ((n : ℝ) * Real.exp 1 / B) ^ (3 * B) :=
      pow_nonneg (zero_le_one.trans hbase) _
    nlinarith [h2, h3, h4]
  · have hcb := boundedPow_card_le_exp hA hb1 hbn
    have hcard : (((Finset.univ : Finset (Fin 3)) ×ˢ
        boundedPow A B ×ˢ boundedPow A B ×ˢ boundedPow A B).filter (validEntryCond n u A)).card
        ≤ 3 * (boundedPow A B).card ^ 3 := by
      calc (((Finset.univ : Finset (Fin 3)) ×ˢ
            boundedPow A B ×ˢ boundedPow A B ×ˢ boundedPow A B).filter (validEntryCond n u A)).card
          ≤ ((Finset.univ : Finset (Fin 3)) ×ˢ
              boundedPow A B ×ˢ boundedPow A B ×ˢ boundedPow A B).card :=
            Finset.card_filter_le _ _
        _ = 3 * (boundedPow A B).card ^ 3 := by
            rw [Finset.card_product, Finset.card_product,
              Finset.card_product, Finset.card_univ, Fintype.card_fin]
            ring
    have hcardR : ((((Finset.univ : Finset (Fin 3)) ×ˢ boundedPow A B ×ˢ
          boundedPow A B ×ˢ boundedPow A B).filter
        (validEntryCond n u A)).card : ℝ) ≤
          3 * ((boundedPow A B).card : ℝ) ^ 3 := by
      exact_mod_cast hcard
    calc ((((Finset.univ : Finset (Fin 3)) ×ˢ boundedPow A B ×ˢ
          boundedPow A B ×ˢ boundedPow A B).filter
          (validEntryCond n u A)).card : ℝ)
        ≤ 3 * ((boundedPow A B).card : ℝ) ^ 3 := hcardR
      _ ≤ 3 * (((n : ℝ) * Real.exp 1 / B) ^ B) ^ 3 :=
          mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (Nat.cast_nonneg _) hcb 3) (by norm_num)
      _ = 3 * ((n : ℝ) * Real.exp 1 / B) ^ (3 * B) := by
          rw [← pow_mul]
          ring_nf

/-- `(Fiter … k).card ≤ (3·(e·n/B)^{3B})^k`. -/
theorem Fiter_card_le {n : ℕ} {u δ' : ℝ} {B : ℕ} (hb1 : 1 ≤ B) (hbn : B ≤ n)
    (k : ℕ) :
    ((Fiter n u δ' B k).card : ℝ) ≤
      (3 * ((n : ℝ) * Real.exp 1 / B) ^ (3 * B)) ^ k := by
  set M := 3 * ((n : ℝ) * Real.exp 1 / B) ^ (3 * B) with hM
  have hM0 : (0 : ℝ) ≤ M :=
    mul_nonneg (by norm_num)
      (pow_nonneg (div_nonneg (mul_nonneg (Nat.cast_nonneg _)
        (Real.exp_pos 1).le) (by positivity)) _)
  induction k with
  | zero =>
      rw [Fiter, Finset.card_singleton, Nat.cast_one, pow_zero]
  | succ k ih =>
      have hbound : ∀ A ∈ Fiter n u δ' B k,
          (((validEntries n u δ' B A).image (applyEntry A)).card : ℝ) ≤
            M := by
        intro A hA
        have hAsub := Fiter_subset_interval k A hA
        calc (((validEntries n u δ' B A).image (applyEntry A)).card : ℝ)
            ≤ (validEntries n u δ' B A).card :=
              Nat.cast_le.mpr Finset.card_image_le
          _ ≤ M := validEntries_card_le hAsub hb1 hbn
      have hsum : ((Fstep n u δ' B (Fiter n u δ' B k)).card : ℝ) ≤
          (Fiter n u δ' B k).card * M := by
        calc ((Fstep n u δ' B (Fiter n u δ' B k)).card : ℝ)
            ≤ ∑ A ∈ Fiter n u δ' B k,
                (((validEntries n u δ' B A).image (applyEntry A)).card : ℝ) := by
              have h := Finset.card_biUnion_le
                (s := Fiter n u δ' B k)
                (t := fun A => (validEntries n u δ' B A).image (applyEntry A))
              unfold Fstep
              exact_mod_cast h
          _ ≤ ∑ _A ∈ Fiter n u δ' B k, M :=
              Finset.sum_le_sum fun A hA => hbound A hA
          _ = (Fiter n u δ' B k).card * M := by
              rw [Finset.sum_const, nsmul_eq_mul]
      calc ((Fiter n u δ' B (k + 1)).card : ℝ)
          ≤ (Fiter n u δ' B k).card * M := hsum
        _ ≤ M ^ k * M :=
            mul_le_mul_of_nonneg_right ih hM0
        _ = M ^ (k + 1) := by rw [pow_succ', mul_comm]


/-- `interval n` contains a strict Schur edge once `n ≥ 3`. -/
theorem schurEdgeCount_pos {n : ℕ} (hn : 3 ≤ n) :
    0 < schurEdgeCount (interval n) := by
  have he : ({1, 2, 3} : Finset ℤ) ∈ schurEdges (interval n) := by
    rw [mem_schurEdges]
    refine ⟨?_, by norm_num, 1, by decide, 2, by decide, by norm_num, ?_⟩
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rw [interval, Finset.mem_Icc]
      have hni : (3 : ℤ) ≤ n := by exact_mod_cast hn
      rcases hx with rfl | rfl | rfl <;> refine ⟨by norm_num, by omega⟩
    · show (1 : ℤ) + 2 ∈ ({1, 2, 3} : Finset ℤ)
      decide
  rw [schurEdgeCount]
  exact Finset.card_pos.mpr ⟨{1, 2, 3}, he⟩

/-- **The BMS/Saxton–Thomason container lemma for Schur triples.**
Assembled from: level selection (`st_level_exists`), the one-round trace
construction (`one_round`), iteration (`Fiter_covers`), the entry-count bound
(`Fiter_card_le`) and the strict-edge/ordered-triple bridge
(`schurTripleCount_le_edge_card`). -/
theorem containerExistence : ContainerExistence := by
  intro ε hε δ hδ
  -- Sparse-edge threshold: `9δ'n² + n ≤ δn²` eventually, and `δ' < 1`.
  set δ' := min (δ / 18) (1 / 2) with hδ'def
  have hδ' : 0 < δ' := lt_min (by linarith) (by norm_num)
  have hδ'le : δ' ≤ δ / 18 := min_le_left _ _
  have hδ'1 : δ' < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  -- Round count `K`, large enough that `(29/30)^K ≤ δ'`.
  set K := Nat.ceil (30 * Real.log δ'⁻¹) with hKdef
  have hKge : 30 * Real.log δ'⁻¹ ≤ (K : ℝ) := Nat.le_ceil _
  have hlogpos : 0 < 30 * Real.log δ'⁻¹ := by
    have hlog : Real.log δ' < 0 := Real.log_neg hδ' hδ'1
    rw [Real.log_inv]
    exact mul_pos (by norm_num) (neg_pos.mpr hlog)
  have hK1 : 1 ≤ K := by
    have h : (0 : ℝ) < K := lt_of_lt_of_le hlogpos hKge
    exact_mod_cast h
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK1
  have hpowK : (29 / 30 : ℝ) ^ K ≤ δ' := by
    have h1 : (29 / 30 : ℝ) ≤ Real.exp (-1 / 30) := by
      linarith [Real.add_one_le_exp (-1 / 30)]
    calc (29 / 30 : ℝ) ^ K ≤ (Real.exp (-1 / 30)) ^ K :=
          pow_le_pow_left₀ (by norm_num) h1 K
      _ = Real.exp ((K : ℝ) * (-1 / 30)) := by rw [← Real.exp_nat_mul]
      _ ≤ Real.exp (30 * Real.log δ'⁻¹ * (-1 / 30)) := by
          apply Real.exp_le_exp.mpr
          nlinarith [hKge]
      _ = δ' := by
          have heq : 30 * Real.log δ'⁻¹ * (-1 / 30) = Real.log δ' := by
            rw [Real.log_inv]; ring
          rw [heq, Real.exp_log hδ']
  -- Choose `u` small: `u·log₂(e/(3000u)) < ε/(18000K)` and `u < 1/3000`.
  have hε' : (0 : ℝ) < ε / (18000 * K) :=
    div_pos hε (mul_pos (by norm_num) hK0)
  obtain ⟨u, huL', hu0, huS⟩ : ∃ u : ℝ,
      u * Real.logb 2 ((Real.exp 1 / 3000) / u) < ε / (18000 * K) ∧
      0 < u ∧ u < 1 / 3000 := by
    have hT := tendsto_mul_logb_div_nhdsGT_zero
      (C := Real.exp 1 / 3000) (by positivity : (Real.exp 1 / 3000 : ℝ) ≠ 0)
    have h1 := hT.eventually (Iio_mem_nhds hε')
    have h2 : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), t < 1 / 3000 :=
      nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 3000))
    have h3 : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), 0 < t :=
      Filter.mem_of_superset self_mem_nhdsWithin
        (fun t (ht : t ∈ Set.Ioi (0 : ℝ)) => ht)
    obtain ⟨u, ⟨h1', h3'⟩, h2'⟩ := ((h1.and h3).and h2).exists
    exact ⟨u, h1', h3', h2'⟩
  have huL : u * Real.logb 2 (Real.exp 1 / (3000 * u)) < ε / (18000 * K) := by
    have heq : (Real.exp 1 / 3000) / u = Real.exp 1 / (3000 * u) := by
      rw [div_div]
    rwa [heq] at huL'
  have hu1 : u < 1 := by linarith
  set L := Real.logb 2 (Real.exp 1 / (3000 * u)) with hLdef
  have hLpos : 0 < L := by
    rw [hLdef]
    apply Real.logb_pos (by norm_num : (1 : ℝ) < 2)
    have he1 : (2 : ℝ) ≤ Real.exp 1 := by
      have h := Real.add_one_le_exp 1
      linarith [h]
    rw [lt_div_iff₀ (by positivity : (0 : ℝ) < 3000 * u)]
    nlinarith [he1, huS, hu0]
  -- For large `n` all hypotheses of `Fiter_covers` and the counting bound
  -- hold simultaneously.
  set N1 := Nat.ceil (240 / (δ' * u ^ 2)) with hN1
  set N2 := Nat.ceil (1 / (δ' * u ^ 4)) with hN2
  set N3 := Nat.ceil (2 / δ) with hN3
  set N4 := Nat.ceil (2 * (K : ℝ) * (2 + 3 * L) / ε) with hN4
  set N := max (max N1 N2) (max (max N3 N4) 3) with hN
  filter_upwards [Filter.eventually_ge_atTop N] with n hn
  have hnN1 : N1 ≤ n :=
    (le_max_left N1 N2).trans ((le_max_left _ _).trans hn)
  have hnN2 : N2 ≤ n :=
    (le_max_right N1 N2).trans ((le_max_left _ _).trans hn)
  have hnN3 : N3 ≤ n :=
    (le_max_left N3 N4).trans ((le_max_left _ _).trans
      ((le_max_right _ _).trans hn))
  have hnN4 : N4 ≤ n :=
    (le_max_right N3 N4).trans ((le_max_left _ _).trans
      ((le_max_right _ _).trans hn))
  have hn3 : 3 ≤ n :=
    (le_max_right _ 3).trans ((le_max_right _ _).trans hn)
  have hn1 : 1 ≤ n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  classical
  set B := Nat.ceil (3000 * u * (n : ℝ)) with hBdef
  have hBge : 3000 * u * n ≤ (B : ℝ) := Nat.le_ceil _
  have hBlt : (B : ℝ) < 3000 * u * n + 1 := Nat.ceil_lt_add_one (by positivity)
  have hBpos : (0 : ℝ) < B := by
    have : (0 : ℝ) < B := by
      rw [hBdef]
      exact_mod_cast (Nat.one_le_ceil_iff.mpr (by positivity :
        (0 : ℝ) < 3000 * u * n) : 1 ≤ Nat.ceil (3000 * u * n))
    exact this
  have hB1 : 1 ≤ B :=
    Nat.one_le_ceil_iff.mpr (by positivity : (0 : ℝ) < 3000 * u * n)
  have hBn : B ≤ n := by
    rw [hBdef, Nat.ceil_le]
    have : 3000 * u * (n : ℝ) < n := by
      have h : 3000 * u < 1 := by linarith [huS]
      calc 3000 * u * (n : ℝ) < 1 * n := mul_lt_mul_of_pos_right h hnpos
        _ = n := one_mul _
    exact this.le
  have hepos : 0 < schurEdgeCount (interval n) := schurEdgeCount_pos hn3
  have hcardpos : (0 : ℝ) < (interval n).card := by
    rw [card_interval]; positivity
  have hpos : ∀ x ∈ interval n, (0 : ℤ) < x := fun x hx => by
    rw [interval, Finset.mem_Icc] at hx
    exact zero_lt_one.trans_le hx.1
  -- `120n ≤ δ'n²u²(1-u)` since `n ≥ 240/(δ'u²)` and `1-u ≥ 1/2`.
  have hnu : 120 * (n : ℝ) ≤ δ' * (n : ℝ) ^ 2 * u ^ 2 * (1 - u) := by
    have hnN1r : (240 : ℝ) ≤ δ' * u ^ 2 * n := by
      have hN1c : (N1 : ℝ) ≤ n := by exact_mod_cast hnN1
      have h1 : (240 / (δ' * u ^ 2) : ℝ) ≤ n :=
        (Nat.le_ceil _).trans hN1c
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < δ' * u ^ 2)] at h1
      rwa [mul_comm] at h1
    have h1u : (1 : ℝ) / 2 ≤ 1 - u := by linarith
    have h2 : (240 : ℝ) * (n * (1 / 2)) ≤ (δ' * u ^ 2 * n) * (n * (1 - u)) :=
      mul_le_mul hnN1r (mul_le_mul_of_nonneg_left h1u hnpos.le)
        (by positivity) (by positivity)
    have h3 : δ' * (n : ℝ) ^ 2 * u ^ 2 * (1 - u) =
        (δ' * u ^ 2 * n) * (n * (1 - u)) := by ring
    rw [h3]
    calc 120 * (n : ℝ) = 240 * (n * (1 / 2)) := by ring
      _ ≤ (δ' * u ^ 2 * n) * (n * (1 - u)) := h2
  -- `4√(120n/(δ'u²(1-u))) ≤ B`: the root is at most `√(240n/(δ'u²))`,
  -- whose square is bounded using `n ≥ 1/(δ'u⁴)`.
  have hRB : 4 * Real.sqrt (120 * (n : ℝ) / (δ' * u ^ 2 * (1 - u))) ≤ B := by
    have h1u : (1 : ℝ) / 2 ≤ 1 - u := by linarith
    have hstep : 120 * (n : ℝ) / (δ' * u ^ 2 * (1 - u)) ≤
        240 * n / (δ' * u ^ 2) := by
      have hd : δ' * u ^ 2 / 2 ≤ δ' * u ^ 2 * (1 - u) := by
        have h := mul_le_mul_of_nonneg_left h1u
          (by positivity : (0 : ℝ) ≤ δ' * u ^ 2)
        linarith [h]
      have h := div_le_div₀ (by positivity : (0 : ℝ) ≤ 120 * n)
        (le_refl (120 * (n : ℝ)))
        (by positivity : (0 : ℝ) < δ' * u ^ 2 / 2) hd
      rwa [show 120 * (n : ℝ) / (δ' * u ^ 2 / 2) = 240 * n / (δ' * u ^ 2) by
        rw [div_div_eq_mul_div]; ring] at h
    have h2 : 4 * Real.sqrt (240 * (n : ℝ) / (δ' * u ^ 2)) ≤ 3000 * u * n := by
      have hsq : (4 * Real.sqrt (240 * (n : ℝ) / (δ' * u ^ 2))) ^ 2 ≤
          (3000 * u * n) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by positivity)]
        have hscale : (4 : ℝ) ^ 2 * (240 * n / (δ' * u ^ 2)) =
            (3840 * n) / (δ' * u ^ 2) := by ring
        rw [hscale, div_le_iff₀ (by positivity : (0 : ℝ) < δ' * u ^ 2)]
        have hN2c : (N2 : ℝ) ≤ n := by exact_mod_cast hnN2
        have hN2r : (1 / (δ' * u ^ 4) : ℝ) ≤ n :=
          (Nat.le_ceil _).trans hN2c
        have h1 : (1 : ℝ) ≤ δ' * u ^ 4 * n := by
          rw [div_le_iff₀ (by positivity : (0 : ℝ) < δ' * u ^ 4)] at hN2r
          rw [mul_comm] at hN2r
          exact hN2r
        have h3840 : (3840 : ℝ) * n ≤ 9000000 * δ' * u ^ 4 * n ^ 2 := by
          have h2 := mul_le_mul_of_nonneg_right h1 hnpos.le
          calc (3840 : ℝ) * n ≤ 9000000 * n :=
                mul_le_mul_of_nonneg_right (by norm_num) hnpos.le
            _ = 9000000 * (1 * n) := by ring
            _ ≤ 9000000 * (δ' * u ^ 4 * n * n) :=
                mul_le_mul_of_nonneg_left h2 (by norm_num)
            _ = 9000000 * δ' * u ^ 4 * n ^ 2 := by ring
        have heq : (3000 * u * n) ^ 2 * (δ' * u ^ 2) =
            9000000 * δ' * u ^ 4 * n ^ 2 := by ring
        rw [heq]
        exact h3840
      exact le_of_sq_le_sq hsq (by positivity)
    calc 4 * Real.sqrt (120 * (n : ℝ) / (δ' * u ^ 2 * (1 - u)))
        ≤ 4 * Real.sqrt (240 * (n : ℝ) / (δ' * u ^ 2)) :=
          mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hstep) (by norm_num)
      _ ≤ 3000 * u * n := h2
      _ ≤ B := hBge
  have hTB : 1440 * u * (n : ℝ) ≤ B := by
    calc 1440 * u * n ≤ 3000 * u * n :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (by norm_num : (1440 : ℝ) ≤ 3000)
              hu0.le) hnpos.le
      _ ≤ B := hBge
  -- The family: endpoints of length-`K` paths whose edge count is ≤ δ'n².
  -- Counting: `log₂ |Fiter K| ≤ K·(2 + 3B·L) ≤ εn`.
  have hMK : (3 * ((n : ℝ) * Real.exp 1 / (B : ℝ)) ^ (3 * B)) ^ K ≤
      (2 : ℝ) ^ (ε * n) := by
    have hbase : (n : ℝ) * Real.exp 1 / B ≤ Real.exp 1 / (3000 * u) := by
      rw [div_le_div_iff₀ hBpos (mul_pos (by norm_num) hu0)]
      have h := mul_le_mul_of_nonneg_left hBge (Real.exp_pos 1).le
      have heq : (n : ℝ) * Real.exp 1 * (3000 * u) =
          Real.exp 1 * (3000 * u * n) := by ring
      rwa [heq]
    have hlog : Real.logb 2 ((n : ℝ) * Real.exp 1 / B) ≤ L :=
      (Real.logb_le_logb (by norm_num : (1 : ℝ) < 2) (by positivity)
        (by positivity)).mpr hbase
    set M := 3 * ((n : ℝ) * Real.exp 1 / (B : ℝ)) ^ (3 * B) with hMeq
    have hMpos : (0 : ℝ) < M := by
      rw [hMeq]
      exact mul_pos (by norm_num)
        (pow_pos (div_pos (mul_pos hnpos (Real.exp_pos 1)) hBpos) _)
    have hlogM : Real.logb 2 M ≤ 2 + 3 * (B : ℝ) * L := by
      have hpow' : ((n : ℝ) * Real.exp 1 / (B : ℝ)) ^ (3 * B) ≠ 0 :=
        pow_ne_zero _ (ne_of_gt
          (div_pos (mul_pos hnpos (Real.exp_pos 1)) hBpos))
      have h3 : Real.logb 2 3 ≤ 2 := by
        have h := (Real.logb_le_logb (by norm_num : (1 : ℝ) < 2)
          (by norm_num : (0 : ℝ) < 3) (by norm_num : (0 : ℝ) < 4)).mpr
          (by norm_num : (3 : ℝ) ≤ 4)
        rwa [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.logb_pow,
          Real.logb_self_eq_one (b := 2) (by norm_num), mul_one] at h
      have hmul : 3 * (B : ℝ) * Real.logb 2 ((n : ℝ) * Real.exp 1 / B) ≤
          3 * B * L :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
      have heq1 : Real.logb 2 M =
          Real.logb 2 3 +
            Real.logb 2 (((n : ℝ) * Real.exp 1 / B) ^ (3 * B)) := by
        rw [hMeq, Real.logb_mul (by norm_num) hpow']
      have heq2 : Real.logb 2 (((n : ℝ) * Real.exp 1 / B) ^ (3 * B)) =
          (3 * B : ℝ) * Real.logb 2 ((n : ℝ) * Real.exp 1 / B) := by
        rw [Real.logb_pow]
        norm_cast
      rw [heq1, heq2]
      linarith [h3, hmul]
    have hKl : (K : ℝ) * Real.logb 2 M ≤ ε * n := by
      have hu1 : (K : ℝ) * (2 + 3 * L) ≤ ε * n / 2 := by
        have hN4c : (N4 : ℝ) ≤ n := by exact_mod_cast hnN4
        have hnN4r : 2 * (K : ℝ) * (2 + 3 * L) / ε ≤ n :=
          (Nat.le_ceil _).trans hN4c
        have h := (div_le_iff₀ hε).mp hnN4r
        have h2pos : (0 : ℝ) < 2 := by norm_num
        calc (K : ℝ) * (2 + 3 * L) = (2 * K * (2 + 3 * L)) / 2 := by ring
          _ ≤ (n * ε) / 2 := (div_le_div_iff_of_pos_right h2pos).mpr h
          _ = ε * n / 2 := by ring
      have hu2 : 9000 * u * n * L * K ≤ ε * n / 2 := by
        have h' : u * L * (K : ℝ) ≤ ε / 18000 := by
          have h : u * L * (18000 * K) < ε := by
            rwa [lt_div_iff₀ (mul_pos (by norm_num) hK0)] at huL
          have heq : u * L * (K : ℝ) * 18000 = u * L * (18000 * K) := by ring
          rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 18000), heq]
          exact h.le
        calc 9000 * u * n * L * K = n * (9000 * (u * L * K)) := by ring
          _ ≤ n * (9000 * (ε / 18000)) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left h' (by norm_num)) hnpos.le
          _ = ε * n / 2 := by ring
      calc (K : ℝ) * Real.logb 2 M
          ≤ K * (2 + 3 * (B : ℝ) * L) :=
            mul_le_mul_of_nonneg_left hlogM hK0.le
        _ ≤ K * (2 + 3 * (3000 * u * n + 1) * L) := by
            apply mul_le_mul_of_nonneg_left _ hK0.le
            have h1 : 3 * (B : ℝ) * L ≤ 3 * (3000 * u * n + 1) * L :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hBlt.le
                  (by norm_num : (0 : ℝ) ≤ 3)) hLpos.le
            linarith [h1]
        _ = K * (2 + 3 * L) + 9000 * u * n * L * K := by ring
        _ ≤ ε * n / 2 + ε * n / 2 := add_le_add hu1 hu2
        _ = ε * n := by ring
    calc M ^ K
        ≤ ((2 : ℝ) ^ (Real.logb 2 M)) ^ K := by
          apply pow_le_pow_left₀ hMpos.le _ K
          exact (Real.rpow_logb (b := 2) (by norm_num) (by norm_num) hMpos).ge
      _ = (2 : ℝ) ^ ((K : ℝ) * Real.logb 2 M) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
            mul_comm (Real.logb 2 M) (K : ℝ)]
      _ ≤ (2 : ℝ) ^ (ε * n) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hKl
  refine ⟨(Fiter n u δ' B K).filter
      (fun C => (schurEdgeCount C : ℝ) ≤ δ' * (n : ℝ) ^ 2), ?_, ?_, ?_⟩
  · refine ⟨fun C hC => ?_, fun I hI hIsf => ?_⟩
    · exact Fiter_subset_interval K C (Finset.mem_filter.mp hC).1
    · obtain ⟨C, hCF, hIC, heC⟩ := Fiter_covers K hδ' hu0
        (by linarith : u ≤ 1 / 2) hn1 hnu hRB hTB I hI hIsf
      have heC' : (schurEdgeCount C : ℝ) ≤ δ' * (n : ℝ) ^ 2 := by
        have h2 : (29 / 30 : ℝ) ^ K * n ^ 2 ≤ δ' * n ^ 2 :=
          mul_le_mul_of_nonneg_right hpowK (sq_nonneg _)
        exact heC.trans (max_le_iff.mpr ⟨le_refl _, h2⟩)
      exact ⟨C, Finset.mem_filter.mpr ⟨hCF, heC'⟩, hIC⟩
  · calc (((Fiter n u δ' B K).filter
          (fun C => (schurEdgeCount C : ℝ) ≤ δ' * (n : ℝ) ^ 2)).card : ℝ)
        ≤ (Fiter n u δ' B K).card := by
          exact_mod_cast Finset.card_filter_le _ _
      _ ≤ (3 * ((n : ℝ) * Real.exp 1 / (B : ℝ)) ^ (3 * B)) ^ K :=
        Fiter_card_le hB1 hBn K
      _ ≤ (2 : ℝ) ^ (ε * n) := hMK
  · intro C hC
    have hCF := (Finset.mem_filter.mp hC).1
    have heC := (Finset.mem_filter.mp hC).2
    have hCsub := Fiter_subset_interval K C hCF
    have h1 : (schurTripleCount C : ℝ) ≤ 9 * schurEdgeCount C + n := by
      exact_mod_cast schurTripleCount_le_edge_card hCsub
    have h2 : 9 * (δ' * (n : ℝ) ^ 2) + n ≤ δ * (n : ℝ) ^ 2 := by
      have h9 : 9 * δ' ≤ δ / 2 := by linarith [hδ'le]
      have hnδ : (2 : ℝ) ≤ δ * n := by
        have hN3c : (N3 : ℝ) ≤ n := by exact_mod_cast hnN3
        have hnN3r : (2 / δ : ℝ) ≤ n :=
          (Nat.le_ceil _).trans hN3c
        have h := (div_le_iff₀ hδ).mp hnN3r
        rwa [mul_comm] at h
      have h4 : 9 * δ' * (n : ℝ) ^ 2 ≤ δ / 2 * n ^ 2 :=
        mul_le_mul_of_nonneg_right h9 (sq_nonneg _)
      have h3 : (n : ℝ) ≤ δ * n ^ 2 / 2 := by
        have h5 : 2 * n ≤ δ * n * n :=
          mul_le_mul_of_nonneg_right hnδ hnpos.le
        have h2pos : (0 : ℝ) < 2 := by norm_num
        calc (n : ℝ) = 2 * n / 2 := by ring
          _ ≤ (δ * n * n) / 2 := (div_le_div_iff_of_pos_right h2pos).mpr h5
          _ = δ * n ^ 2 / 2 := by ring
      calc 9 * (δ' * (n : ℝ) ^ 2) + n = 9 * δ' * n ^ 2 + n := by ring
        _ ≤ δ / 2 * n ^ 2 + δ * n ^ 2 / 2 := add_le_add h4 h3
        _ = δ * (n : ℝ) ^ 2 := by ring
    calc (schurTripleCount C : ℝ) ≤ 9 * schurEdgeCount C + n := h1
      _ ≤ 9 * (δ' * (n : ℝ) ^ 2) + n :=
          add_le_add
            (mul_le_mul_of_nonneg_left heC (by norm_num : (0 : ℝ) ≤ 9))
            (le_refl _)
      _ ≤ δ * (n : ℝ) ^ 2 := h2

/-- **BLST18 modulo removal + DFST only.**  With the container lemma
discharged unconditionally (`containerExistence`), the sharp asymptotic
needs only the two remaining cited theorems: Green's arithmetic removal
lemma and the Deshouillers–Freiman–Sós–Temkin trichotomy. -/
theorem sharpAsymptotic_of_removal_dfst
    (hSR : SchurRemoval) (hDFST : DFST) : SharpAsymptotic :=
  sharpAsymptotic_of_containerExistence_removal_dfst
    containerExistence hSR hDFST

/-- The `EventualRatioUpper` form of the same conditional headline. -/
theorem eventualRatioUpper_quarter_of_removal_dfst
    (hSR : SchurRemoval) (hDFST : DFST) : EventualRatioUpper (1 / 4) :=
  sharpAsymptotic_iff_eventualRatioUpper.mp
    (sharpAsymptotic_of_removal_dfst hSR hDFST)
