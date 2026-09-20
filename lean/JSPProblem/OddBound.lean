import JSPProblem.Trichotomy
import JSPProblem.OddLink
import JSPProblem.AlmostTF
import JSPProblem.Sapozhenko
import JSPProblem.MaxCard
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# JSP-000728 — closing the `OddContainerBound` hypothesis (BLST Lemma 3.4)

For a sum-free fingerprint `S ⊆ {1,…,n}` consisting entirely of *even*
numbers, the link graph `L_S[odds n]` has at most `2^{(1/4 + ε)n}` maximal
independent sets, eventually.  The proof is the `n^{1/4}` threshold split:

* **Sparse case** (`|S|^4 ≤ n`): `L_S[odds n]` has at most `24·|S|³`
  triangles (`triangles_le_mul_card_pow`), and deleting the
  `T = triVerts` set (`|T| ≤ 72·|S|³ ≤ 72·n^{3/4} = o(n)`) leaves a
  triangle-free graph.  The almost-triangle-free bound
  (`card_linkMaxSets_le_two_pow_mul_two_rpow_sdiff`, BLST Lemma 2.6) gives
  `|linkMaxSets| ≤ 2^{|T|} · 2^{|O∖T|/2} ≤ 2^{εn/2} · 2^{(n+1)/4}
  ≤ 2^{(1/4 + ε)n}`.
* **Dense case** (`n < |S|^4`): every `x ∈ odds n` has link-degree in
  `[|S|/2, 2|S| + 2]` (`deg_lo_le`, `deg_le_two_mul_add`), so `L_S[O]` is
  almost regular with ratio `≤ 5` once `|S| ≥ 4`.  Sapozhenko's
  almost-regular MIS bound
  (`exists_misCount_le_three_rpow_of_almostRegular` with `k = 5`) gives
  `misCount ≤ 3^{(5/6 + ε)·|O|/3} ≤ 2^{(8/5)·(5/6 + ε)·(n+1)/6}
  ≤ 2^{(1/4 + ε)n}`.

The arithmetic uses only `log₂ 3 ≤ 8/5` (`3^5 = 243 ≤ 256 = 2^8`) and the
cardinality `(odds n).card = (n + 1)/2` (`card_odds`).
-/

namespace JSP000728

/-- `3 ≤ 2^{8/5}` (equivalently `log₂ 3 ≤ 8/5`), via `3^5 = 243 ≤ 256 = 2^8`. -/
private theorem three_le_two_rpow_eight_fifths :
    (3 : ℝ) ≤ (2 : ℝ) ^ ((8 : ℝ) / 5) := by
  have e : ((2 : ℝ) ^ ((8 : ℝ) / 5)) ^ 5 = 256 := by
    have e' : ((2 : ℝ) ^ ((8 : ℝ) / 5)) ^ 5 = (2 : ℝ) ^ ((8 : ℕ) : ℝ) := by
      rw [← Real.rpow_natCast _ 5, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      norm_num
    rw [e', Real.rpow_natCast]
    norm_num
  refine le_of_pow_le_pow_left₀ (by norm_num : (5 : ℕ) ≠ 0)
    (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _) ?_
  rw [e]
  norm_num

/-- `3^t ≤ 2^{8t/5}` for `t ≥ 0`. -/
private theorem three_rpow_le_two_rpow_eight_fifths (t : ℝ) (ht : 0 ≤ t) :
    (3 : ℝ) ^ t ≤ (2 : ℝ) ^ ((8 / 5 : ℝ) * t) := by
  have h1 : (3 : ℝ) ^ t ≤ ((2 : ℝ) ^ ((8 : ℝ) / 5)) ^ t :=
    Real.rpow_le_rpow (by norm_num) three_le_two_rpow_eight_fifths ht
  have h2 : ((2 : ℝ) ^ ((8 : ℝ) / 5)) ^ t = (2 : ℝ) ^ ((8 / 5 : ℝ) * t) := by
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  exact h1.trans_eq h2

/-- **BLST Lemma 3.4, proved.**  For every `ε > 0`, eventually every
sum-free fingerprint `S ⊆ {1,…,n}` of even numbers has at most
`2^{(1/4 + ε)n}` maximal link-independent subsets of `odds n`. -/
theorem oddContainerBound : OddContainerBound := by
  intro ε hε
  -- Sapozhenko bound with `k = 5`, tuned to `ε`.
  obtain ⟨δ₀, hsap⟩ := exists_misCount_le_three_rpow_of_almostRegular
    (k := 5) (ε := ε) (by norm_num) hε
  filter_upwards [Filter.eventually_ge_atTop 256,
    Filter.eventually_ge_atTop ⌈(2 * δ₀) ^ 4⌉₊,
    Filter.eventually_ge_atTop ⌈(144 / ε) ^ 4⌉₊,
    Filter.eventually_ge_atTop ⌈1 / (2 * ε)⌉₊]
    with n hn256 hnδ₀ hn144 hn2ε
  intro S hSI hSf hmod
  have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hε2 : (0 : ℝ) < ε / 2 := by linarith
  have hpos : ∀ s ∈ S, 0 < s := fun s hs =>
    (Finset.mem_Icc.mp (hSI hs)).1
  have hEven : ∀ s ∈ S, Even s := fun s hs =>
    Int.even_iff.mpr (hmod s hs)
  -- real-valued threshold hypotheses
  have hnδ₀R : (2 * δ₀) ^ 4 ≤ (n : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hnδ₀)
  have hn144R : (144 / ε) ^ 4 ≤ (n : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hn144)
  have hn2εR : (1 : ℝ) / (2 * ε) ≤ (n : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hn2ε)
  have hquarter : (1 : ℝ) / 4 ≤ ε * (n : ℝ) / 2 := by
    have h1 : (1 : ℝ) ≤ (n : ℝ) * (2 * ε) := by
      rwa [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * ε)] at hn2εR
    nlinarith [hε]
  -- the `n^{1/4}` split, phrased on naturals
  rcases le_or_gt (S.card ^ 4) n with hsm | hbig
  · /- Sparse case: `|S|^4 ≤ n`, so `72·|S|³ ≤ εn/2` and deleting the
      triangle vertices leaves a triangle-free graph. -/
    obtain ⟨T, hTO, hTcard, hTtri⟩ :=
      exists_triangleFree_sdiff_odds (n := n) hSf hpos le_rfl
    have hbound := card_linkMaxSets_le_two_pow_mul_two_rpow_sdiff
      (S := S) (B := odds n) (T := T) hTO hTtri
    have hs4 : (S.card : ℝ) ^ 4 ≤ (n : ℝ) := by exact_mod_cast hsm
    have hTR : (T.card : ℝ) ≤ 72 * (S.card : ℝ) ^ 3 := by
      exact_mod_cast hTcard
    have hs3 : 72 * (S.card : ℝ) ^ 3 ≤ ε * (n : ℝ) / 2 := by
      rcases le_or_gt (S.card : ℝ) (144 / ε) with hsc | hsc
      · -- bounded `|S|`: `72·|S|³ ≤ 72·(144/ε)³ = (ε/2)·(144/ε)^4 ≤ εn/2`.
        have h1 : (S.card : ℝ) ^ 3 ≤ (144 / ε) ^ 3 :=
          pow_le_pow_left₀ (Nat.cast_nonneg _) hsc 3
        have h2 : 72 * (144 / ε) ^ 3 = (ε / 2) * (144 / ε) ^ 4 := by
          have hεne : ε ≠ 0 := hε.ne'
          field_simp
          ring
        calc 72 * (S.card : ℝ) ^ 3
            ≤ 72 * (144 / ε) ^ 3 :=
              mul_le_mul_of_nonneg_left h1 (by norm_num)
          _ = (ε / 2) * (144 / ε) ^ 4 := h2
          _ ≤ (ε / 2) * (n : ℝ) :=
              mul_le_mul_of_nonneg_left hn144R hε2.le
          _ = ε * (n : ℝ) / 2 := by ring
      · -- `|S| > 144/ε`: `72·|S|³ ≤ (ε/2)·|S|^4 ≤ εn/2`.
        have h144 : (144 : ℝ) ≤ ε * (S.card : ℝ) := by
          rw [div_lt_iff₀ hε] at hsc
          rw [mul_comm]
          exact hsc.le
        have h72 : (72 : ℝ) ≤ (ε / 2) * (S.card : ℝ) := by linarith [h144]
        calc 72 * (S.card : ℝ) ^ 3
            ≤ ((ε / 2) * (S.card : ℝ)) * (S.card : ℝ) ^ 3 :=
              mul_le_mul_of_nonneg_right h72
                (pow_nonneg (Nat.cast_nonneg _) _)
          _ = (ε / 2) * (S.card : ℝ) ^ 4 := by ring
          _ ≤ (ε / 2) * (n : ℝ) :=
              mul_le_mul_of_nonneg_left hs4 hε2.le
          _ = ε * (n : ℝ) / 2 := by ring
    have hTbound : (2 : ℝ) ^ T.card ≤ (2 : ℝ) ^ (ε * (n : ℝ) / 2) := by
      rw [← Real.rpow_natCast (2 : ℝ) T.card]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (hTR.trans hs3)
    have hOT : ((odds n \ T).card : ℝ) ≤ ((n : ℝ) + 1) / 2 := by
      have h1 : (odds n \ T).card ≤ (odds n).card :=
        Finset.card_le_card Finset.sdiff_subset
      rw [card_odds n] at h1
      calc ((odds n \ T).card : ℝ)
          ≤ (((n + 1) / 2 : ℕ) : ℝ) := by exact_mod_cast h1
        _ ≤ ((n : ℝ) + 1) / 2 := by
            calc (((n + 1) / 2 : ℕ) : ℝ)
                ≤ (((n + 1 : ℕ)) : ℝ) / 2 := Nat.cast_div_le
              _ = ((n : ℝ) + 1) / 2 := by norm_cast
    have hOTbound : (2 : ℝ) ^ (((odds n \ T).card : ℝ) / 2) ≤
        (2 : ℝ) ^ (((n : ℝ) + 1) / 4) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith [hOT])
    calc ((linkMaxSets S (odds n)).card : ℝ)
        ≤ (2 : ℝ) ^ T.card * (2 : ℝ) ^ (((odds n \ T).card : ℝ) / 2) :=
          hbound
      _ ≤ (2 : ℝ) ^ (ε * (n : ℝ) / 2) * (2 : ℝ) ^ (((n : ℝ) + 1) / 4) :=
          mul_le_mul hTbound hOTbound
            (Real.rpow_nonneg (by norm_num) _)
            (Real.rpow_nonneg (by norm_num) _)
      _ = (2 : ℝ) ^ (ε * (n : ℝ) / 2 + ((n : ℝ) + 1) / 4) := by
          rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      _ ≤ (2 : ℝ) ^ ((1 / 4 + ε) * (n : ℝ)) := by
          refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
          linarith [hquarter]
  · /- Dense case: `n < |S|^4`, so `|S| ≥ 4` and `|S|/2 ≥ δ₀` for `n` large;
      degrees lie in `[|S|/2, 2|S|+2] ⊆ [|S|/2, 5·(|S|/2)]`, and the
      almost-regular Sapozhenko bound applies on `B = odds n` directly
      (looped vertices are simply never selected). -/
    have hs4R : (n : ℝ) < (S.card : ℝ) ^ 4 := by exact_mod_cast hbig
    have hsge4 : (4 : ℝ) ≤ (S.card : ℝ) := by
      rcases lt_or_ge S.card 4 with hslt | hsge
      · exfalso
        have h81 : S.card ^ 4 ≤ 81 := by
          calc S.card ^ 4 ≤ 3 ^ 4 := Nat.pow_le_pow_left (by omega) 4
            _ = 81 := by norm_num
        omega
      · exact_mod_cast hsge
    have hδle : δ₀ ≤ (S.card : ℝ) / 2 := by
      rcases le_or_gt δ₀ 0 with hδ | hδ
      · exact hδ.trans (by positivity)
      · by_contra hnot
        push Not at hnot
        have hsle : (S.card : ℝ) ≤ 2 * δ₀ := by linarith [hnot.le]
        have h4 : (S.card : ℝ) ^ 4 ≤ (2 * δ₀) ^ 4 :=
          pow_le_pow_left₀ (Nat.cast_nonneg _) hsle 4
        linarith [hs4R, hnδ₀R]
    have hlo : ∀ v ∈ odds n,
        (S.card : ℝ) / 2 ≤ (degIn (linkAdj S) (odds n) v : ℝ) := by
      intro v hv
      have h := deg_lo_le hv hSI hEven
      have h' : (S.card : ℝ) ≤
          2 * ((linkNbrs S (odds n) v).card : ℝ) := by
        exact_mod_cast h
      have hdegid : degIn (linkAdj S) (odds n) v =
          (linkNbrs S (odds n) v).card := rfl
      rw [hdegid]
      linarith [h']
    have hhi : ∀ v ∈ odds n,
        (degIn (linkAdj S) (odds n) v : ℝ) ≤ 5 * ((S.card : ℝ) / 2) := by
      intro v hv
      have h := deg_le_two_mul_add (S := S) hv
      have h' : ((linkNbrs S (odds n) v).card : ℝ) ≤
          2 * (S.card : ℝ) + 2 := by
        exact_mod_cast h
      have hdegid : degIn (linkAdj S) (odds n) v =
          (linkNbrs S (odds n) v).card := rfl
      rw [hdegid]
      linarith [h', hsge4]
    have hmis := hsap (linkAdj S) (linkLoop S)
      (fun x y h => linkAdj_comm.mp h) (odds n) ((S.card : ℝ) / 2)
      hδle hlo hhi
    simp only [misCount, maxIndepSets_link] at hmis
    have hOcard : ((odds n).card : ℝ) ≤ ((n : ℝ) + 1) / 2 := by
      rw [card_odds n]
      calc (((n + 1) / 2 : ℕ) : ℝ)
          ≤ (((n + 1 : ℕ)) : ℝ) / 2 := Nat.cast_div_le
        _ = ((n : ℝ) + 1) / 2 := by norm_cast
    have hn8 : (8 : ℝ) ≤ (n : ℝ) := by
      have h : (8 : ℕ) ≤ n := by omega
      exact_mod_cast h
    have h1 : (2 / 9 : ℝ) * ((n : ℝ) + 1) ≤ (n : ℝ) / 4 := by linarith
    have h2 : (4 * ε / 15 : ℝ) * ((n : ℝ) + 1) ≤ ε * (n : ℝ) := by
      have h4 : ε * 4 ≤ ε * (11 * (n : ℝ)) :=
        mul_le_mul_of_nonneg_left (by linarith) hε.le
      linarith [h4]
    calc ((linkMaxSets S (odds n)).card : ℝ)
        ≤ (3 : ℝ) ^ ((5 / (5 + 1) + ε) * ((odds n).card : ℝ) / 3) := hmis
      _ ≤ (3 : ℝ) ^ ((5 / (5 + 1) + ε) * (((n : ℝ) + 1) / 2) / 3) := by
          refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
          have hc : (0 : ℝ) ≤ 5 / (5 + 1) + ε := by positivity
          linarith [mul_le_mul_of_nonneg_left hOcard hc]
      _ ≤ (2 : ℝ) ^ ((8 / 5) * ((5 / (5 + 1) + ε) *
            (((n : ℝ) + 1) / 2) / 3)) :=
          three_rpow_le_two_rpow_eight_fifths _ (by positivity)
      _ ≤ (2 : ℝ) ^ ((1 / 4 + ε) * (n : ℝ)) := by
          refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
          have hk56 : (5 : ℝ) / (5 + 1) = 5 / 6 := by norm_num
          rw [hk56]
          have hexp : (8 / 5 : ℝ) * ((5 / 6 + ε) * (((n : ℝ) + 1) / 2) / 3) =
              (2 / 9) * ((n : ℝ) + 1) + (4 * ε / 15) * ((n : ℝ) + 1) := by
            ring
          rw [hexp]
          calc (2 / 9 : ℝ) * ((n : ℝ) + 1) + (4 * ε / 15) * ((n : ℝ) + 1)
              ≤ (n : ℝ) / 4 + ε * (n : ℝ) := add_le_add h1 h2
            _ = (1 / 4 + ε) * (n : ℝ) := by ring

end JSP000728
