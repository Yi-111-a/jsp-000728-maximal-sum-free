import JSPProblem.HujterTuza
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

/-!
# JSP-000728 — BLST Lemma 2.6: the almost-triangle-free MIS bound

If a graph on `B` becomes triangle-free after deleting a set `T` of
vertices, the number of maximal independent sets is at most
`2^{|T|} · 2^{|B ∖ T|/2} = 2^{(|B| + |T|)/2}`.

**Encoding.**  A maximal independent set `I` of `B` is encoded by the
pair `(S', J)` where `S' = I ∩ T` is an arbitrary subset of `T`
(≤ `2^{|T|}` choices) and `J = I ∖ T` is a maximal independent subset of
the *reduced* vertex set `redSet adj B T S' = (B ∖ T) ∖ N(S')`: every
`x ∈ (B ∖ T) ∖ N(S')` outside `J` is dominated in `B`, and its dominator
cannot lie in `S'` (that would put `x ∈ N(S')`), so it lies in `J`.
Since `redSet adj B T S' ⊆ B ∖ T` is triangle-free, the Hujter–Tuza bound
`misCount ≤ 2^{|B ∖ T|/2}` applies to each fibre, and the fibres cover:

* `maxIndepSets_subset_redSet_cover` — the covering statement;
* `misCount_le_two_pow_mul_two_rpow_sdiff` — the `2^{|T|}·2^{|B∖T|/2}`
  bound;
* `misCount_le_two_rpow_card_add` — the combined `2^{(|B|+|T|)/2}` form;
* `card_linkMaxSets_le_two_pow_mul_two_rpow_sdiff` — transfer to the
  link graph `linkMaxSets`.
-/

namespace JSP000728

/-- The *reduced* vertex set after committing to the in-`T` part `S'`:
the vertices of `B ∖ T` with no `adj`-edge into `S'`.  If `I` is a
maximal independent subset of `B` with `I ∩ T = S'`, then `I ∖ T` is a
maximal independent subset of `redSet adj B T S'`. -/
def redSet (adj : ℤ → ℤ → Prop) [DecidableRel adj] (B T S' : Finset ℤ) :
    Finset ℤ :=
  (B \ T).filter fun x => ∀ s ∈ S', ¬ adj x s

/-- **Covering by the in-`T` part.**  Every maximal independent subset `t`
of `B` is the union `S' ∪ j` of a subset `S' ⊆ T` (namely `t ∩ T`) and a
maximal independent subset `j` of the reduced set `redSet adj B T S'`
(namely `t ∖ T`). -/
theorem maxIndepSets_subset_redSet_cover {adj : ℤ → ℤ → Prop}
    {loop : ℤ → Prop} [DecidableRel adj] [DecidablePred loop]
    {B T : Finset ℤ} (_hT : T ⊆ B) :
    maxIndepSets adj loop B ⊆
      T.powerset.biUnion fun S' =>
        (maxIndepSets adj loop (redSet adj B T S')).image (S' ∪ ·) := by
  intro t ht
  rw [mem_maxIndepSets] at ht
  obtain ⟨htB, hti, htm⟩ := ht
  rw [Finset.mem_biUnion]
  refine ⟨t ∩ T, Finset.mem_powerset.mpr Finset.inter_subset_right, ?_⟩
  rw [Finset.mem_image]
  refine ⟨t \ T, ?_, ?_⟩
  · rw [mem_maxIndepSets]
    refine ⟨?_, ⟨?_, ?_⟩, ?_⟩
    · -- `t ∖ T ⊆ redSet`: an element of `t` has no edge into `t ∩ T`.
      intro y hy
      obtain ⟨hyt, hyT⟩ := Finset.mem_sdiff.mp hy
      rw [redSet, Finset.mem_filter, Finset.mem_sdiff]
      refine ⟨⟨htB hyt, hyT⟩, fun s hs hadj => ?_⟩
      exact hti.2 y hyt s (Finset.mem_inter.mp hs).1 hadj
    · intro x hx
      exact hti.1 x (Finset.sdiff_subset hx)
    · intro x hx y hy
      exact hti.2 x (Finset.sdiff_subset hx) y
        (Finset.sdiff_subset hy)
    · -- maximality: `x ∈ redSet`, `x ∉ t ∖ T`.  Its `B`-dominator cannot
      -- lie in `t ∩ T` (that would exclude `x` from `redSet`), so it is
      -- in `t ∖ T`.
      intro x hx hxt
      rw [redSet, Finset.mem_filter, Finset.mem_sdiff] at hx
      obtain ⟨⟨hxB, hxT⟩, hxno⟩ := hx
      have hxnt : x ∉ t :=
        fun hxm => hxt (Finset.mem_sdiff.mpr ⟨hxm, hxT⟩)
      rcases htm x hxB hxnt with hl | ⟨y, hyt, hyadj⟩
      · exact Or.inl hl
      · refine Or.inr ⟨y, Finset.mem_sdiff.mpr ⟨hyt, fun hyT => ?_⟩, hyadj⟩
        exact hxno y (Finset.mem_inter.mpr ⟨hyt, hyT⟩) hyadj
  · -- `t = (t ∩ T) ∪ (t ∖ T)`.
    rw [Finset.union_comm, Finset.sdiff_union_inter]

/-- **BLST Lemma 2.6 (factored form).**  If `T ⊆ B` and the induced graph
on `B ∖ T` is triangle-free, then
`misCount adj loop B ≤ 2^{|T|} · 2^{|B ∖ T|/2}`. -/
theorem misCount_le_two_pow_mul_two_rpow_sdiff {adj : ℤ → ℤ → Prop}
    {loop : ℤ → Prop} [DecidableRel adj] [DecidablePred loop]
    (hsymm : ∀ x y, adj x y → adj y x)
    {B T : Finset ℤ} (hT : T ⊆ B) (htri : triangleFree adj (B \ T)) :
    (misCount adj loop B : ℝ) ≤
      2 ^ T.card * (2 : ℝ) ^ (((B \ T).card : ℝ) / 2) := by
  have cover := maxIndepSets_subset_redSet_cover
    (adj := adj) (loop := loop) (B := B) (T := T) hT
  -- the covering bound, cast to `ℝ`.
  have hcard : (misCount adj loop B : ℝ) ≤
      ∑ S' ∈ T.powerset,
        (misCount adj loop (redSet adj B T S') : ℝ) := by
    have h2 : (maxIndepSets adj loop B).card ≤
        ∑ S' ∈ T.powerset,
          ((maxIndepSets adj loop (redSet adj B T S')).image
            (S' ∪ ·)).card :=
      le_trans (Finset.card_le_card cover) Finset.card_biUnion_le
    have h3 : ∑ S' ∈ T.powerset,
          ((maxIndepSets adj loop (redSet adj B T S')).image
            (S' ∪ ·)).card ≤
        ∑ S' ∈ T.powerset,
          (maxIndepSets adj loop (redSet adj B T S')).card :=
      Finset.sum_le_sum fun S' _ => Finset.card_image_le
    simp only [misCount]
    exact_mod_cast le_trans h2 h3
  -- each fibre: `redSet ⊆ B ∖ T` is triangle-free, so Hujter–Tuza applies.
  have hterm : ∀ S' ∈ T.powerset,
      (misCount adj loop (redSet adj B T S') : ℝ) ≤
        (2 : ℝ) ^ (((B \ T).card : ℝ) / 2) := by
    intro S' _
    have hsub : redSet adj B T S' ⊆ B \ T := Finset.filter_subset _ _
    have hle : (misCount adj loop (redSet adj B T S') : ℝ) ≤
        (2 : ℝ) ^ (((redSet adj B T S').card : ℝ) / 2) :=
      misCount_le_two_rpow_of_triangleFree adj loop hsymm _ _ le_rfl
        (htri.mono hsub)
    refine le_trans hle (Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 2) ?_)
    have hcardle : ((redSet adj B T S').card : ℝ) ≤ ((B \ T).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    linarith
  calc (misCount adj loop B : ℝ)
      ≤ ∑ S' ∈ T.powerset,
          (misCount adj loop (redSet adj B T S') : ℝ) := hcard
    _ ≤ ∑ _S' ∈ T.powerset,
          (2 : ℝ) ^ (((B \ T).card : ℝ) / 2) :=
        Finset.sum_le_sum fun S' hS' => hterm S' hS'
    _ = (T.powerset.card : ℝ) * (2 : ℝ) ^ (((B \ T).card : ℝ) / 2) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = 2 ^ T.card * (2 : ℝ) ^ (((B \ T).card : ℝ) / 2) := by
        rw [Finset.card_powerset, Nat.cast_pow, Nat.cast_two]

/-- **BLST Lemma 2.6 (combined exponent).**  Under the same hypotheses,
`misCount adj loop B ≤ 2^{(|B| + |T|)/2}`. -/
theorem misCount_le_two_rpow_card_add {adj : ℤ → ℤ → Prop}
    {loop : ℤ → Prop} [DecidableRel adj] [DecidablePred loop]
    (hsymm : ∀ x y, adj x y → adj y x)
    {B T : Finset ℤ} (hT : T ⊆ B) (htri : triangleFree adj (B \ T)) :
    (misCount adj loop B : ℝ) ≤
      (2 : ℝ) ^ (((B.card : ℝ) + T.card) / 2) := by
  have hle : T.card ≤ B.card := Finset.card_le_card hT
  have hcard : (B \ T).card = B.card - T.card :=
    Finset.card_sdiff_of_subset hT
  calc (misCount adj loop B : ℝ)
      ≤ 2 ^ T.card * (2 : ℝ) ^ (((B \ T).card : ℝ) / 2) :=
        misCount_le_two_pow_mul_two_rpow_sdiff hsymm hT htri
    _ = (2 : ℝ) ^ (((B.card : ℝ) + T.card) / 2) := by
        rw [← Real.rpow_natCast (2 : ℝ) T.card,
          ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        have e : (T.card : ℝ) + ((B \ T).card : ℝ) / 2 =
            ((B.card : ℝ) + T.card) / 2 := by
          rw [hcard, Nat.cast_sub hle]
          ring
        rw [e]

/-- **Transfer to the link graph.**  If `T ⊆ B` and the link graph on
`B ∖ T` is triangle-free, then
`|linkMaxSets S B| ≤ 2^{|T|} · 2^{|B ∖ T|/2}` (the odd-container case of
the BLST bound). -/
theorem card_linkMaxSets_le_two_pow_mul_two_rpow_sdiff {S B T : Finset ℤ}
    (hT : T ⊆ B) (htri : triangleFree (linkAdj S) (B \ T)) :
    ((linkMaxSets S B).card : ℝ) ≤
      2 ^ T.card * (2 : ℝ) ^ (((B \ T).card : ℝ) / 2) := by
  have h := misCount_le_two_pow_mul_two_rpow_sdiff
    (adj := linkAdj S) (loop := linkLoop S)
    (fun x y h => linkAdj_comm.mp h) hT htri
  simp only [misCount, maxIndepSets_link] at h
  exact h

end JSP000728
