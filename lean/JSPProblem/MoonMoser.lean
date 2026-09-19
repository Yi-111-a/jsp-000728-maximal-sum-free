import JSPProblem.LinkGraph
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith

/-!
# JSP-000728 — a Moon–Moser bound for maximal independent sets

Moon–Moser (1965): a graph on `n` vertices has at most `3^{n/3}` maximal
independent sets.  We prove the bound for a generic adjacency-with-loops
model `maxIndepSets adj loop B`, which instantiates to the link-graph
family `linkMaxSets S B` (see `card_linkMaxSets_le_three_rpow`).

The proof is the standard minimum-degree recurrence.  Every maximal
independent set `t` meets the closed neighbourhood `N[v]` of a
non-looped vertex `v` (otherwise `t` could absorb `v`), and for
`u ∈ t ∩ N[v]` the fibre `t ↦ t.erase u` lands in the maximal
independent sets of `B ∖ N[u]` (`maxIndepSet_erase`).  Choosing `v`
with `|N[v]| = c` minimal over the non-looped vertices gives

`mis(G) ≤ c · 3^{(n−c)/3} ≤ 3^{n/3}`,

using `c³ ≤ 3^c` for all `c ≥ 1` (`cube_le_three_pow`).
-/

namespace JSP000728

/-! ## Generic maximal independent sets -/

/-- `t` is independent for adjacency `adj` with loops `loop`: no vertex of
`t` is looped and no two vertices of `t` are adjacent. -/
def indepSet (adj : ℤ → ℤ → Prop) (loop : ℤ → Prop) (t : Finset ℤ) : Prop :=
  (∀ x ∈ t, ¬ loop x) ∧ ∀ x ∈ t, ∀ y ∈ t, ¬ adj x y

instance decidableIndepSet (adj : ℤ → ℤ → Prop) (loop : ℤ → Prop)
    [DecidableRel adj] [DecidablePred loop] (t : Finset ℤ) :
    Decidable (indepSet adj loop t) := by
  unfold indepSet; infer_instance

/-- `t` is a maximal independent subset of `B` for `(adj, loop)`: it is
independent, contained in `B`, and every `x ∈ B ∖ t` carries a loop or has
an edge into `t`. -/
def maxIndepSet (adj : ℤ → ℤ → Prop) (loop : ℤ → Prop) (B t : Finset ℤ) :
    Prop :=
  t ⊆ B ∧ indepSet adj loop t ∧
    ∀ x ∈ B, x ∉ t → loop x ∨ ∃ y ∈ t, adj x y

instance decidableMaxIndepSet (adj : ℤ → ℤ → Prop) (loop : ℤ → Prop)
    [DecidableRel adj] [DecidablePred loop] (B t : Finset ℤ) :
    Decidable (maxIndepSet adj loop B t) := by
  unfold maxIndepSet; infer_instance

/-- The family of maximal independent subsets of `B`. -/
def maxIndepSets (adj : ℤ → ℤ → Prop) (loop : ℤ → Prop) [DecidableRel adj]
    [DecidablePred loop] (B : Finset ℤ) : Finset (Finset ℤ) :=
  B.powerset.filter (maxIndepSet adj loop B)

/-- The number of maximal independent subsets of `B`. -/
def misCount (adj : ℤ → ℤ → Prop) (loop : ℤ → Prop) [DecidableRel adj]
    [DecidablePred loop] (B : Finset ℤ) : ℕ :=
  (maxIndepSets adj loop B).card

theorem mem_maxIndepSets {adj : ℤ → ℤ → Prop} {loop : ℤ → Prop}
    [DecidableRel adj] [DecidablePred loop] {B t : Finset ℤ} :
    t ∈ maxIndepSets adj loop B ↔ maxIndepSet adj loop B t := by
  rw [maxIndepSets, Finset.mem_filter, Finset.mem_powerset]
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨h.1, h⟩⟩

/-- The closed neighbourhood of `u` in `B`: `u` itself together with all
its `adj`-neighbours inside `B`. -/
def nbd (adj : ℤ → ℤ → Prop) [DecidableRel adj] (B : Finset ℤ) (u : ℤ) :
    Finset ℤ :=
  B.filter fun y => y = u ∨ adj u y

/-- **Fibre maximality.**  If `t` is a maximal independent subset of `B`
and `u ∈ t`, then `t.erase u` is a maximal independent subset of
`B ∖ N[u]`: every `x ∈ B ∖ N[u] ∖ t` is still blocked by `t` (its blocker
cannot be `u` itself, since `x ∉ N[u]` rules out `x = u` and `adj u x`). -/
theorem maxIndepSet_erase {adj : ℤ → ℤ → Prop} {loop : ℤ → Prop}
    [DecidableRel adj] [DecidablePred loop]
    (hsymm : ∀ x y : ℤ, adj x y → adj y x) {B t : Finset ℤ} {u : ℤ}
    (ht : maxIndepSet adj loop B t) (hu : u ∈ t) :
    maxIndepSet adj loop (B \ nbd adj B u) (t.erase u) := by
  obtain ⟨htB, hti, htm⟩ := ht
  refine ⟨?_, ⟨?_, ?_⟩, ?_⟩
  · -- `t.erase u ⊆ B ∖ N[u]`: a second `t`-element cannot equal `u` or be
    -- adjacent to `u` (independence of `t`).
    intro y hy
    rw [Finset.mem_erase] at hy
    obtain ⟨hyu, hyt⟩ := hy
    rw [Finset.mem_sdiff]
    refine ⟨htB hyt, fun hyN => ?_⟩
    have hyN' := Finset.mem_filter.mp hyN
    rcases hyN'.2 with rfl | hyadj
    · exact hyu rfl
    · exact hti.2 u hu y hyt hyadj
  · intro x hx
    exact hti.1 x (Finset.mem_of_mem_erase hx)
  · intro x hx y hy
    exact hti.2 x (Finset.mem_of_mem_erase hx) y (Finset.mem_of_mem_erase hy)
  · -- maximality: `x ∈ B ∖ N[u]`, `x ∉ t.erase u`.
    intro x hx hxt
    rw [Finset.mem_sdiff] at hx
    obtain ⟨hxB, hxN⟩ := hx
    have hxN' : ¬ (x = u ∨ adj u x) :=
      fun h => hxN (Finset.mem_filter.mpr ⟨hxB, h⟩)
    have hxnt : x ∉ t := fun hxm =>
      hxt (Finset.mem_erase.mpr ⟨fun h => hxN' (Or.inl h), hxm⟩)
    rcases htm x hxB hxnt with hl | ⟨y, hyt, hyadj⟩
    · exact Or.inl hl
    · refine Or.inr ⟨y, Finset.mem_erase.mpr ⟨?_, hyt⟩, hyadj⟩
      rintro rfl
      exact hxN' (Or.inr (hsymm _ _ hyadj))

/-! ## The arithmetic step `c³ ≤ 3^c` -/

/-- `c³ ≤ 3^c` for all `c ≥ 1` — the arithmetic heart of the `3^{n/3}`
bound (`t·3^{−t/3} ≤ 1` for `t ≥ 1`, with equality at `t = 3`).  For
`c ≥ 3` one inducts: the ratio `(1 + 1/c)³ ≤ (4/3)³ < 3`. -/
theorem cube_le_three_pow {c : ℕ} (hc : 1 ≤ c) : (c : ℝ) ^ 3 ≤ (3 : ℝ) ^ c := by
  have key : ∀ k : ℕ, 3 ≤ k → (k : ℝ) ^ 3 ≤ (3 : ℝ) ^ k := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => norm_num
    | succ k hk ih =>
      push_cast
      have hk3 : (3 : ℝ) ≤ k := by exact_mod_cast hk
      have hk0 : (0 : ℝ) ≤ k := by linarith
      have h1 : 3 * (k : ℝ) ^ 2 ≤ (k : ℝ) ^ 3 :=
        calc 3 * (k : ℝ) ^ 2 ≤ (k : ℝ) * (k : ℝ) ^ 2 :=
              mul_le_mul_of_nonneg_right hk3 (sq_nonneg _)
          _ = (k : ℝ) ^ 3 := by ring
      have h2 : 3 * (k : ℝ) + 1 ≤ (k : ℝ) ^ 3 := by
        have h9 : (9 : ℝ) ≤ (k : ℝ) ^ 2 := by
          nlinarith [mul_nonneg (sub_nonneg.mpr hk3)
            (show (0 : ℝ) ≤ (k : ℝ) + 3 by linarith)]
        calc 3 * (k : ℝ) + 1 ≤ 9 * (k : ℝ) := by linarith
          _ = (k : ℝ) * 9 := by ring
          _ ≤ (k : ℝ) * (k : ℝ) ^ 2 := mul_le_mul_of_nonneg_left h9 hk0
          _ = (k : ℝ) ^ 3 := by ring
      have h3 : ((k : ℝ) + 1) ^ 3 ≤ 3 * (k : ℝ) ^ 3 := by
        have e : ((k : ℝ) + 1) ^ 3 =
            (k : ℝ) ^ 3 + 3 * (k : ℝ) ^ 2 + 3 * (k : ℝ) + 1 := by ring
        rw [e]; linarith
      calc ((k : ℝ) + 1) ^ 3 ≤ 3 * (k : ℝ) ^ 3 := h3
        _ ≤ 3 * (3 : ℝ) ^ k :=
            mul_le_mul_of_nonneg_left ih (show (0 : ℝ) ≤ 3 by norm_num)
        _ = (3 : ℝ) ^ (k + 1) := (pow_succ' _ _).symm
  rcases Nat.lt_or_ge c 3 with hlt | hge
  · interval_cases c <;> norm_num
  · exact key c hge

/-- `c ≤ 3^{c/3}` for `c ≥ 1`: the cube root of `c³ ≤ 3^c`. -/
theorem natCast_le_three_rpow_div_three {c : ℕ} (hc : 1 ≤ c) :
    (c : ℝ) ≤ (3 : ℝ) ^ ((c : ℝ) / 3) := by
  have e : ((3 : ℝ) ^ ((c : ℝ) / 3)) ^ 3 = (3 : ℝ) ^ c := by
    rw [← Real.rpow_natCast _ 3, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3),
      ← Real.rpow_natCast _ c]
    congr 1
    push_cast
    ring
  have h := cube_le_three_pow hc
  rw [← e] at h
  exact (pow_le_pow_iff_left₀ (Nat.cast_nonneg c)
    (Real.rpow_nonneg (show (0 : ℝ) ≤ 3 by norm_num) _)
    (by norm_num : (3 : ℕ) ≠ 0)).mp h

/-- `c · 3^{(n−c)/3} ≤ 3^{n/3}` for `c ≥ 1` — the final estimate of the
min-degree recurrence `mis ≤ Σ_{u ∈ N[v]} mis(G ∖ N[u])`. -/
theorem mul_three_rpow_le {n c : ℕ} (hc : 1 ≤ c) :
    (c : ℝ) * (3 : ℝ) ^ (((n : ℝ) - c) / 3) ≤ (3 : ℝ) ^ ((n : ℝ) / 3) := by
  have hc3 : (c : ℝ) ≤ (3 : ℝ) ^ ((c : ℝ) / 3) :=
    natCast_le_three_rpow_div_three hc
  have h3c : (0 : ℝ) < (3 : ℝ) ^ ((c : ℝ) / 3) :=
    Real.rpow_pos_of_pos (show (0 : ℝ) < 3 by norm_num) _
  have h3n : (0 : ℝ) < (3 : ℝ) ^ ((n : ℝ) / 3) :=
    Real.rpow_pos_of_pos (show (0 : ℝ) < 3 by norm_num) _
  rw [show ((n : ℝ) - c) / 3 = (n : ℝ) / 3 - (c : ℝ) / 3 by ring,
    Real.rpow_sub (by norm_num : (0 : ℝ) < 3), ← mul_div_assoc,
    div_le_iff₀ h3c]
  calc (c : ℝ) * (3 : ℝ) ^ ((n : ℝ) / 3)
      ≤ (3 : ℝ) ^ ((c : ℝ) / 3) * (3 : ℝ) ^ ((n : ℝ) / 3) :=
        mul_le_mul_of_nonneg_right hc3 h3n.le
    _ = (3 : ℝ) ^ ((n : ℝ) / 3) * (3 : ℝ) ^ ((c : ℝ) / 3) := by ring

/-! ## The Moon–Moser bound -/

/-- **Moon–Moser bound.**  For a symmetric adjacency `adj` with loops
`loop`, the number of maximal independent subsets of `B` is at most
`3^{|B|/3}`.  Induction on `|B|`: if every vertex is looped the only
maximal independent set is `∅`; otherwise pick a non-looped vertex `v`
minimising `|N[v]|` over non-looped vertices and use the fibre covering
`t ↦ t.erase u` over `u ∈ t ∩ N[v]`. -/
theorem misCount_le_three_rpow (adj : ℤ → ℤ → Prop) (loop : ℤ → Prop)
    [DecidableRel adj] [DecidablePred loop]
    (hsymm : ∀ x y : ℤ, adj x y → adj y x) :
    ∀ n : ℕ, ∀ B : Finset ℤ, B.card ≤ n →
      (misCount adj loop B : ℝ) ≤ (3 : ℝ) ^ ((B.card : ℝ) / 3) := by
  intro n
  induction n with
  | zero =>
    intro B hB
    rw [Nat.le_zero, Finset.card_eq_zero] at hB
    subst hB
    have h1 : maxIndepSets adj loop ∅ = {∅} := by
      ext t
      rw [mem_maxIndepSets, Finset.mem_singleton]
      constructor
      · rintro ⟨htB, -, -⟩
        exact Finset.subset_empty.mp htB
      · rintro rfl
        exact ⟨Finset.empty_subset _,
          ⟨fun x hx => absurd hx (Finset.notMem_empty x),
            fun x hx y _ => absurd hx (Finset.notMem_empty x)⟩,
          fun x hx => absurd hx (Finset.notMem_empty x)⟩
    rw [show misCount adj loop ∅ = 1 by simp [misCount, h1]]
    have hz : (0 : ℝ) ≤ ((∅ : Finset ℤ).card : ℝ) / 3 := by positivity
    exact_mod_cast Real.one_le_rpow (show (1 : ℝ) ≤ 3 by norm_num) hz
  | succ n ih =>
    intro B hB
    by_cases hall : ∀ v ∈ B, loop v
    · -- every vertex looped: the only maximal independent set is `∅`.
      have h1 : maxIndepSets adj loop B = {∅} := by
        ext t
        rw [mem_maxIndepSets, Finset.mem_singleton]
        constructor
        · rintro ⟨htB, hti, -⟩
          exact Finset.eq_empty_iff_forall_notMem.mpr
            fun x hx => hti.1 x hx (hall x (htB hx))
        · rintro rfl
          exact ⟨Finset.empty_subset _,
            ⟨fun x hx => absurd hx (Finset.notMem_empty x),
              fun x hx y _ => absurd hx (Finset.notMem_empty x)⟩,
            fun x hxB _ => Or.inl (hall x hxB)⟩
      rw [show misCount adj loop B = 1 by simp [misCount, h1]]
      have hz : (0 : ℝ) ≤ (B.card : ℝ) / 3 := by positivity
      exact_mod_cast Real.one_le_rpow (show (1 : ℝ) ≤ 3 by norm_num) hz
    · -- some vertex `v` is not looped; pick one minimising `|N[v]|`.
      push Not at hall
      obtain ⟨w, hwB, hwl⟩ := hall
      obtain ⟨v, hvNL, hvmin⟩ := Finset.exists_min_image
        (B.filter (fun x => ¬ loop x)) (fun u => (nbd adj B u).card)
        ⟨w, Finset.mem_filter.mpr ⟨hwB, hwl⟩⟩
      rw [Finset.mem_filter] at hvNL
      obtain ⟨hvB, hvl⟩ := hvNL
      have hvNv : v ∈ nbd adj B v := Finset.mem_filter.mpr ⟨hvB, Or.inl rfl⟩
      have hc1 : 1 ≤ (nbd adj B v).card := Finset.card_pos.mpr ⟨v, hvNv⟩
      have hNvs : nbd adj B v ⊆ B := Finset.filter_subset _ _
      have hcn : (nbd adj B v).card ≤ B.card := Finset.card_le_card hNvs
      -- every MIS `t` of `B` meets `N[v]` at a non-looped `u`, and then
      -- `t = insert u (t.erase u)` with `t.erase u` a MIS of `B ∖ N[u]`.
      have cover : maxIndepSets adj loop B ⊆
          ((nbd adj B v).filter (fun u => ¬ loop u)).biUnion
            (fun u => (maxIndepSets adj loop (B \ nbd adj B u)).image
              (insert u)) := by
        intro t ht
        rw [mem_maxIndepSets] at ht
        obtain ⟨htB, hti, htm⟩ := ht
        have hne : (t ∩ nbd adj B v).Nonempty := by
          by_contra hcon
          rw [Finset.not_nonempty_iff_eq_empty] at hcon
          have hvt : v ∉ t := fun hv => by
            have h2 : v ∈ t ∩ nbd adj B v := Finset.mem_inter.mpr ⟨hv, hvNv⟩
            rw [hcon] at h2
            exact Finset.notMem_empty _ h2
          rcases htm v hvB hvt with hl | ⟨y, hyt, hyadj⟩
          · exact hvl hl
          · have h2 : y ∈ t ∩ nbd adj B v := Finset.mem_inter.mpr
                ⟨hyt, Finset.mem_filter.mpr ⟨htB hyt, Or.inr hyadj⟩⟩
            rw [hcon] at h2
            exact Finset.notMem_empty _ h2
        obtain ⟨u, hu⟩ := hne
        rw [Finset.mem_inter] at hu
        obtain ⟨hut, huNv⟩ := hu
        obtain ⟨huB, hvu⟩ := Finset.mem_filter.mp huNv
        have hul : ¬ loop u := hti.1 u hut
        rw [Finset.mem_biUnion]
        refine ⟨u, Finset.mem_filter.mpr
          ⟨Finset.mem_filter.mpr ⟨huB, hvu⟩, hul⟩, ?_⟩
        rw [Finset.mem_image]
        exact ⟨t.erase u, mem_maxIndepSets.mpr
          (maxIndepSet_erase hsymm ⟨htB, hti, htm⟩ hut),
          Finset.insert_erase hut⟩
      have hcard : (misCount adj loop B : ℝ) ≤
          ∑ u ∈ (nbd adj B v).filter (fun u => ¬ loop u),
            (misCount adj loop (B \ nbd adj B u) : ℝ) := by
        have h2 : (maxIndepSets adj loop B).card ≤
            ∑ u ∈ (nbd adj B v).filter (fun u => ¬ loop u),
              ((maxIndepSets adj loop (B \ nbd adj B u)).image
                (insert u)).card :=
          le_trans (Finset.card_le_card cover) Finset.card_biUnion_le
        have h3 : ∑ u ∈ (nbd adj B v).filter (fun u => ¬ loop u),
              ((maxIndepSets adj loop (B \ nbd adj B u)).image
                (insert u)).card ≤
            ∑ u ∈ (nbd adj B v).filter (fun u => ¬ loop u),
              (maxIndepSets adj loop (B \ nbd adj B u)).card :=
          Finset.sum_le_sum fun u _ => Finset.card_image_le
        simp only [misCount]
        exact_mod_cast le_trans h2 h3
      -- each fibre has `|B ∖ N[u]| ≤ n − c` vertices, `c = |N[v]|`.
      have hterm : ∀ u ∈ (nbd adj B v).filter (fun u => ¬ loop u),
          (misCount adj loop (B \ nbd adj B u) : ℝ) ≤
            (3 : ℝ) ^ (((B.card : ℝ) - (nbd adj B v).card) / 3) := by
        intro u huF
        obtain ⟨huNv, hul⟩ := Finset.mem_filter.mp huF
        obtain ⟨huB, -⟩ := Finset.mem_filter.mp huNv
        have hcu : (nbd adj B v).card ≤ (nbd adj B u).card :=
          hvmin u (Finset.mem_filter.mpr ⟨huB, hul⟩)
        have hsub : nbd adj B u ⊆ B := Finset.filter_subset _ _
        have hsdiff : (B \ nbd adj B u).card = B.card - (nbd adj B u).card :=
          Finset.card_sdiff_of_subset hsub
        have hu1 : 1 ≤ (nbd adj B u).card := Finset.card_pos.mpr
          ⟨u, Finset.mem_filter.mpr ⟨huB, Or.inl rfl⟩⟩
        have hlen : (B \ nbd adj B u).card ≤ n := by omega
        have hle2 : ((B \ nbd adj B u).card : ℝ) ≤
            (B.card : ℝ) - (nbd adj B v).card := by
          have h : (B \ nbd adj B u).card ≤ B.card - (nbd adj B v).card := by
            omega
          calc ((B \ nbd adj B u).card : ℝ)
              ≤ ((B.card - (nbd adj B v).card : ℕ) : ℝ) := by exact_mod_cast h
            _ = (B.card : ℝ) - (nbd adj B v).card := Nat.cast_sub hcn
        calc (misCount adj loop (B \ nbd adj B u) : ℝ)
            ≤ (3 : ℝ) ^ (((B \ nbd adj B u).card : ℝ) / 3) := ih _ hlen
          _ ≤ (3 : ℝ) ^ (((B.card : ℝ) - (nbd adj B v).card) / 3) := by
              refine Real.rpow_le_rpow_of_exponent_le
                (show (1 : ℝ) ≤ 3 by norm_num) ?_
              linarith
      calc (misCount adj loop B : ℝ)
          ≤ ∑ u ∈ (nbd adj B v).filter (fun u => ¬ loop u),
              (misCount adj loop (B \ nbd adj B u) : ℝ) := hcard
        _ ≤ ∑ u ∈ (nbd adj B v).filter (fun u => ¬ loop u),
              (3 : ℝ) ^ (((B.card : ℝ) - (nbd adj B v).card) / 3) :=
            Finset.sum_le_sum fun u hu => hterm u hu
        _ = (((nbd adj B v).filter (fun u => ¬ loop u)).card : ℝ) *
              (3 : ℝ) ^ (((B.card : ℝ) - (nbd adj B v).card) / 3) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ((nbd adj B v).card : ℝ) *
              (3 : ℝ) ^ (((B.card : ℝ) - (nbd adj B v).card) / 3) := by
            refine mul_le_mul_of_nonneg_right ?_
              (Real.rpow_nonneg (show (0 : ℝ) ≤ 3 by norm_num) _)
            exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
        _ ≤ (3 : ℝ) ^ ((B.card : ℝ) / 3) := mul_three_rpow_le hc1

/-! ## Transfer to the link graph -/

/-- The generic maximal-independent-set predicate specialises to the
link-graph one. -/
theorem maxIndepSet_iff_link {S B t : Finset ℤ} :
    maxIndepSet (linkAdj S) (linkLoop S) B t ↔ linkMaxIndepSet S B t :=
  Iff.rfl

/-- `maxIndepSets (linkAdj S) (linkLoop S) B = linkMaxSets S B`. -/
theorem maxIndepSets_link (S B : Finset ℤ) :
    maxIndepSets (linkAdj S) (linkLoop S) B = linkMaxSets S B := by
  unfold maxIndepSets linkMaxSets
  exact Finset.filter_congr fun t _ => maxIndepSet_iff_link

/-- **Moon–Moser for the link graph**: `|linkMaxSets S B| ≤ 3^{|B|/3}`. -/
theorem card_linkMaxSets_le_three_rpow (S B : Finset ℤ) :
    ((linkMaxSets S B).card : ℝ) ≤ (3 : ℝ) ^ ((B.card : ℝ) / 3) := by
  have h := misCount_le_three_rpow (linkAdj S) (linkLoop S)
    (fun x y h => linkAdj_comm.mp h) B.card B le_rfl
  simp only [misCount, maxIndepSets_link] at h
  exact h

/-- Integer form: `(misCount)^3 ≤ 3^{|B|}` for the link graph. -/
theorem card_linkMaxSets_cube_le (S B : Finset ℤ) :
    (linkMaxSets S B).card ^ 3 ≤ 3 ^ B.card := by
  have h := card_linkMaxSets_le_three_rpow S B
  have h2 : ((linkMaxSets S B).card : ℝ) ^ 3 ≤
      ((3 : ℝ) ^ ((B.card : ℝ) / 3)) ^ 3 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) h 3
  have e : ((3 : ℝ) ^ ((B.card : ℝ) / 3)) ^ 3 = (3 : ℝ) ^ B.card := by
    rw [← Real.rpow_natCast _ 3, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3),
      ← Real.rpow_natCast _ B.card]
    congr 1
    push_cast
    ring
  rw [e] at h2
  exact_mod_cast h2

/-- Integer form with a coarse exponent: `|linkMaxSets S B| ≤ 3^{|B|/3+1}`
(natural division). -/
theorem card_linkMaxSets_le_three_pow (S B : Finset ℤ) :
    (linkMaxSets S B).card ≤ 3 ^ (B.card / 3 + 1) := by
  have h := card_linkMaxSets_le_three_rpow S B
  have h1 : B.card < 3 * (B.card / 3 + 1) :=
    Nat.lt_mul_div_succ B.card (show (0 : ℕ) < 3 by norm_num)
  have hlt : (B.card : ℝ) / 3 < ((B.card / 3 + 1 : ℕ) : ℝ) := by
    have h1' : (B.card : ℝ) < 3 * ((B.card / 3 + 1 : ℕ) : ℝ) := by
      exact_mod_cast h1
    linarith
  have hle : (3 : ℝ) ^ ((B.card : ℝ) / 3) ≤
      (3 : ℝ) ^ (((B.card / 3 + 1 : ℕ) : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 3 by norm_num) hlt.le
  rw [Real.rpow_natCast] at hle
  exact_mod_cast le_trans h hle

end JSP000728
