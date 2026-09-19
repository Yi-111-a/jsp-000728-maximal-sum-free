import JSPProblem.MoonMoser
import JSPProblem.LinkTriangleFree
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith

/-!
# JSP-000728 — the Hujter–Tuza bound for maximal independent sets

Hujter–Tuza (1993): a *triangle-free* graph on `n` vertices has at most
`2^{n/2}` maximal independent sets — sharp for a perfect matching.  We
prove the bound for the generic adjacency-with-loops model
`maxIndepSets adj loop B` of `MoonMoser.lean` and specialise it to the
link graph on the upper half (which is triangle-free by
`LinkTriangleFree.lean`).

The proof is a refined minimum-degree recurrence.  Fix a non-looped
vertex `u` minimising the closed-neighbourhood size `c = |N[u]|`, and let
`s` be the non-looped open neighbourhood of `u`.  Every maximal
independent set `t` either contains `u` — then `t.erase u` is maximal
independent in `B ∖ N[u]` — or avoids `u`, in which case maximality gives
`t ∩ s ≠ ∅`.  For the *least* `w ∈ t ∩ s`, the set `t.erase w` is maximal
independent in `B ∖ (N[w] ∪ s.filter (· < w))`: triangle-freeness makes
`N[w]` disjoint from the smaller neighbours of `u`, so the reduced ground
set has at most `n − c − rank(w)` elements, where `rank w` is the number
of smaller neighbours of `u`.  Since `rank` is injective,

  `mi(G) ≤ 2^{(n−c)/2} · (1 + Σ_{j<k} ρ^j)`,  `ρ = 2^{−1/2}`,
  `k = |s| ≤ c−1`,

and `1 + Σ_{j<k} ρ^j ≤ 2^{c/2}` (`one_add_geom_le_sigma_pow`): equality
at `k = 1, c = 2`; the cases `k ≤ 3` are finite checks, and for `k ≥ 4`
the geometric sum is bounded by `1/(1−ρ) = 2+√2 ≤ 4√2 = 2^{5/2}`.
-/

namespace JSP000728

/-- `adj` is *triangle-free* on `B`: no three pairwise distinct vertices
of `B` are pairwise adjacent. -/
def triangleFree (adj : ℤ → ℤ → Prop) (B : Finset ℤ) : Prop :=
  ∀ x ∈ B, ∀ y ∈ B, ∀ z ∈ B, x ≠ y → y ≠ z → x ≠ z →
    ¬ (adj x y ∧ adj y z ∧ adj x z)

theorem triangleFree.mono {adj : ℤ → ℤ → Prop} {C B : Finset ℤ}
    (h : triangleFree adj B) (hCB : C ⊆ B) : triangleFree adj C :=
  fun x hx y hy z hz hxy hyz hxz =>
    h x (hCB hx) y (hCB hy) z (hCB hz) hxy hyz hxz

/-- The non-looped open neighbourhood of `u` inside `B` (`u` itself
excluded): the vertices that can actually serve as dominators of `u` in a
maximal independent set. -/
def openNbd (adj : ℤ → ℤ → Prop) (loop : ℤ → Prop) [DecidableRel adj]
    [DecidablePred loop] (B : Finset ℤ) (u : ℤ) : Finset ℤ :=
  B.filter fun y => y ≠ u ∧ adj u y ∧ ¬ loop y

/-! ## The covering lemma -/

/-- **Covering by the least selected neighbour.**  Every maximal
independent set `t` of `B` is the insertion of `u` into a maximal
independent set of `B ∖ N[u]`, or the insertion of the least `w` of
`t ∩ s` into a maximal independent set of `B ∖ (N[w] ∪ s.filter (· < w))`,
where `s` is the non-looped open neighbourhood of `u`.  Triangle-freeness
is not needed for the inclusion itself — it enters only later, when
bounding the size of the reduced ground set. -/
theorem maxIndepSets_subset_leastNbd_cover {adj : ℤ → ℤ → Prop}
    {loop : ℤ → Prop} [DecidableRel adj] [DecidablePred loop]
    (hsymm : ∀ x y : ℤ, adj x y → adj y x)
    {B : Finset ℤ} {u : ℤ} (huB : u ∈ B) (hul : ¬ loop u) :
    maxIndepSets adj loop B ⊆
      (maxIndepSets adj loop (B \ nbd adj B u)).image (insert u) ∪
        (openNbd adj loop B u).biUnion fun w =>
          (maxIndepSets adj loop
            (B \ (nbd adj B w ∪
              (openNbd adj loop B u).filter (· < w)))).image (insert w) := by
  intro t ht
  rw [mem_maxIndepSets] at ht
  obtain ⟨htB, hti, htm⟩ := ht
  by_cases hut : u ∈ t
  · rw [Finset.mem_union]
    left
    rw [Finset.mem_image]
    exact ⟨t.erase u,
      mem_maxIndepSets.mpr
        (maxIndepSet_erase hsymm ⟨htB, hti, htm⟩ hut),
      Finset.insert_erase hut⟩
  · rw [Finset.mem_union]
    right
    obtain ⟨y, hyt, hyadj⟩ := (htm u huB hut).resolve_left hul
    have hys : y ∈ openNbd adj loop B u :=
      Finset.mem_filter.mpr ⟨htB hyt, fun h => hut (h ▸ hyt), hyadj,
        hti.1 y hyt⟩
    have hne : (t ∩ openNbd adj loop B u).Nonempty :=
      ⟨y, Finset.mem_inter.mpr ⟨hyt, hys⟩⟩
    set w := (t ∩ openNbd adj loop B u).min' hne with hwdef
    have hwmem : w ∈ t ∩ openNbd adj loop B u := Finset.min'_mem _ hne
    obtain ⟨hwt, hws⟩ := Finset.mem_inter.mp hwmem
    obtain ⟨hwB, hwu, hwadj, hwl⟩ := Finset.mem_filter.mp hws
    rw [Finset.mem_biUnion]
    refine ⟨w, Finset.mem_filter.mpr ⟨hwB, hwu, hwadj, hwl⟩, ?_⟩
    rw [Finset.mem_image]
    refine ⟨t.erase w, ?_, Finset.insert_erase hwt⟩
    rw [mem_maxIndepSets]
    refine ⟨?_, ⟨?_, ?_⟩, ?_⟩
    · -- `t.erase w ⊆ B ∖ (N[w] ∪ s.filter (· < w))`.
      intro z hz
      rw [Finset.mem_erase] at hz
      obtain ⟨hzw, hzt⟩ := hz
      rw [Finset.mem_sdiff]
      refine ⟨htB hzt, ?_⟩
      rw [Finset.mem_union, not_or]
      refine ⟨?_, ?_⟩
      · intro hzN
        obtain ⟨_, hzw'⟩ := Finset.mem_filter.mp hzN
        rcases hzw' with rfl | hadj
        · exact hzw rfl
        · exact hti.2 w hwt z hzt hadj
      · intro hzL
        obtain ⟨hzs, hzw2⟩ := Finset.mem_filter.mp hzL
        have hle : w ≤ z :=
          Finset.min'_le _ z (Finset.mem_inter.mpr ⟨hzt, hzs⟩)
        exact absurd hle (not_le.mpr hzw2)
    · intro x hx
      exact hti.1 x (Finset.mem_of_mem_erase hx)
    · intro x hx y hy
      exact hti.2 x (Finset.mem_of_mem_erase hx)
        y (Finset.mem_of_mem_erase hy)
    · -- maximality in `B ∖ (N[w] ∪ s.filter (· < w))`.
      intro x hx hxt
      rw [Finset.mem_sdiff] at hx
      obtain ⟨hxB, hxU⟩ := hx
      rw [Finset.mem_union, not_or] at hxU
      obtain ⟨hxNw, _⟩ := hxU
      have hxnw : ¬ (x = w ∨ adj w x) :=
        fun h => hxNw (Finset.mem_filter.mpr ⟨hxB, h⟩)
      have hxnt : x ∉ t := by
        intro hxm
        apply hxt
        rw [Finset.mem_erase]
        exact ⟨fun h => hxnw (Or.inl h), hxm⟩
      rcases htm x hxB hxnt with hl | ⟨y, hyt, hyadj⟩
      · exact Or.inl hl
      · refine Or.inr ⟨y, Finset.mem_erase.mpr ⟨?_, hyt⟩, hyadj⟩
        rintro rfl
        exact hxnw (Or.inr (hsymm _ _ hyadj))

/-! ## Real-arithmetic facts about `σ = 2^{1/2}` and `ρ = 2^{−1/2}` -/

private theorem two_rpow_half_sq :
    ((2 : ℝ) ^ ((1 : ℝ) / 2)) ^ 2 = 2 := by
  rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  have e : (1 : ℝ) / 2 * ((2 : ℕ) : ℝ) = 1 := by norm_num
  rw [e, Real.rpow_one]

private theorem one_le_two_rpow_half :
    (1 : ℝ) ≤ (2 : ℝ) ^ ((1 : ℝ) / 2) :=
  Real.one_le_rpow (by norm_num) (by norm_num)

private theorem two_rpow_neg_half_lt_one :
    (2 : ℝ) ^ ((-1 : ℝ) / 2) < 1 := by
  calc (2 : ℝ) ^ ((-1 : ℝ) / 2) < (2 : ℝ) ^ (0 : ℝ) :=
      Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by norm_num)
    _ = 1 := Real.rpow_zero 2

private theorem two_rpow_neg_half_pos :
    (0 : ℝ) < (2 : ℝ) ^ ((-1 : ℝ) / 2) :=
  Real.rpow_pos_of_pos (by norm_num) _

private theorem two_rpow_neg_half_mul :
    (2 : ℝ) ^ ((-1 : ℝ) / 2) * (2 : ℝ) ^ ((1 : ℝ) / 2) = 1 := by
  rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
  rw [show (-1:ℝ)/2 + 1/2 = 0 by ring, Real.rpow_zero]

private theorem two_rpow_neg_half_sq :
    ((2 : ℝ) ^ ((-1 : ℝ) / 2)) ^ 2 = 1 / 2 := by
  have hρinv : (2 : ℝ) ^ ((-1 : ℝ) / 2) = ((2 : ℝ) ^ ((1 : ℝ) / 2))⁻¹ := by
    rw [← Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
    congr 1
    ring
  rw [hρinv, inv_pow, two_rpow_half_sq]
  norm_num

private theorem two_rpow_half_le :
    (2 : ℝ) ^ ((1 : ℝ) / 2) ≤ 3 / 2 := by
  nlinarith [two_rpow_half_sq,
    sq_nonneg ((2 : ℝ) ^ ((1 : ℝ) / 2) - 3 / 2),
    Real.rpow_pos_of_pos (show (0:ℝ) < 2 by norm_num) ((1:ℝ)/2)]

/-- `σ ^ n = 2^{n/2}` for `σ = 2^{1/2}` (natural power). -/
private theorem two_rpow_half_pow (n : ℕ) :
    ((2 : ℝ) ^ ((1 : ℝ) / 2)) ^ n = (2 : ℝ) ^ ((n : ℝ) / 2) := by
  rw [← Real.rpow_natCast _ n, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  congr 1
  ring

/-- The geometric sum `Σ_{j<k} ρ^j` is bounded by its infinite sum
`1/(1−ρ) = 2 + σ`, where `ρ = 2^{−1/2}` and `σ = 2^{1/2}`. -/
private theorem sum_geom_le_two_add (k : ℕ) :
    ∑ j ∈ Finset.range k, ((2 : ℝ) ^ ((-1 : ℝ) / 2)) ^ j ≤
      2 + (2 : ℝ) ^ ((1 : ℝ) / 2) := by
  set ρ := (2 : ℝ) ^ ((-1 : ℝ) / 2) with hρdef
  set σ := (2 : ℝ) ^ ((1 : ℝ) / 2) with hσdef
  have hρ : ρ < 1 := two_rpow_neg_half_lt_one
  have hρ0 : 0 < ρ := two_rpow_neg_half_pos
  have hρσ : ρ * σ = 1 := two_rpow_neg_half_mul
  have hσsq : σ ^ 2 = 2 := two_rpow_half_sq
  have hσpos : 0 < σ := Real.rpow_pos_of_pos (by norm_num) _
  -- telescoping: `(Σ ρ^j)·(1−ρ) = 1 − ρ^k`.
  have hgeom : (∑ j ∈ Finset.range k, ρ ^ j) * (1 - ρ) = 1 - ρ ^ k := by
    have h := geom_sum_mul ρ k
    nlinarith [h]
  -- `1/(1−ρ) = 2+σ` since `(2+σ)(1−ρ) = 1`, using `σ = 2ρ` (which is
  -- `σ² = 2` times `ρσ = 1`).
  have hσ2ρ : σ = 2 * ρ := mul_right_cancel₀ hσpos.ne'
    (calc σ * σ = σ ^ 2 := by ring
      _ = 2 := hσsq
      _ = 2 * (ρ * σ) := by rw [hρσ]; norm_num
      _ = 2 * ρ * σ := by ring)
  have hkey : (2 + σ) * (1 - ρ) = 1 := by
    linear_combination hσ2ρ - hρσ
  have hnum : (∑ j ∈ Finset.range k, ρ ^ j) * (1 - ρ) ≤ 1 := by
    rw [hgeom]
    have hρk := pow_nonneg hρ0.le k
    linarith
  calc ∑ j ∈ Finset.range k, ρ ^ j
      = (∑ j ∈ Finset.range k, ρ ^ j) * (1 - ρ) * (2 + σ) := by
        rw [mul_assoc, mul_comm (1 - ρ) (2 + σ), hkey, mul_one]
    _ ≤ 1 * (2 + σ) :=
        mul_le_mul_of_nonneg_right hnum (by linarith [hσpos])
    _ = 2 + σ := one_mul _

/-- **The arithmetic step.**  With `ρ = 2^{−1/2}` and `σ = 2^{1/2}`,
`1 + Σ_{j<k} ρ^j ≤ σ^c` whenever `k + 1 ≤ c`.  Worst cases: `k = 0`
(`1 ≤ σ`), `k = 1` (`2 = σ²`), `k = 2` (`2 + ρ ≤ 2σ = σ³`, using
`σ ≤ 3/2`), `k = 3` (`5/2 + ρ ≤ 4 = σ⁴`), and `k ≥ 4` via the geometric
bound `1 + Σ ≤ 3 + σ ≤ 4σ = σ⁵`. -/
private theorem one_add_geom_le_sigma_pow {c k : ℕ} (hkc : k + 1 ≤ c) :
    (1 : ℝ) + ∑ j ∈ Finset.range k, ((2 : ℝ) ^ ((-1 : ℝ) / 2)) ^ j ≤
      ((2 : ℝ) ^ ((1 : ℝ) / 2)) ^ c := by
  set ρ := (2 : ℝ) ^ ((-1 : ℝ) / 2) with hρdef
  set σ := (2 : ℝ) ^ ((1 : ℝ) / 2) with hσdef
  have hσ1 : 1 ≤ σ := one_le_two_rpow_half
  have hσsq : σ ^ 2 = 2 := two_rpow_half_sq
  have hρσ : ρ * σ = 1 := two_rpow_neg_half_mul
  have hρle : ρ ≤ 1 := two_rpow_neg_half_lt_one.le
  have hρpos : 0 < ρ := two_rpow_neg_half_pos
  have hσpos : 0 < σ := Real.rpow_pos_of_pos (by norm_num) _
  have hσ3 : σ ^ 3 = 2 * σ := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, pow_add, hσsq, pow_one]
  have hσ4 : σ ^ 4 = 4 := by
    rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, hσsq]; norm_num
  have hσ5 : σ ^ 5 = 4 * σ := by
    rw [show (5 : ℕ) = 4 + 1 from rfl, pow_add, hσ4, pow_one]
  have hσle : σ ≤ 3 / 2 := two_rpow_half_le
  rcases lt_or_ge k 4 with hk | hk
  · interval_cases k
    · simp only [Finset.range_zero, Finset.sum_empty, add_zero]
      calc (1 : ℝ) ≤ σ := hσ1
        _ = σ ^ 1 := (pow_one σ).symm
        _ ≤ σ ^ c := pow_le_pow_right₀ hσ1 (by omega)
    · rw [Finset.sum_range_one, pow_zero]
      calc (1 : ℝ) + 1 = σ ^ 2 := by rw [hσsq]; norm_num
        _ ≤ σ ^ c := pow_le_pow_right₀ hσ1 (by omega)
    · rw [Finset.sum_range_succ, Finset.sum_range_one, pow_zero, pow_one]
      -- goal: `1 + (1 + ρ) ≤ σ ^ c`; `2 + ρ ≤ 2σ = σ³`.
      have key : (2 : ℝ) + ρ ≤ 2 * σ := by
        have h2 : (2 + ρ) * σ = 2 * σ + 1 := by
          linear_combination hρσ
        have h4 : (2 + ρ) * σ ≤ 2 * σ * σ := by
          rw [h2]
          nlinarith [hσsq, hσle, hσpos]
        exact le_of_mul_le_mul_right h4 hσpos
      calc (1 : ℝ) + (1 + ρ) = 2 + ρ := by ring
        _ ≤ 2 * σ := key
        _ = σ ^ 3 := hσ3.symm
        _ ≤ σ ^ c := pow_le_pow_right₀ hσ1 (by omega)
    · have e : ∑ j ∈ Finset.range 3, ρ ^ j = 1 + ρ + ρ ^ 2 := by
        rw [Finset.sum_range_succ, Finset.sum_range_succ,
          Finset.sum_range_one]
        ring
      rw [e]
      have hρ2 : ρ ^ 2 = 1 / 2 := two_rpow_neg_half_sq
      have key : (1 : ℝ) + (1 + ρ + ρ ^ 2) ≤ 4 := by
        linarith [hρ2, hρle]
      calc (1 : ℝ) + (1 + ρ + ρ ^ 2) ≤ 4 := key
        _ = σ ^ 4 := hσ4.symm
        _ ≤ σ ^ c := pow_le_pow_right₀ hσ1 (by omega)
  · -- `k ≥ 4`, so `c ≥ 5`: `1 + Σ ≤ 3 + σ ≤ 4σ = σ⁵ ≤ σ^c`.
    have h1 := sum_geom_le_two_add k
    rw [← hρdef, ← hσdef] at h1
    have h2 : σ ^ 5 ≤ σ ^ c := pow_le_pow_right₀ hσ1 (by omega)
    linarith

/-! ## The Hujter–Tuza bound -/

/-- **Hujter–Tuza bound.**  If `adj` is symmetric and triangle-free on
`B`, the number of maximal independent subsets of `B` is at most
`2^{|B|/2}` (looped vertices are simply never selected).

Induction on `|B|`.  If every vertex is looped the only maximal
independent set is `∅`.  Otherwise pick a non-looped `u` minimising
`c = |N[u]|`; the covering lemma splits maximal independent sets into a
`u`-fibre over `B ∖ N[u]` and, for each `w` in the non-looped open
neighbourhood `s` of `u`, a fibre over `B ∖ (N[w] ∪ s.filter (· < w))`.
Triangle-freeness forces `N[w] ∩ s.filter (· < w) = ∅`, so the `w`-fibre
loses `|N[w]| + rank(w) ≥ c + rank(w)` vertices, and `rank` is injective
on `s`. -/
theorem misCount_le_two_rpow_of_triangleFree (adj : ℤ → ℤ → Prop)
    (loop : ℤ → Prop) [DecidableRel adj] [DecidablePred loop]
    (hsymm : ∀ x y : ℤ, adj x y → adj y x) :
    ∀ n : ℕ, ∀ B : Finset ℤ, B.card ≤ n → triangleFree adj B →
      (misCount adj loop B : ℝ) ≤ (2 : ℝ) ^ ((B.card : ℝ) / 2) := by
  intro n
  induction n with
  | zero =>
    intro B hB _
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
    have hz : (0 : ℝ) ≤ ((∅ : Finset ℤ).card : ℝ) / 2 := by positivity
    exact_mod_cast Real.one_le_rpow (show (1 : ℝ) ≤ 2 by norm_num) hz
  | succ n ih =>
    intro B hB htri
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
      have hz : (0 : ℝ) ≤ (B.card : ℝ) / 2 := by positivity
      exact_mod_cast Real.one_le_rpow (show (1 : ℝ) ≤ 2 by norm_num) hz
    · -- some vertex is not looped; pick `u` minimising `|N[u]|`.
      push Not at hall
      obtain ⟨w₀, hwB, hwl⟩ := hall
      obtain ⟨u, huNL, humin⟩ := Finset.exists_min_image
        (B.filter (fun x => ¬ loop x)) (fun v => (nbd adj B v).card)
        ⟨w₀, Finset.mem_filter.mpr ⟨hwB, hwl⟩⟩
      rw [Finset.mem_filter] at huNL
      obtain ⟨huB, hul⟩ := huNL
      set s := openNbd adj loop B u with hsdef
      set c := (nbd adj B u).card with hcdef
      have huNu : u ∈ nbd adj B u :=
        Finset.mem_filter.mpr ⟨huB, Or.inl rfl⟩
      have hc1 : 1 ≤ c := Finset.card_pos.mpr ⟨u, huNu⟩
      have hcn : c ≤ B.card := Finset.card_le_card (Finset.filter_subset _ _)
      -- `|s| + 1 ≤ c` since `s ⊆ N[u] ∖ {u}`.
      have hcs : s.card + 1 ≤ c := by
        have h1 : s ⊆ (nbd adj B u).erase u := by
          intro y hy
          obtain ⟨hyB, hyu, hyadj, hyl⟩ := Finset.mem_filter.mp hy
          rw [Finset.mem_erase]
          exact ⟨hyu, Finset.mem_filter.mpr ⟨hyB, Or.inr hyadj⟩⟩
        have h2 := Finset.card_le_card h1
        rw [Finset.card_erase_of_mem huNu] at h2
        omega
      -- the covering bound, cast to `ℝ`.
      have cover := maxIndepSets_subset_leastNbd_cover hsymm huB hul
      rw [← hsdef] at cover
      have hcard : (misCount adj loop B : ℝ) ≤
          (misCount adj loop (B \ nbd adj B u) : ℝ) +
          ∑ w ∈ s, (misCount adj loop
            (B \ (nbd adj B w ∪ s.filter (· < w))) : ℝ) := by
        have h2 : (maxIndepSets adj loop B).card ≤
            (maxIndepSets adj loop (B \ nbd adj B u)).card +
            ∑ w ∈ s, (maxIndepSets adj loop
              (B \ (nbd adj B w ∪ s.filter (· < w)))).card := by
          refine le_trans (Finset.card_le_card cover) ?_
          refine le_trans (Finset.card_union_le _ _) ?_
          refine add_le_add Finset.card_image_le ?_
          exact le_trans Finset.card_biUnion_le
            (Finset.sum_le_sum fun w _ => Finset.card_image_le)
        simp only [misCount]
        exact_mod_cast h2
      -- the first fibre loses exactly `c` vertices.
      have hfirst : (misCount adj loop (B \ nbd adj B u) : ℝ) ≤
          (2 : ℝ) ^ (((B.card : ℝ) - c) / 2) := by
        have hcard1 : (B \ nbd adj B u).card = B.card - c :=
          Finset.card_sdiff_of_subset (Finset.filter_subset _ _)
        have hlen1 : (B \ nbd adj B u).card ≤ n := by rw [hcard1]; omega
        have hbound := ih _ hlen1 (htri.mono Finset.sdiff_subset)
        have hcast : ((B \ nbd adj B u).card : ℝ) = (B.card : ℝ) - c := by
          rw [hcard1]
          exact Nat.cast_sub hcn
        rw [hcast] at hbound
        exact hbound
      -- the `w`-fibre loses `|N[w]| + rank(w) ≥ c + rank(w)` vertices.
      have hterm : ∀ w ∈ s, (misCount adj loop
            (B \ (nbd adj B w ∪ s.filter (· < w))) : ℝ) ≤
          (2 : ℝ) ^ (((B.card : ℝ) - c -
            ((s.filter (· < w)).card : ℝ)) / 2) := by
        intro w hw
        obtain ⟨hwB, hwu, hwadj, hwl⟩ := Finset.mem_filter.mp hw
        -- `N[w] ∩ s.filter (· < w) = ∅`: a member `z` would close the
        -- triangle `u w z`.
        have hdisj : Disjoint (nbd adj B w) (s.filter (· < w)) := by
          rw [Finset.disjoint_left]
          intro z hzn hzL
          obtain ⟨hzs, hzw⟩ := Finset.mem_filter.mp hzL
          obtain ⟨hzB, hzu, hzadj, hzl⟩ := Finset.mem_filter.mp hzs
          obtain ⟨-, hzor⟩ := Finset.mem_filter.mp hzn
          rcases hzor with rfl | hadj
          · exact absurd hzw (lt_irrefl z)
          · exact htri z hzB w hwB u huB (ne_of_lt hzw) hwu hzu
              ⟨hsymm _ _ hadj, hsymm _ _ hwadj, hsymm _ _ hzadj⟩
        have hUsub : nbd adj B w ∪ s.filter (· < w) ⊆ B :=
          Finset.union_subset (Finset.filter_subset _ _)
            ((Finset.filter_subset _ _).trans (Finset.filter_subset _ _))
        have hcardU : (nbd adj B w ∪ s.filter (· < w)).card =
            (nbd adj B w).card + (s.filter (· < w)).card :=
          Finset.card_union_of_disjoint hdisj
        have hUle : (nbd adj B w).card + (s.filter (· < w)).card ≤
            B.card := hcardU ▸ Finset.card_le_card hUsub
        have hcw : c ≤ (nbd adj B w).card :=
          humin w (Finset.mem_filter.mpr ⟨hwB, hwl⟩)
        have hcardR : (B \ (nbd adj B w ∪ s.filter (· < w))).card =
            B.card - ((nbd adj B w).card + (s.filter (· < w)).card) := by
          rw [← hcardU]
          exact Finset.card_sdiff_of_subset hUsub
        have hlenR : (B \ (nbd adj B w ∪ s.filter (· < w))).card ≤ n := by
          have h1 : 1 ≤ (nbd adj B w).card + (s.filter (· < w)).card := by
            have h2 : 1 ≤ (nbd adj B w).card := Finset.card_pos.mpr
              ⟨w, Finset.mem_filter.mpr ⟨hwB, Or.inl rfl⟩⟩
            omega
          rw [hcardR]; omega
        have hbound := ih _ hlenR (htri.mono Finset.sdiff_subset)
        have hcast : ((B \ (nbd adj B w ∪ s.filter (· < w))).card : ℝ) =
            (B.card : ℝ) - (nbd adj B w).card -
              ((s.filter (· < w)).card : ℝ) := by
          rw [hcardR, Nat.cast_sub hUle]
          push_cast
          ring
        have hexp : ((B \ (nbd adj B w ∪ s.filter (· < w))).card : ℝ) ≤
            (B.card : ℝ) - c - ((s.filter (· < w)).card : ℝ) := by
          rw [hcast]
          have hcw' : (c : ℝ) ≤ ((nbd adj B w).card : ℝ) := by
            exact_mod_cast hcw
          linarith
        calc (misCount adj loop
                (B \ (nbd adj B w ∪ s.filter (· < w))) : ℝ)
            ≤ (2 : ℝ) ^ (((B \ (nbd adj B w ∪ s.filter (· < w))).card : ℝ)
                / 2) := hbound
          _ ≤ (2 : ℝ) ^ (((B.card : ℝ) - c -
                ((s.filter (· < w)).card : ℝ)) / 2) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
              (by linarith [hexp])
      -- `w ↦ |s.filter (· < w)|` is injective, so the `w`-sum is bounded
      -- by a geometric series over `range s.card`.
      have hrank : ∑ w ∈ s, ((2 : ℝ) ^ ((-1 : ℝ) / 2)) ^
              (s.filter (· < w)).card ≤
          ∑ j ∈ Finset.range s.card, ((2 : ℝ) ^ ((-1 : ℝ) / 2)) ^ j := by
        have hinj : ∀ a ∈ s, ∀ b ∈ s,
            (s.filter (· < a)).card = (s.filter (· < b)).card → a = b := by
          intro a ha b hb hab
          rcases lt_trichotomy a b with h | h | h
          · exfalso
            have hlt : (s.filter (· < a)).card <
                (s.filter (· < b)).card := by
              refine Finset.card_lt_card ?_
              rw [Finset.ssubset_iff_subset_ne]
              constructor
              · intro z hz
                rw [Finset.mem_filter] at hz ⊢
                exact ⟨hz.1, lt_trans hz.2 h⟩
              · intro heq
                have h1 : a ∈ s.filter (· < b) :=
                  Finset.mem_filter.mpr ⟨ha, h⟩
                have h2 : a ∈ s.filter (· < a) := heq.symm ▸ h1
                exact lt_irrefl _ (Finset.mem_filter.mp h2).2
            omega
          · exact h
          · exfalso
            have hlt : (s.filter (· < b)).card <
                (s.filter (· < a)).card := by
              refine Finset.card_lt_card ?_
              rw [Finset.ssubset_iff_subset_ne]
              constructor
              · intro z hz
                rw [Finset.mem_filter] at hz ⊢
                exact ⟨hz.1, lt_trans hz.2 h⟩
              · intro heq
                have h1 : b ∈ s.filter (· < a) :=
                  Finset.mem_filter.mpr ⟨hb, h⟩
                have h2 : b ∈ s.filter (· < b) := heq.symm ▸ h1
                exact lt_irrefl _ (Finset.mem_filter.mp h2).2
            omega
        rw [← Finset.sum_image hinj]
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun j _ _ =>
          pow_nonneg (Real.rpow_nonneg (by norm_num) _) _
        intro j hj
        rw [Finset.mem_image] at hj
        obtain ⟨w, hw, rfl⟩ := hj
        rw [Finset.mem_range]
        refine Finset.card_lt_card ?_
        rw [Finset.ssubset_iff_subset_ne]
        constructor
        · exact Finset.filter_subset _ _
        · intro heq
          have h1 : w ∈ s.filter (· < w) := heq.symm ▸ hw
          exact lt_irrefl _ (Finset.mem_filter.mp h1).2
      -- factoring out `2^{(N−c)/2}` and closing with `σ^c = 2^{c/2}`.
      have hfact : ∀ j : ℕ,
          (2 : ℝ) ^ (((B.card : ℝ) - c - (j : ℝ)) / 2) =
            (2 : ℝ) ^ (((B.card : ℝ) - c) / 2) *
              ((2 : ℝ) ^ ((-1 : ℝ) / 2)) ^ j := by
        intro j
        have e : ((B.card : ℝ) - c - j) / 2 =
            ((B.card : ℝ) - c) / 2 + (-(1 : ℝ) / 2) * j := by
          ring
        rw [e, Real.rpow_add (by norm_num : (0:ℝ) < 2)]
        congr 1
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
      have hsum_eq : ∑ w ∈ s,
            (2 : ℝ) ^ (((B.card : ℝ) - c -
              ((s.filter (· < w)).card : ℝ)) / 2) =
          (2 : ℝ) ^ (((B.card : ℝ) - c) / 2) *
            ∑ w ∈ s, ((2 : ℝ) ^ ((-1 : ℝ) / 2)) ^
              (s.filter (· < w)).card := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun w _ => hfact _
      have hfin : (2 : ℝ) ^ (((B.card : ℝ) - c) / 2) *
            ((2 : ℝ) ^ ((1 : ℝ) / 2)) ^ c =
          (2 : ℝ) ^ ((B.card : ℝ) / 2) := by
        rw [two_rpow_half_pow, ← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
        congr 1
        ring
      calc (misCount adj loop B : ℝ)
          ≤ (misCount adj loop (B \ nbd adj B u) : ℝ) +
            ∑ w ∈ s, (misCount adj loop
              (B \ (nbd adj B w ∪ s.filter (· < w))) : ℝ) := hcard
        _ ≤ (2 : ℝ) ^ (((B.card : ℝ) - c) / 2) +
            ∑ w ∈ s, (2 : ℝ) ^ (((B.card : ℝ) - c -
              ((s.filter (· < w)).card : ℝ)) / 2) :=
            add_le_add hfirst (Finset.sum_le_sum fun w hw => hterm w hw)
        _ = (2 : ℝ) ^ (((B.card : ℝ) - c) / 2) *
            (1 + ∑ w ∈ s,
              ((2 : ℝ) ^ ((-1 : ℝ) / 2)) ^ (s.filter (· < w)).card) := by
            rw [hsum_eq]; ring
        _ ≤ (2 : ℝ) ^ (((B.card : ℝ) - c) / 2) *
            ((2 : ℝ) ^ ((1 : ℝ) / 2)) ^ c := by
            refine mul_le_mul_of_nonneg_left ?_
              (Real.rpow_nonneg (by norm_num) _)
            exact le_trans (add_le_add le_rfl hrank)
              (one_add_geom_le_sigma_pow hcs)
        _ = (2 : ℝ) ^ ((B.card : ℝ) / 2) := hfin

/-! ## Transfer to the link graph -/

/-- **Hujter–Tuza for the link graph on the upper half**: for `S ⊆ [1, n]`
sum-free and `B` contained in `(n/2, ∞)`, the link graph on `B` is
triangle-free, so `|linkMaxSets S B| ≤ 2^{|B|/2}`. -/
theorem card_linkMaxSets_le_two_rpow {S B : Finset ℤ} {n : ℤ}
    (hS : S ⊆ Finset.Icc 1 n) (hSf : IsSumFree S)
    (hB : ∀ x ∈ B, n < 2 * x) :
    ((linkMaxSets S B).card : ℝ) ≤ (2 : ℝ) ^ ((B.card : ℝ) / 2) := by
  have hTF : triangleFree (linkAdj S) B := fun x hx y hy z hz hxy hyz hxz =>
    linkTriangleFree hS hSf hB x hx y hy z hz hxy hyz hxz
  have h := misCount_le_two_rpow_of_triangleFree (linkAdj S) (linkLoop S)
    (fun x y h => linkAdj_comm.mp h) B.card B le_rfl hTF
  simp only [misCount, maxIndepSets_link] at h
  exact h

/-- Integer form: `(misCount)² ≤ 2^{|B|}` for triangle-free `adj`. -/
theorem misCount_sq_le_two_pow_of_triangleFree {adj : ℤ → ℤ → Prop}
    {loop : ℤ → Prop} [DecidableRel adj] [DecidablePred loop]
    (hsymm : ∀ x y : ℤ, adj x y → adj y x)
    {B : Finset ℤ} (htri : triangleFree adj B) :
    (misCount adj loop B) ^ 2 ≤ 2 ^ B.card := by
  have h := misCount_le_two_rpow_of_triangleFree adj loop hsymm B.card B
    le_rfl htri
  have h2 : (misCount adj loop B : ℝ) ^ 2 ≤
      ((2 : ℝ) ^ ((B.card : ℝ) / 2)) ^ 2 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) h 2
  have e : ((2 : ℝ) ^ ((B.card : ℝ) / 2)) ^ 2 = (2 : ℝ) ^ B.card := by
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2),
      ← Real.rpow_natCast]
    congr 1
    push_cast
    ring
  rw [e] at h2
  exact_mod_cast h2

end JSP000728
