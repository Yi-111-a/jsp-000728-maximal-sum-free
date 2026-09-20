import JSPProblem.HujterTuza
import JSPProblem.FingerprintCount
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith

/-!
# JSP-000728 — the Sapozhenko almost-regular MIS bound

BLST15 Lemma 2.7 / BLST18 Lemma 3.4: if `adj` is a symmetric adjacency on a
vertex set `B` whose degrees all lie in `[δ, Δ]` with `Δ ≤ k·δ` and `δ` large,
then the number of maximal independent subsets of `B` is at most
`3^{(k/(k+1) + o(1))·|B|/3}` — beating the Moon–Moser bound `3^{|B|/3}`.

**The mechanism.**  Set `b ≈ √δ`.  For each maximal independent set `I`,
greedily peel vertices `v ∈ I` whose degree into the remaining vertex set is
at least `b`, removing the whole closed neighbourhood `N_B[v]` each time.
Each step removes `≥ b` fresh vertices, so at most `|B|/b` vertices of `I`
are peeled; the unpeeled part `I ∖ R` (with `R = ⋃_{v ∈ F} N_B[v]`) lies in

  `Z = {w ∈ U : deg_{G[U]}(w) < b}`   (`U = B ∖ R`).

Every `x ∈ Z ∖ (I ∖ R)` is dominated by `I`, and its dominator cannot be a
peeled vertex (that would put `x` in a removed neighbourhood), so `I ∖ R` is
a *maximal* independent set of `G[Z]`.  Double-counting degrees gives

  `δ·|Z| ≤ Σ_{v ∈ Z} deg_B(v) ≤ b·|Z| + Δ·(|B| − |Z|)`,

hence `(δ + Δ − b)·|Z| ≤ Δ·|B|`.  Finally `I` is determined by the peeled set
`F = I ∩ R` (at most `Σ_{i ≤ |B|/b} C(|B|, i)` possibilities) together with a
maximal independent set of `Z`, so

  `mis(G) ≤ #{F ⊆ B : b·|F| ≤ |B|} · 3^{Δ|B|/(3(δ+Δ−b))}`.

## Main declarations

* `degIn adj B v` — the number of `adj`-neighbours of `v` in `B`;
* `peel_exists` — the greedy peeling construction;
* `lowdegRemainder` — the set `Z` described above;
* `card_lowdeg_le` — `(δ + Δ − b)·|Z| ≤ Δ·|B|`;
* `maxIndepSets_subset_biUnion_peel` — the `(F, J)`-covering;
* `misCount_le_card_mul_three_rpow` — the explicit Sapozhenko bound;
* `misCount_le_rpow_mul_three_rpow` — the same with the fingerprint count
  bounded by `(2·e·b)^{|B|/b}`;
* `exists_misCount_le_three_rpow_of_almostRegular` — the eventual form:
  for fixed `k, ε` and `δ` large enough, degrees in `[δ, kδ]` imply
  `misCount ≤ 3^{(k/(k+1) + ε)·|B|/3}`.
-/

namespace JSP000728

/-- The (open) degree of `v` inside `B`: the number of `adj`-neighbours of
`v` in `B` (`v` itself is counted when `adj v v` holds). -/
def degIn (adj : ℤ → ℤ → Prop) [DecidableRel adj] (B : Finset ℤ) (v : ℤ) : ℕ :=
  (B.filter (adj v)).card

theorem degIn_mono {adj : ℤ → ℤ → Prop} [DecidableRel adj]
    {C B : Finset ℤ} (h : C ⊆ B) (v : ℤ) : degIn adj C v ≤ degIn adj B v := by
  apply Finset.card_le_card
  intro y hy
  rw [Finset.mem_filter] at hy ⊢
  exact ⟨h hy.1, hy.2⟩

/-- The degree of `v` in `X` is a lower bound for `|X ∩ N_B[v]|`: every
`adj`-neighbour of `v` in `X` lies in the closed `B`-neighbourhood. -/
theorem degIn_le_card_inter_nbd {adj : ℤ → ℤ → Prop} [DecidableRel adj]
    {X B : Finset ℤ} (hXB : X ⊆ B) (v : ℤ) :
    degIn adj X v ≤ (X ∩ nbd adj B v).card := by
  apply Finset.card_le_card
  intro y hy
  rw [Finset.mem_filter] at hy
  exact Finset.mem_inter.mpr
    ⟨hy.1, Finset.mem_filter.mpr ⟨hXB hy.1, Or.inr hy.2⟩⟩

/-! ## The peeling construction -/

/-- **Greedy peeling.**  Starting from `X ⊆ B` and `I ⊆ X`, repeatedly remove
`N_B[v]` for some `v ∈ I` whose `X`-degree is at least `b`.  The resulting set
`F` of peeled vertices satisfies `b·|F| ≤ |X ∩ ⋃_{v ∈ F} N_B[v]|` (each step
contributes `≥ b` fresh vertices), and every remaining `w ∈ I` outside the
removed region has `X ∖ ⋃`-degree `< b`.

Induction on `|X|`: if some `v ∈ I` has `X`-degree `≥ b`, recurse on
`X ∖ N_B[v]` and `I ∖ N_B[v]` and adjoin `v`; otherwise `F = ∅` works. -/
theorem peel_exists (adj : ℤ → ℤ → Prop) [DecidableRel adj]
    (B : Finset ℤ) (b : ℕ) :
    ∀ n : ℕ, ∀ X I : Finset ℤ, X.card ≤ n → X ⊆ B → I ⊆ X →
      ∃ F : Finset ℤ, F ⊆ I ∧
        b * F.card ≤ (X ∩ F.biUnion (nbd adj B)).card ∧
        ∀ w ∈ I, w ∉ F.biUnion (nbd adj B) →
          ((X \ F.biUnion (nbd adj B)).filter (adj w)).card < b := by
  intro n
  induction n with
  | zero =>
    intro X I hX hXB hIX
    rw [Nat.le_zero, Finset.card_eq_zero] at hX
    subst hX
    refine ⟨∅, Finset.empty_subset _, by simp, ?_⟩
    intro w hwI _
    exact absurd (hIX hwI) (Finset.notMem_empty w)
  | succ n ih =>
    intro X I hX hXB hIX
    by_cases hex : ∃ v ∈ I, b ≤ (X.filter (adj v)).card
    · obtain ⟨v, hvI, hvb⟩ := hex
      have hvX : v ∈ X := hIX hvI
      have hvB : v ∈ B := hXB hvX
      have hvN : v ∈ nbd adj B v := Finset.mem_filter.mpr ⟨hvB, Or.inl rfl⟩
      -- the recursive call shrinks `X`, since `v ∈ X ∩ N_B[v]`.
      have hX'lt : (X \ nbd adj B v).card < X.card := by
        refine Finset.card_lt_card ?_
        rw [Finset.ssubset_iff_subset_ne]
        refine ⟨Finset.sdiff_subset, fun heq => ?_⟩
        rw [← heq] at hvX
        exact absurd hvN (Finset.mem_sdiff.mp hvX).2
      have hI' : I \ nbd adj B v ⊆ X \ nbd adj B v :=
        Finset.sdiff_subset_sdiff hIX (Finset.Subset.refl _)
      obtain ⟨F', hF'I, hcard', hstop'⟩ := ih (X \ nbd adj B v)
        (I \ nbd adj B v) (by omega) (Finset.sdiff_subset.trans hXB) hI'
      have hvF' : v ∉ F' := fun hv =>
        (Finset.mem_sdiff.mp (hF'I hv)).2 hvN
      refine ⟨insert v F',
        Finset.insert_subset hvI (hF'I.trans Finset.sdiff_subset), ?_, ?_⟩
      · rw [Finset.card_insert_of_notMem hvF', Finset.biUnion_insert]
        have hge : b ≤ (X ∩ nbd adj B v).card :=
          hvb.trans (degIn_le_card_inter_nbd hXB v)
        have hdisj : Disjoint (X ∩ nbd adj B v)
            (X \ nbd adj B v ∩ F'.biUnion (nbd adj B)) := by
          rw [Finset.disjoint_left]
          intro y hy hy2
          exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp hy2).1).2
            (Finset.mem_inter.mp hy).2
        have hsub : (X ∩ nbd adj B v) ∪
            (X \ nbd adj B v ∩ F'.biUnion (nbd adj B)) ⊆
            X ∩ (nbd adj B v ∪ F'.biUnion (nbd adj B)) := by
          intro y hy
          rw [Finset.mem_union] at hy
          rcases hy with hy | hy
          · obtain ⟨hyX, hyN⟩ := Finset.mem_inter.mp hy
            exact Finset.mem_inter.mpr ⟨hyX, Finset.mem_union.mpr (Or.inl hyN)⟩
          · obtain ⟨hyX', hyR⟩ := Finset.mem_inter.mp hy
            exact Finset.mem_inter.mpr
              ⟨(Finset.mem_sdiff.mp hyX').1, Finset.mem_union.mpr (Or.inr hyR)⟩
        calc b * (F'.card + 1) = b * F'.card + b := by ring
          _ ≤ (X \ nbd adj B v ∩ F'.biUnion (nbd adj B)).card +
              (X ∩ nbd adj B v).card :=
              Nat.add_le_add hcard' hge
          _ = (X ∩ nbd adj B v).card +
              (X \ nbd adj B v ∩ F'.biUnion (nbd adj B)).card :=
              Nat.add_comm _ _
          _ = ((X ∩ nbd adj B v) ∪
                (X \ nbd adj B v ∩ F'.biUnion (nbd adj B))).card :=
              (Finset.card_union_of_disjoint hdisj).symm
          _ ≤ (X ∩ (nbd adj B v ∪ F'.biUnion (nbd adj B))).card :=
              Finset.card_le_card hsub
      · intro w hwI hwR
        rw [Finset.biUnion_insert] at hwR ⊢
        rw [Finset.mem_union] at hwR
        push Not at hwR
        obtain ⟨hwN, hwR'⟩ := hwR
        have hwI' : w ∈ I \ nbd adj B v := Finset.mem_sdiff.mpr ⟨hwI, hwN⟩
        have h := hstop' w hwI' hwR'
        have heq : (X \ nbd adj B v) \ F'.biUnion (nbd adj B) =
            X \ (nbd adj B v ∪ F'.biUnion (nbd adj B)) := by
          ext y
          simp only [Finset.mem_sdiff, Finset.mem_union]
          constructor
          · rintro ⟨⟨hX, hN⟩, hR'⟩
            exact ⟨hX, not_or.mpr ⟨hN, hR'⟩⟩
          · rintro ⟨hX, hNR'⟩
            obtain ⟨hN, hR'⟩ := not_or.mp hNR'
            exact ⟨⟨hX, hN⟩, hR'⟩
        rwa [heq] at h
    · push Not at hex
      refine ⟨∅, Finset.empty_subset _, by simp, ?_⟩
      intro w hwI _
      simpa only [Finset.biUnion_empty, Finset.sdiff_empty] using hex w hwI

/-! ## The low-degree remainder -/

/-- **The low-degree remainder.**  With `U = B ∖ ⋃_{v ∈ F} N_B[v]` the vertex
set left after peeling `F`, this is `Z = {w ∈ U : deg_U(w) < b}` — the part
of `B` in which every unpeeled vertex of a maximal independent set must
land. -/
def lowdegRemainder (adj : ℤ → ℤ → Prop) [DecidableRel adj] (B : Finset ℤ)
    (b : ℕ) (F : Finset ℤ) : Finset ℤ :=
  (B \ F.biUnion (nbd adj B)).filter fun w =>
    ((B \ F.biUnion (nbd adj B)).filter (adj w)).card < b

/-- **Degree double-count.**  For `Z` the low-degree vertices of `U ⊆ B`,
`δ·|Z| ≤ Σ_{v ∈ Z} deg_B(v) = Σ_{v ∈ Z} deg_Z(v) + e(Z, B ∖ Z)`, where the
first sum is at most `b·|Z|` (each `deg_Z ≤ deg_U < b`) and the second —
counted from the `B ∖ Z` side using symmetry of `adj` — at most
`Δ·|B ∖ Z|`.  Rearranged: `(δ + Δ − b)·|Z| ≤ Δ·|B|`. -/
theorem card_lowdeg_le (adj : ℤ → ℤ → Prop) [DecidableRel adj]
    (hsymm : ∀ x y : ℤ, adj x y → adj y x)
    {B U : Finset ℤ} (hUB : U ⊆ B) (b : ℕ) {δ Δ : ℝ}
    (hδ : ∀ v ∈ B, δ ≤ (degIn adj B v : ℝ))
    (hΔ : ∀ v ∈ B, (degIn adj B v : ℝ) ≤ Δ) :
    (δ + Δ - b) *
        ((U.filter fun w => degIn adj U w < b).card : ℝ) ≤ Δ * B.card := by
  set Z := U.filter fun w => degIn adj U w < b with hZdef
  have hZU : Z ⊆ U := Finset.filter_subset _ _
  have hZB : Z ⊆ B := hZU.trans hUB
  -- lower bound: each `v ∈ Z ⊆ B` has `deg_B(v) ≥ δ`.
  have hlow : δ * Z.card ≤ ∑ v ∈ Z, (degIn adj B v : ℝ) := by
    rw [show δ * (Z.card : ℝ) = ∑ _v ∈ Z, δ by
      rw [Finset.sum_const, nsmul_eq_mul]; ring]
    exact Finset.sum_le_sum fun v hv => hδ v (hZB hv)
  -- split `deg_B(v) = deg_Z(v) + deg_{B∖Z}(v)` along `B = Z ∪ (B ∖ Z)`.
  have hsplit : ∀ v ∈ Z, (degIn adj B v : ℝ) =
      degIn adj Z v + degIn adj (B \ Z) v := by
    intro v hv
    have hunion : Z ∪ B \ Z = B := Finset.union_sdiff_of_subset hZB
    have hBU : B.filter (adj v) =
        Z.filter (adj v) ∪ (B \ Z).filter (adj v) := by
      conv_lhs => rw [← hunion]
      rw [Finset.filter_union]
    have hdisj : Disjoint (Z.filter (adj v)) ((B \ Z).filter (adj v)) := by
      rw [Finset.disjoint_left]
      intro y hy1 hy2
      exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hy2).1).2
        (Finset.mem_filter.mp hy1).1
    have hnat : degIn adj B v = degIn adj Z v + degIn adj (B \ Z) v := by
      unfold degIn
      rw [hBU, Finset.card_union_of_disjoint hdisj]
    exact_mod_cast hnat
  -- `Σ_{v ∈ Z} deg_Z(v) ≤ b·|Z|` since `deg_Z(v) ≤ deg_U(v) < b`.
  have hsumZ : ∑ v ∈ Z, (degIn adj Z v : ℝ) ≤ b * Z.card := by
    calc ∑ v ∈ Z, (degIn adj Z v : ℝ)
        ≤ ∑ v ∈ Z, (degIn adj U v : ℝ) :=
          Finset.sum_le_sum fun v _ =>
            Nat.cast_le.mpr (degIn_mono hZU _)
      _ ≤ ∑ v ∈ Z, (b : ℝ) :=
          Finset.sum_le_sum fun v hv =>
            (Nat.cast_le.mpr (Finset.mem_filter.mp hv).2.le)
      _ = b * Z.card := by rw [Finset.sum_const, nsmul_eq_mul]; ring
  -- `Σ_{v ∈ Z} deg_{B∖Z}(v) = Σ_{w ∈ B∖Z} deg_Z(w) ≤ Δ·|B ∖ Z|`.
  have hcross : ∑ v ∈ Z, (degIn adj (B \ Z) v : ℝ) ≤ Δ * (B \ Z).card := by
    have hnat : ∑ v ∈ Z, ((B \ Z).filter (adj v)).card =
        ∑ w ∈ B \ Z, (Z.filter (adj w)).card := by
      simp_rw [Finset.card_filter]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun v _ => ?_
      by_cases h : adj v w
      · have h' : adj w v := hsymm _ _ h
        simp [h, h']
      · have h' : ¬ adj w v := fun hwv => h (hsymm _ _ hwv)
        simp [h, h']
    have heq : ∑ v ∈ Z, (degIn adj (B \ Z) v : ℝ) =
        ∑ w ∈ B \ Z, (degIn adj Z w : ℝ) := by
      exact_mod_cast hnat
    calc ∑ v ∈ Z, (degIn adj (B \ Z) v : ℝ)
        = ∑ w ∈ B \ Z, (degIn adj Z w : ℝ) := heq
      _ ≤ ∑ w ∈ B \ Z, (degIn adj B w : ℝ) :=
          Finset.sum_le_sum fun w _ =>
            Nat.cast_le.mpr (degIn_mono hZB _)
      _ ≤ ∑ w ∈ B \ Z, Δ :=
          Finset.sum_le_sum fun w hw =>
            hΔ w (Finset.mem_sdiff.mp hw).1
      _ = Δ * (B \ Z).card := by rw [Finset.sum_const, nsmul_eq_mul]; ring
  -- combine: `δ|Z| ≤ b|Z| + Δ(|B| − |Z|)`.
  have hmain : δ * Z.card ≤ b * Z.card + Δ * (B \ Z).card := by
    calc δ * Z.card ≤ ∑ v ∈ Z, (degIn adj B v : ℝ) := hlow
      _ = ∑ v ∈ Z, (degIn adj Z v + degIn adj (B \ Z) v : ℝ) :=
          Finset.sum_congr rfl hsplit
      _ = ∑ v ∈ Z, (degIn adj Z v : ℝ) + ∑ v ∈ Z, (degIn adj (B \ Z) v : ℝ) :=
          Finset.sum_add_distrib
      _ ≤ b * Z.card + Δ * (B \ Z).card := add_le_add hsumZ hcross
  have hcard : ((B \ Z).card : ℝ) = B.card - Z.card := by
    rw [Finset.card_sdiff_of_subset hZB]
    exact Nat.cast_sub (Finset.card_le_card hZB)
  rw [hcard] at hmain
  linarith

/-- The real-valued form: `|Z| ≤ Δ·|B| / (δ + Δ − b)`. -/
theorem card_lowdeg_le_div (adj : ℤ → ℤ → Prop) [DecidableRel adj]
    (hsymm : ∀ x y : ℤ, adj x y → adj y x)
    {B U : Finset ℤ} (hUB : U ⊆ B) (b : ℕ) {δ Δ : ℝ}
    (hpos : (0 : ℝ) < δ + Δ - b)
    (hδ : ∀ v ∈ B, δ ≤ (degIn adj B v : ℝ))
    (hΔ : ∀ v ∈ B, (degIn adj B v : ℝ) ≤ Δ) :
    ((U.filter fun w => degIn adj U w < b).card : ℝ) ≤
      Δ * B.card / (δ + Δ - b) := by
  rw [le_div_iff₀ hpos, mul_comm]
  exact card_lowdeg_le adj hsymm hUB b hδ hΔ

/-! ## The covering -/

/-- **Covering by peeled sets.**  Every maximal independent subset `t` of `B`
is `F ∪ J` where `F = t ∩ ⋃ N_B[F]` is the peeled part (`b·|F| ≤ |B|`) and
`J = t ∖ ⋃ N_B[F]` is a maximal independent subset of the low-degree
remainder `Z_F`.

Maximality of `J`: a vertex `x ∈ Z ∖ J` is dominated by some `y ∈ t`; `y`
cannot be peeled (otherwise `x ∈ N_B[y]` would be removed), so `y ∈ J`. -/
theorem maxIndepSets_subset_biUnion_peel {adj : ℤ → ℤ → Prop}
    {loop : ℤ → Prop} [DecidableRel adj] [DecidablePred loop]
    (hsymm : ∀ x y : ℤ, adj x y → adj y x)
    (B : Finset ℤ) (b : ℕ) :
    maxIndepSets adj loop B ⊆
      (B.powerset.filter fun F => b * F.card ≤ B.card).biUnion fun F =>
        (maxIndepSets adj loop (lowdegRemainder adj B b F)).image (F ∪ ·) := by
  intro t ht
  rw [mem_maxIndepSets] at ht
  obtain ⟨htB, hti, htm⟩ := ht
  obtain ⟨F, hFt, hcard, hstop⟩ :=
    peel_exists adj B b B.card B t le_rfl (Finset.Subset.refl B) htB
  set R := F.biUnion (nbd adj B) with hRdef
  -- `t ∩ R = F`: a `t`-element of `N_B[v]` with `v ∈ F ⊆ t` equals `v`
  -- (independence rules out `adj v y`).
  have htR : t ∩ R = F := by
    apply Finset.Subset.antisymm
    · intro y hy
      obtain ⟨hyt, hyR⟩ := Finset.mem_inter.mp hy
      obtain ⟨v, hvF, hvN⟩ := Finset.mem_biUnion.mp hyR
      obtain ⟨-, hveq⟩ := Finset.mem_filter.mp hvN
      rcases hveq with rfl | hadj
      · exact hvF
      · exact (hti.2 v (hFt hvF) y hyt hadj).elim
    · intro y hyF
      exact Finset.mem_inter.mpr ⟨hFt hyF, Finset.mem_biUnion.mpr
        ⟨y, hyF, Finset.mem_filter.mpr ⟨htB (hFt hyF), Or.inl rfl⟩⟩⟩
  have ht_eq : F ∪ t \ R = t := by
    ext y
    rw [Finset.mem_union, Finset.mem_sdiff]
    constructor
    · rintro (hy | ⟨hy, -⟩)
      · exact hFt hy
      · exact hy
    · intro hy
      by_cases hyR : y ∈ R
      · have hmem : y ∈ t ∩ R := Finset.mem_inter.mpr ⟨hy, hyR⟩
        exact Or.inl (htR ▸ hmem)
      · exact Or.inr ⟨hy, hyR⟩
  have hJ : maxIndepSet adj loop (lowdegRemainder adj B b F) (t \ R) := by
    refine ⟨?_, ⟨?_, ?_⟩, ?_⟩
    · -- `t ∖ R ⊆ Z`: unpeeled `t`-vertices have `U`-degree `< b`.
      intro y hy
      obtain ⟨hyt, hyR⟩ := Finset.mem_sdiff.mp hy
      rw [lowdegRemainder, Finset.mem_filter]
      exact ⟨Finset.mem_sdiff.mpr ⟨htB hyt, hyR⟩, hstop y hyt hyR⟩
    · intro x hx
      exact hti.1 x (Finset.mem_sdiff.mp hx).1
    · intro x hx y hy
      exact hti.2 x (Finset.mem_sdiff.mp hx).1
        y (Finset.mem_sdiff.mp hy).1
    · intro x hxZ hxJ
      obtain ⟨hxU, -⟩ := Finset.mem_filter.mp hxZ
      obtain ⟨hxB, hxR⟩ := Finset.mem_sdiff.mp hxU
      have hxt : x ∉ t := fun h => hxJ (Finset.mem_sdiff.mpr ⟨h, hxR⟩)
      rcases htm x hxB hxt with hl | ⟨y, hyt, hyadj⟩
      · exact Or.inl hl
      · refine Or.inr ⟨y, Finset.mem_sdiff.mpr ⟨hyt, fun hyR => ?_⟩, hyadj⟩
        -- `y ∈ R` forces `y ∈ F`, so `adj x y` puts `x ∈ N_B[y] ⊆ R`.
        have hmem : y ∈ t ∩ R := Finset.mem_inter.mpr ⟨hyt, hyR⟩
        have hyF : y ∈ F := htR ▸ hmem
        exact hxR (Finset.mem_biUnion.mpr
          ⟨y, hyF, Finset.mem_filter.mpr ⟨hxB, Or.inr (hsymm x y hyadj)⟩⟩)
  rw [Finset.mem_biUnion]
  refine ⟨F, Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr (hFt.trans htB), ?_⟩, ?_⟩
  · exact hcard.trans (Finset.card_le_card Finset.inter_subset_left)
  · rw [Finset.mem_image]
    exact ⟨t \ R, mem_maxIndepSets.mpr hJ, ht_eq⟩

/-! ## The counting bounds -/

/-- **Sapozhenko bound, fingerprint × Moon–Moser form.**  Under degree
bounds `δ ≤ deg_B(v) ≤ Δ` on `B`, every maximal independent set splits as a
peeled part `F` (at most `|B|/b` elements) and a maximal independent set of
`Z_F` with `|Z_F| ≤ Δ|B|/(δ + Δ − b)`. -/
theorem misCount_le_card_mul_three_rpow (adj : ℤ → ℤ → Prop)
    (loop : ℤ → Prop) [DecidableRel adj] [DecidablePred loop]
    (hsymm : ∀ x y : ℤ, adj x y → adj y x)
    (B : Finset ℤ) (b : ℕ) {δ Δ : ℝ}
    (hpos : (0 : ℝ) < δ + Δ - b)
    (hδ : ∀ v ∈ B, δ ≤ (degIn adj B v : ℝ))
    (hΔ : ∀ v ∈ B, (degIn adj B v : ℝ) ≤ Δ) :
    (misCount adj loop B : ℝ) ≤
      ((B.powerset.filter fun F => b * F.card ≤ B.card).card : ℝ) *
        (3 : ℝ) ^ (Δ * B.card / (δ + Δ - b) / 3) := by
  have hM : ∀ F : Finset ℤ,
      ((lowdegRemainder adj B b F).card : ℝ) ≤
        Δ * B.card / (δ + Δ - b) := by
    intro F
    exact card_lowdeg_le_div adj hsymm
      (B := B) (U := B \ F.biUnion (nbd adj B)) Finset.sdiff_subset b
      hpos hδ hΔ
  have hsum : (misCount adj loop B : ℝ) ≤
      ∑ F ∈ B.powerset.filter (fun F => b * F.card ≤ B.card),
        (misCount adj loop (lowdegRemainder adj B b F) : ℝ) := by
    have hnat : misCount adj loop B ≤
        ∑ F ∈ B.powerset.filter (fun F => b * F.card ≤ B.card),
          misCount adj loop (lowdegRemainder adj B b F) := by
      refine (Finset.card_le_card
        (maxIndepSets_subset_biUnion_peel hsymm B b)).trans ?_
      refine Finset.card_biUnion_le.trans ?_
      exact Finset.sum_le_sum fun F _ => Finset.card_image_le
    exact_mod_cast hnat
  calc (misCount adj loop B : ℝ)
      ≤ ∑ F ∈ B.powerset.filter (fun F => b * F.card ≤ B.card),
          (misCount adj loop (lowdegRemainder adj B b F) : ℝ) := hsum
    _ ≤ ∑ F ∈ B.powerset.filter (fun F => b * F.card ≤ B.card),
          (3 : ℝ) ^ (((lowdegRemainder adj B b F).card : ℝ) / 3) :=
        Finset.sum_le_sum fun F _ =>
          misCount_le_three_rpow adj loop hsymm _ _ le_rfl
    _ ≤ ∑ F ∈ B.powerset.filter (fun F => b * F.card ≤ B.card),
          (3 : ℝ) ^ (Δ * B.card / (δ + Δ - b) / 3) :=
        Finset.sum_le_sum fun F _ =>
          Real.rpow_le_rpow_of_exponent_le (by norm_num)
            (by linarith [hM F])
    _ = (B.powerset.filter fun F => b * F.card ≤ B.card).card *
          (3 : ℝ) ^ (Δ * B.card / (δ + Δ - b) / 3) := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-- The peeled part has at most `|B| / b` elements, so its count is at most
`Σ_{i ≤ |B|/b} C(|B|, i)`. -/
theorem card_powerset_filter_mul_card_le_choose (B : Finset ℤ) {b : ℕ}
    (hb : 0 < b) :
    (B.powerset.filter fun F => b * F.card ≤ B.card).card ≤
      ∑ i ∈ Finset.range (B.card / b + 1), Nat.choose B.card i := by
  have hfilter : B.powerset.filter (fun F => b * F.card ≤ B.card) =
      B.powerset.filter (fun F => F.card ≤ B.card / b) := by
    refine Finset.filter_congr fun F _ => ?_
    rw [Nat.le_div_iff_mul_le hb, Nat.mul_comm]
  rw [hfilter]
  exact card_powerset_filter_card_le B (B.card / b)

/-- Entropy form: the fingerprint count is at most `(2·e·b)^{|B|/b}` for
`b ≥ 1`. -/
theorem card_powerset_filter_mul_card_le_rpow (B : Finset ℤ) {b : ℕ}
    (hb : 1 ≤ b) :
    ((B.powerset.filter fun F => b * F.card ≤ B.card).card : ℝ) ≤
      (2 * Real.exp 1 * b) ^ ((B.card : ℝ) / b) := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hbase1 : (1 : ℝ) ≤ 2 * Real.exp 1 * b := by
    have he : (2 : ℝ) ≤ Real.exp 1 := by
      have h := Real.add_one_le_exp (1 : ℝ)
      linarith
    have hb1R : (1 : ℝ) ≤ b := by exact_mod_cast hb
    have h4 : (4 : ℝ) ≤ 2 * Real.exp 1 * b := by
      have := mul_le_mul (by linarith : (4 : ℝ) ≤ 2 * Real.exp 1) hb1R
        zero_le_one (by linarith : (0 : ℝ) ≤ 2 * Real.exp 1)
      simpa using this
    linarith
  have hfilter : B.powerset.filter (fun F => b * F.card ≤ B.card) =
      B.powerset.filter (fun F => F.card ≤ B.card / b) := by
    refine Finset.filter_congr fun F _ => ?_
    rw [Nat.le_div_iff_mul_le (by omega : 0 < b), Nat.mul_comm]
  rw [hfilter]
  have hle : ((B.powerset.filter fun F => F.card ≤ B.card / b).card : ℝ) ≤
      ∑ i ∈ Finset.range (B.card / b + 1), (Nat.choose B.card i : ℝ) := by
    have h := card_powerset_filter_card_le B (B.card / b)
    exact_mod_cast h
  rcases Nat.eq_zero_or_pos (B.card / b) with hm | hm
  · -- `B.card / b = 0`: the sum is `C(N,0) = 1 ≤ (2eb)^{N/b}`.
    rw [hm] at hle ⊢
    rw [Finset.sum_range_one, Nat.choose_zero_right, Nat.cast_one] at hle
    refine hle.trans ?_
    exact Real.one_le_rpow hbase1 (by positivity)
  · have hmn : B.card / b ≤ B.card := Nat.div_le_self _ _
    have hmR : (0 : ℝ) < ((B.card / b : ℕ) : ℝ) := by exact_mod_cast hm
    have hNle : (B.card : ℝ) ≤ b * ((B.card / b : ℕ) + 1) := by
      have h := Nat.lt_mul_div_succ B.card (by omega : 0 < b)
      have h' : (B.card : ℝ) < b * ((B.card / b : ℕ) + 1) := by
        exact_mod_cast h
      linarith
    have hbm : (b : ℝ) ≤ b * ((B.card / b : ℕ) : ℝ) := by
      have h1 : (1 : ℝ) ≤ ((B.card / b : ℕ) : ℝ) := by exact_mod_cast hm
      calc (b : ℝ) = b * 1 := by ring
        _ ≤ b * ((B.card / b : ℕ) : ℝ) :=
            mul_le_mul_of_nonneg_left h1 hbR.le
    have hbnd : (B.card : ℝ) * Real.exp 1 / ((B.card / b : ℕ) : ℝ) ≤
        2 * Real.exp 1 * b := by
      have h1 : (B.card : ℝ) / ((B.card / b : ℕ) : ℝ) ≤ 2 * b := by
        rw [div_le_iff₀ hmR]
        calc (B.card : ℝ) ≤ b * ((B.card / b : ℕ) + 1) := hNle
          _ = b * ((B.card / b : ℕ) : ℝ) + b := by ring
          _ ≤ b * ((B.card / b : ℕ) : ℝ) + b * ((B.card / b : ℕ) : ℝ) := by
              linarith [hbm]
          _ = 2 * b * ((B.card / b : ℕ) : ℝ) := by ring
      calc (B.card : ℝ) * Real.exp 1 / ((B.card / b : ℕ) : ℝ)
          = ((B.card : ℝ) / ((B.card / b : ℕ) : ℝ)) * Real.exp 1 := by
            rw [mul_div_right_comm]
        _ ≤ 2 * b * Real.exp 1 :=
            mul_le_mul_of_nonneg_right h1 (Real.exp_pos 1).le
        _ = 2 * Real.exp 1 * b := by ring
    have hbase0 : (0 : ℝ) ≤
        (B.card : ℝ) * Real.exp 1 / ((B.card / b : ℕ) : ℝ) := by
      positivity
    calc ((B.powerset.filter fun F => F.card ≤ B.card / b).card : ℝ)
        ≤ ∑ i ∈ Finset.range (B.card / b + 1), (Nat.choose B.card i : ℝ) :=
          hle
      _ ≤ ((B.card : ℝ) * Real.exp 1 / ((B.card / b : ℕ) : ℝ)) ^
            (B.card / b) := sum_choose_le_exp_mul_pow hm hmn
      _ ≤ (2 * Real.exp 1 * b) ^ (B.card / b) :=
          pow_le_pow_left₀ hbase0 hbnd _
      _ = (2 * Real.exp 1 * b : ℝ) ^ (((B.card / b : ℕ)) : ℝ) := by
          rw [Real.rpow_natCast]
      _ ≤ (2 * Real.exp 1 * b : ℝ) ^ ((B.card : ℝ) / b) :=
          Real.rpow_le_rpow_of_exponent_le hbase1 Nat.cast_div_le

/-- **Sapozhenko bound, explicit form.**  Under `δ ≤ deg_B ≤ Δ` with
`b < δ + Δ` and `b ≥ 1`,
`mis(G) ≤ (2·e·b)^{|B|/b} · 3^{Δ·|B| / (3(δ + Δ − b))}`. -/
theorem misCount_le_rpow_mul_three_rpow (adj : ℤ → ℤ → Prop)
    (loop : ℤ → Prop) [DecidableRel adj] [DecidablePred loop]
    (hsymm : ∀ x y : ℤ, adj x y → adj y x)
    (B : Finset ℤ) (b : ℕ) {δ Δ : ℝ}
    (hb : 1 ≤ b) (hpos : (0 : ℝ) < δ + Δ - b)
    (hδ : ∀ v ∈ B, δ ≤ (degIn adj B v : ℝ))
    (hΔ : ∀ v ∈ B, (degIn adj B v : ℝ) ≤ Δ) :
    (misCount adj loop B : ℝ) ≤
      (2 * Real.exp 1 * b) ^ ((B.card : ℝ) / b) *
        (3 : ℝ) ^ (Δ * B.card / (δ + Δ - b) / 3) :=
  (misCount_le_card_mul_three_rpow adj loop hsymm B b hpos hδ hΔ).trans
    (mul_le_mul_of_nonneg_right (card_powerset_filter_mul_card_le_rpow B hb)
      (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _))

/-- Specialised to `Δ = k·δ`. -/
theorem misCount_le_rpow_mul_three_rpow_of_le (adj : ℤ → ℤ → Prop)
    (loop : ℤ → Prop) [DecidableRel adj] [DecidablePred loop]
    (hsymm : ∀ x y : ℤ, adj x y → adj y x)
    (B : Finset ℤ) (b : ℕ) {k δ : ℝ}
    (hb : 1 ≤ b) (hpos : (0 : ℝ) < δ + k * δ - b)
    (hδ : ∀ v ∈ B, δ ≤ (degIn adj B v : ℝ))
    (hΔ : ∀ v ∈ B, (degIn adj B v : ℝ) ≤ k * δ) :
    (misCount adj loop B : ℝ) ≤
      (2 * Real.exp 1 * b) ^ ((B.card : ℝ) / b) *
        (3 : ℝ) ^ (k * δ * B.card / (δ + k * δ - b) / 3) :=
  misCount_le_rpow_mul_three_rpow adj loop hsymm B b hb hpos hδ hΔ

/-! ## The eventual (asymptotic) form -/

/-- Auxiliary real-arithmetic estimate: `log(2·e·b) ≤ 2 + 2·√b` for `b ≥ 1`.
From `log(2e) ≤ 2` and `log b = 2 log √b ≤ 2(√b − 1) ≤ 2√b`. -/
theorem log_two_e_mul_le (b : ℕ) (hb : 1 ≤ b) :
    Real.log (2 * Real.exp 1 * b) ≤ 2 + 2 * Real.sqrt b := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have h1 : Real.log (2 * Real.exp 1 * b) =
      Real.log (2 * Real.exp 1) + Real.log b :=
    Real.log_mul (by positivity : (2 * Real.exp 1 : ℝ) ≠ 0) hbR.ne'
  have h2 : Real.log (2 * Real.exp 1) = Real.log 2 + 1 := by
    rw [Real.log_mul two_ne_zero (Real.exp_pos 1).ne', Real.log_exp]
  have h3 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith
  have h4 : Real.log b ≤ 2 * Real.sqrt b := by
    have hsqrt : 0 < Real.sqrt b := Real.sqrt_pos.mpr hbR
    have h5 := Real.log_le_sub_one_of_pos hsqrt
    rw [Real.log_sqrt hbR.le] at h5
    linarith
  rw [h1, h2]
  linarith

/-- If `√b ≥ 2/c + 1` for `c > 0`, then `2 + 2√b ≤ c·b`. -/
theorem two_add_two_sqrt_le {c : ℝ} (hc : 0 < c) {b : ℝ}
    (hb : (2 / c + 1) ^ 2 ≤ b) : 2 + 2 * Real.sqrt b ≤ c * b := by
  have h2c : (0 : ℝ) < 2 / c + 1 := by positivity
  have hb0 : (0 : ℝ) ≤ b := (sq_nonneg _).trans hb
  have hsqrt : 2 / c + 1 ≤ Real.sqrt b := by
    rw [← Real.sqrt_sq h2c.le]
    exact Real.sqrt_le_sqrt hb
  have hcb : c * Real.sqrt b ≥ c * (2 / c + 1) :=
    mul_le_mul_of_nonneg_left hsqrt hc.le
  have key : c * (2 / c + 1) = 2 + c := by field_simp
  have hcsqrt : c * Real.sqrt b ≥ 2 := by linarith
  nlinarith [hsqrt, hcb, key, Real.sq_sqrt hb0]

/-- **Sapozhenko-type almost-regular MIS bound, eventual form.**  For fixed
`k > 0` and `ε > 0`, once `δ` is large enough, every symmetric adjacency
whose `B`-degrees all lie in `[δ, k·δ]` satisfies
`misCount adj loop B ≤ 3^{(k/(k+1) + ε)·|B|/3}`.

The proof peels with `b = ⌊√δ⌋`: the fingerprint factor
`(2·e·b)^{|B|/b}` is `≤ 3^{(ε/2)·|B|/3}` for `b` large (since
`log b = o(b)`), and `Δ·|B|/(δ + Δ − b) ≤ (k/(k+1) + ε/2)·|B|` once
`b/δ` is small. -/
theorem exists_misCount_le_three_rpow_of_almostRegular {k ε : ℝ}
    (hk : 0 < k) (hε : 0 < ε) :
    ∃ δ₀ : ℝ, ∀ (adj : ℤ → ℤ → Prop) (loop : ℤ → Prop) [DecidableRel adj]
        [DecidablePred loop], (∀ x y : ℤ, adj x y → adj y x) →
      ∀ (B : Finset ℤ) (δ : ℝ),
        δ₀ ≤ δ →
        (∀ v ∈ B, δ ≤ (degIn adj B v : ℝ)) →
        (∀ v ∈ B, (degIn adj B v : ℝ) ≤ k * δ) →
        (misCount adj loop B : ℝ) ≤
          (3 : ℝ) ^ ((k / (k + 1) + ε) * B.card / 3) := by
  have hlog3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have hk1 : (0 : ℝ) < k + 1 := by linarith
  have heps : (0 : ℝ) < ε / 2 := by linarith
  -- `c` is the allowed log-cost per unit `b`; `C₁` is the `b`-threshold making
  -- `log(2eb) ≤ c·b`, `C₂` the `√δ`-threshold making
  -- `kδ/((k+1)δ − b) ≤ k/(k+1) + ε/2`.
  set c := ε * Real.log 3 / 6 with hcdef
  have hc : 0 < c := by positivity
  set C₁ := (2 / c + 1) ^ 2 with hC₁def
  set C₂ := (k / (k + 1) + ε / 2) / ((ε / 2) * (k + 1)) with hC₂def
  have hC₁ : 1 ≤ C₁ := by
    have h1 : (0 : ℝ) < 2 / c := by positivity
    rw [hC₁def]
    calc (1 : ℝ) = 1 ^ 2 := (one_pow 2).symm
      _ ≤ (2 / c + 1) ^ 2 := pow_le_pow_left₀ zero_le_one (by linarith) 2
  have hC₂pos : (0 : ℝ) < C₂ := by
    rw [hC₂def]
    have hnum : (0 : ℝ) < k / (k + 1) + ε / 2 := by
      have : (0 : ℝ) ≤ k / (k + 1) := div_nonneg hk.le hk1.le
      linarith
    exact div_pos hnum (mul_pos heps hk1)
  refine ⟨(C₁ + C₂ + 2) ^ 2, ?_⟩
  intro adj loop _ _ hsymm B δ hδ₀ hδ hΔ
  set b := ⌊Real.sqrt δ⌋₊ with hbdef
  have hδ₀pos : (0 : ℝ) < (C₁ + C₂ + 2) ^ 2 := by positivity
  have hδpos : 0 < δ := hδ₀pos.trans_le hδ₀
  have hsqrtδ : C₁ + C₂ + 2 ≤ Real.sqrt δ := by
    have h1 : Real.sqrt ((C₁ + C₂ + 2) ^ 2) ≤ Real.sqrt δ :=
      Real.sqrt_le_sqrt hδ₀
    rwa [Real.sqrt_sq (by linarith : (0:ℝ) ≤ C₁ + C₂ + 2)] at h1
  have hb_ge : C₁ + C₂ + 1 ≤ (b : ℝ) := by
    have h := Nat.lt_floor_add_one (Real.sqrt δ)
    linarith
  have hb_le : (b : ℝ) ≤ Real.sqrt δ :=
    Nat.floor_le (Real.sqrt_nonneg δ)
  have hC1_le : (C₁ : ℝ) ≤ b := by linarith
  have hb1 : 1 ≤ b := by
    have h : (1 : ℝ) ≤ b := by linarith
    exact_mod_cast h
  have hδ1 : (1 : ℝ) ≤ δ := by
    have hge : (1 : ℝ) ≤ (C₁ + C₂ + 2) ^ 2 := by
      have h0 : (0 : ℝ) ≤ C₁ + C₂ + 2 := by linarith
      calc (1 : ℝ) = 1 ^ 2 := (one_pow 2).symm
        _ ≤ (C₁ + C₂ + 2) ^ 2 :=
          pow_le_pow_left₀ zero_le_one (by linarith) 2
    exact hge.trans hδ₀
  have hsqrtδ_le : Real.sqrt δ ≤ δ := by
    have hsqrt1 : (1 : ℝ) ≤ Real.sqrt δ := by
      rw [Real.le_sqrt zero_le_one hδpos.le, one_pow]
      exact hδ1
    calc Real.sqrt δ ≤ Real.sqrt δ * Real.sqrt δ :=
          le_mul_of_one_le_left (Real.sqrt_nonneg δ) hsqrt1
      _ = δ := Real.mul_self_sqrt hδpos.le
  -- positivity of the reduced denominator `(k+1)δ − b`
  have hk1δ : (0:ℝ) < δ + k * δ - b := by
    have hkδ : 0 < k * δ := mul_pos hk hδpos
    nlinarith [hb_le, hsqrtδ_le]
  have hmain := misCount_le_rpow_mul_three_rpow_of_le adj loop hsymm B b
    (k := k) (δ := δ) hb1 hk1δ hδ hΔ
  -- fingerprint factor ≤ `3^{ε·n/6}`
  have hfinger : (2 * Real.exp 1 * b : ℝ) ^ ((B.card : ℝ) / b) ≤
      (3 : ℝ) ^ (ε * B.card / 6) := by
    have hbpos : (0:ℝ) < b := by exact_mod_cast hb1
    have hbne : (b : ℝ) ≠ 0 := hbpos.ne'
    have hbase : (0:ℝ) < 2 * Real.exp 1 * b := by positivity
    have hlog : Real.log (2 * Real.exp 1 * b) ≤ c * b := by
      refine (log_two_e_mul_le b hb1).trans ?_
      exact two_add_two_sqrt_le hc (hC₁def ▸ hC1_le)
    have hlogb : Real.logb 3 (2 * Real.exp 1 * b) ≤ ε * b / 6 := by
      rw [show Real.logb 3 (2 * Real.exp 1 * b) =
          Real.log (2 * Real.exp 1 * b) / Real.log 3 from rfl]
      rw [div_le_iff₀ hlog3]
      rw [show ε * b / 6 * Real.log 3 = c * b by rw [hcdef]; ring]
      exact hlog
    calc (2 * Real.exp 1 * b : ℝ) ^ ((B.card : ℝ) / b)
        = ((3 : ℝ) ^ Real.logb 3 (2 * Real.exp 1 * b)) ^
            ((B.card : ℝ) / b) := by
          rw [Real.rpow_logb (by norm_num) (by norm_num) hbase]
      _ = (3 : ℝ) ^ (Real.logb 3 (2 * Real.exp 1 * b) * (B.card / b)) := by
          rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 3)]
      _ ≤ (3 : ℝ) ^ (ε * B.card / 6) := by
          apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 3)
          have hnb : (0:ℝ) ≤ (B.card : ℝ) / b := by positivity
          calc Real.logb 3 (2 * Real.exp 1 * b) * (B.card / b)
              ≤ (ε * b / 6) * (B.card / b) :=
                mul_le_mul_of_nonneg_right hlogb hnb
            _ = ε * B.card / 6 := by field_simp
  -- the `Z`-factor ≤ `3^{(k/(k+1) + ε/2)·n/3}`
  have hZ : (3 : ℝ) ^ (k * δ * B.card / (δ + k * δ - b) / 3) ≤
      (3 : ℝ) ^ ((k / (k + 1) + ε / 2) * B.card / 3) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 3)
    have hB0 : (0:ℝ) ≤ B.card := Nat.cast_nonneg _
    have hC₂δ : C₂ ≤ Real.sqrt δ := by linarith [hsqrtδ]
    have hsqrt_lb : (k / (k + 1) + ε / 2) ≤
        (ε / 2) * (k + 1) * Real.sqrt δ := by
      have h1 : C₂ * ((ε / 2) * (k + 1)) = k / (k + 1) + ε / 2 := by
        rw [hC₂def]
        exact div_mul_cancel₀ _ (mul_pos heps hk1).ne'
      calc k / (k + 1) + ε / 2 = C₂ * ((ε / 2) * (k + 1)) := h1.symm
        _ ≤ Real.sqrt δ * ((ε / 2) * (k + 1)) :=
            mul_le_mul_of_nonneg_right hC₂δ (mul_pos heps hk1).le
        _ = (ε / 2) * (k + 1) * Real.sqrt δ := by ring
    have hkey : (k / (k + 1) + ε / 2) * (b : ℝ) ≤ (ε / 2) * (k + 1) * δ := by
      have hnn : (0:ℝ) ≤ k / (k + 1) + ε / 2 := by
        have h1 : (0:ℝ) ≤ k / (k + 1) := div_nonneg hk.le hk1.le
        linarith
      have h2 : (k / (k + 1) + ε / 2) * Real.sqrt δ ≤
          (ε / 2) * (k + 1) * δ := by
        calc (k / (k + 1) + ε / 2) * Real.sqrt δ
            ≤ (ε / 2) * (k + 1) * Real.sqrt δ * Real.sqrt δ :=
              mul_le_mul_of_nonneg_right hsqrt_lb (Real.sqrt_nonneg δ)
          _ = (ε / 2) * (k + 1) * δ := by
              linear_combination
                (ε / 2 * (k + 1)) * Real.mul_self_sqrt hδpos.le
      exact (mul_le_mul_of_nonneg_left hb_le hnn).trans h2
    -- main division bound `kδ/((k+1)δ−b) ≤ k/(k+1) + ε/2`
    have hfrac : k * δ / (δ + k * δ - b) ≤ k / (k + 1) + ε / 2 := by
      rw [div_le_iff₀ hk1δ]
      have hk1ne : (k + 1 : ℝ) ≠ 0 := hk1.ne'
      have hexpand : (k / (k + 1) + ε / 2) * (δ + k * δ - b) =
          k * δ + (ε / 2) * (k + 1) * δ - (k / (k + 1) + ε / 2) * b := by
        field_simp
        ring
      rw [hexpand]
      linarith [hkey]
    have h2 : k * δ * B.card / (δ + k * δ - b) =
        (k * δ / (δ + k * δ - b)) * B.card := by ring
    rw [h2]
    have h3 := mul_le_mul_of_nonneg_right hfrac hB0
    linarith [h3]
  -- combine
  calc (misCount adj loop B : ℝ)
      ≤ (2 * Real.exp 1 * b) ^ ((B.card : ℝ) / b) *
          (3 : ℝ) ^ (k * δ * B.card / (δ + k * δ - b) / 3) := hmain
    _ ≤ (3 : ℝ) ^ (ε * B.card / 6) *
          (3 : ℝ) ^ ((k / (k + 1) + ε / 2) * B.card / 3) :=
        mul_le_mul hfinger hZ (Real.rpow_nonneg (by norm_num) _)
          (Real.rpow_nonneg (by norm_num) _)
    _ = (3 : ℝ) ^ ((k / (k + 1) + ε) * B.card / 3) := by
        rw [← Real.rpow_add (by norm_num : (0:ℝ) < 3)]
        congr 1
        ring

end JSP000728
