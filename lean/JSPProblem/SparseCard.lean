import JSPProblem.Supersaturation
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Tactic.Linarith

/-!
# JSP-000728 — sparse containers have at most `(1/2 + o(1))·n` elements

The "size" half of the BLST18 stability analysis, proved here **without** the
Schur removal lemma.  The argument is an elementary record-level
(first-passage) count.

For `C ⊆ {1,…,n}` consider the walk `E(t) = 2·|C ∩ [1,t]| − t` on
`t ∈ {0,…,n}`.  It starts at `0`, moves by `±1` per step, and ends at
`2·|C| − n`.  Let `t_j` be the first time it reaches level `j ≥ 1`
(`j ≤ 2·|C| − n`).  Then `t_j ∈ C` (the last step is `+1`), `E(t_j) = j`
exactly, and inclusion–exclusion on the fiber `{x ∈ C : t_j − x ∈ C}` gives

  `r(t_j) ≥ 2·|C ∩ [1, t_j − 1]| − (t_j − 1) = E(t_j) − 1 = j − 1`.

The `t_j` are distinct, so summing over `j = 1,…,J` with `J = 2·|C| − n`,

  `schurTripleCount C ≥ ∑_{j=1}^{J} (j − 1) = J·(J−1)/2`

(`two_mul_schurTripleCount_ge_of_card`).  Consequently
`schurTripleCount C ≤ δ·n²` with `δ = ε²` forces `2·|C| − n ≤ 2ε·n + O(1)`,
i.e. `|C| ≤ (1/2 + ε)·n` for all large `n`
(`card_le_half_add_of_schurTripleCount_le`) — the removal-free size bound
needed by the container method.
-/

namespace JSP000728

/-- **Record-level supersaturation.**  If `C ⊆ {1,…,n}` satisfies
`n + J ≤ 2·|C|` then `J·(J−1) ≤ 2·schurTripleCount C`: the `J` record
passages of the walk `2·|C ∩ [1,t]| − t` occur at elements of `C`, and the
`j`-th contributes at least `j − 1` Schur triples. -/
theorem two_mul_schurTripleCount_ge_of_card {n : ℕ} {C : Finset ℤ}
    (hsub : C ⊆ interval n) {J : ℕ} (hJ : n + J ≤ 2 * C.card) :
    J * (J - 1) ≤ 2 * schurTripleCount C := by
  classical
  -- `S j` = first-passage candidates: times `t ≤ n` with `2·|C∩[1,t]| − t ≥ j`.
  set S : ℕ → Finset ℕ := fun j => (Finset.range (n + 1)).filter
    fun t => (j : ℤ) ≤ 2 * ((C ∩ Finset.Icc 1 (t : ℤ)).card : ℤ) - (t : ℤ)
    with hS
  have hSmem : ∀ {j t : ℕ}, t ∈ S j ↔
      t < n + 1 ∧ (j : ℤ) ≤ 2 * ((C ∩ Finset.Icc 1 (t : ℤ)).card : ℤ)
        - (t : ℤ) := by
    intro j t
    simp only [hS, Finset.mem_filter, Finset.mem_range]
  have hmem : ∀ j ∈ Finset.Icc 1 J, n ∈ S j := by
    intro j hj
    have hjJ : j ≤ J := (Finset.mem_Icc.mp hj).2
    have han : C ∩ Finset.Icc 1 (n : ℤ) = C := Finset.inter_eq_left.mpr hsub
    refine hSmem.mpr ⟨Nat.lt_succ_self n, ?_⟩
    have hcard : ((C ∩ Finset.Icc 1 (n : ℤ)).card : ℤ) = C.card := by rw [han]
    omega
  -- For each `j ∈ [1,J]`, the first passage time `t j` to level `j`.
  have key : ∀ j : ℕ, ∃ tj : ℕ, j ∈ Finset.Icc 1 J →
      1 ≤ tj ∧ tj ≤ n ∧ ((tj : ℤ) ∈ C) ∧
        (2 * ((C ∩ Finset.Icc 1 (tj : ℤ)).card : ℤ) - (tj : ℤ) = (j : ℤ)) ∧
        (j - 1 ≤ (C.filter fun x => (tj : ℤ) - x ∈ C).card) := by
    intro j
    by_cases hj : j ∈ Finset.Icc 1 J
    · obtain ⟨hj1, -⟩ := Finset.mem_Icc.mp hj
      have hne : (S j).Nonempty := ⟨n, hmem j hj⟩
      refine ⟨(S j).min' hne, fun _ => ?_⟩
      have hmtj : (S j).min' hne ∈ S j := (S j).min'_mem hne
      obtain ⟨hltn, hge⟩ := hSmem.mp hmtj
      -- The first passage time is positive.
      have htpos : 1 ≤ (S j).min' hne := by
        rcases Nat.eq_zero_or_pos ((S j).min' hne) with h0 | h0
        · exfalso
          have ha0 : C ∩ Finset.Icc 1 ((0 : ℕ) : ℤ) = ∅ := by
            apply Finset.eq_empty_of_forall_notMem
            intro x hx
            obtain ⟨hxC, hxI⟩ := Finset.mem_inter.mp hx
            have hx1 : 1 ≤ x := (Finset.mem_Icc.mp (hsub hxC)).1
            obtain ⟨-, hx0⟩ := Finset.mem_Icc.mp hxI
            simp only [Nat.cast_zero] at hx0
            omega
          rw [h0] at hge
          rw [ha0, Finset.card_empty] at hge
          simp only [Nat.cast_zero, mul_zero, sub_zero] at hge
          omega
        · exact h0
      have hcast : (((S j).min' hne - 1 : ℕ) : ℤ) = ((S j).min' hne : ℤ) - 1 := by
        rw [Nat.cast_sub htpos, Nat.cast_one]
      -- Minimality: the predecessor does not reach level `j`.
      have hmin : 2 * ((C ∩ Finset.Icc 1
            (((S j).min' hne - 1 : ℕ) : ℤ)).card : ℤ)
          - (((S j).min' hne - 1 : ℕ) : ℤ) < (j : ℤ) := by
        by_contra hcon
        rw [not_lt] at hcon
        have hm2 : (S j).min' hne - 1 ∈ S j :=
          hSmem.mpr ⟨by omega, hcon⟩
        have hle : (S j).min' hne ≤ (S j).min' hne - 1 :=
          Finset.min'_le _ _ hm2
        omega
      -- The walk step: `a(t) = a(t−1) + [t ∈ C]`.
      have hstep : (C ∩ Finset.Icc 1 ((S j).min' hne : ℤ)).card
          = (C ∩ Finset.Icc 1 (((S j).min' hne - 1 : ℕ) : ℤ)).card
            + (if (((S j).min' hne : ℤ)) ∈ C then 1 else 0) := by
        have hicc : Finset.Icc (1 : ℤ) ((S j).min' hne : ℤ)
            = insert ((S j).min' hne : ℤ)
              (Finset.Icc (1 : ℤ) (((S j).min' hne - 1 : ℕ) : ℤ)) := by
          ext x
          simp only [Finset.mem_Icc, Finset.mem_insert]
          rw [hcast]
          omega
        rw [hicc]
        by_cases hmemC : (((S j).min' hne : ℤ) ∈ C)
        · have hnot : ((S j).min' hne : ℤ)
              ∉ C ∩ Finset.Icc 1 (((S j).min' hne - 1 : ℕ) : ℤ) := by
            intro hbad
            obtain ⟨-, hle⟩ :=
              Finset.mem_Icc.mp (Finset.mem_inter.mp hbad).2
            rw [hcast] at hle
            omega
          rw [Finset.inter_insert_of_mem hmemC,
            Finset.card_insert_of_notMem hnot]
          simp [hmemC]
        · rw [Finset.inter_insert_of_notMem hmemC]
          simp [hmemC]
      -- Since `E(t_j) ≥ j` but `E(t_j − 1) < j`, the step must be `+1`.
      have hmemC : (((S j).min' hne : ℤ)) ∈ C := by
        by_contra hnc
        have hst : (C ∩ Finset.Icc 1 ((S j).min' hne : ℤ)).card
            = (C ∩ Finset.Icc 1 (((S j).min' hne - 1 : ℕ) : ℤ)).card := by
          rw [hstep]; simp [hnc]
        omega
      have hst : (C ∩ Finset.Icc 1 ((S j).min' hne : ℤ)).card
          = (C ∩ Finset.Icc 1 (((S j).min' hne - 1 : ℕ) : ℤ)).card + 1 := by
        rw [hstep]; simp [hmemC]
      have hEj : 2 * ((C ∩ Finset.Icc 1 ((S j).min' hne : ℤ)).card : ℤ)
          - ((S j).min' hne : ℤ) = (j : ℤ) := by
        omega
      -- The fiber bound at `t_j`: `r(t_j) ≥ 2·a(t_j − 1) − (t_j − 1) = j − 1`.
      have hfib : j - 1
          ≤ (C.filter fun x => (((S j).min' hne : ℤ)) - x ∈ C).card := by
        have h0 := card_filter_sub_mem_ge C ((S j).min' hne : ℤ)
        rw [← hcast, Int.toNat_natCast] at h0
        omega
      exact ⟨htpos, by omega, hmemC, hEj, hfib⟩
    · exact ⟨0, fun h => absurd h hj⟩
  choose t ht using key
  -- `t` maps the levels `1,…,J` injectively into `C`.
  have hinj : Set.InjOn (fun j => ((t j : ℤ))) ↑(Finset.Icc 1 J) := by
    intro j hj k hk hjk
    simp only [Finset.mem_coe] at hj hk
    obtain ⟨-, -, -, hEj, -⟩ := ht j hj
    obtain ⟨-, -, -, hEk, -⟩ := ht k hk
    have hjk' : (t j : ℤ) = (t k : ℤ) := hjk
    have htk : t j = t k := by exact_mod_cast hjk'
    have hje : (j : ℤ) = (k : ℤ) := by rw [← hEj, htk, hEk]
    exact_mod_cast hje
  have himage : (Finset.Icc 1 J).image (fun j => ((t j : ℤ))) ⊆ C := by
    intro z hz
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hz
    exact (ht j hj).2.2.1
  -- Summing the fiber bounds over the `J` record elements.
  have hsumle : (∑ j ∈ Finset.Icc 1 J,
      (C.filter fun x => ((t j : ℤ)) - x ∈ C).card) ≤ schurTripleCount C := by
    calc (∑ j ∈ Finset.Icc 1 J,
          (C.filter fun x => ((t j : ℤ)) - x ∈ C).card)
        = ∑ z ∈ (Finset.Icc 1 J).image (fun j => ((t j : ℤ))),
            (C.filter fun x => z - x ∈ C).card :=
          (Finset.sum_image
            (f := fun z => (C.filter fun x => z - x ∈ C).card)
            (g := fun j => ((t j : ℤ))) hinj).symm
      _ ≤ ∑ z ∈ C, (C.filter fun x => z - x ∈ C).card :=
          Finset.sum_le_sum_of_subset_of_nonneg himage
            (fun z _ _ => Nat.zero_le _)
      _ = schurTripleCount C := (schurTripleCount_eq_sum_filter C).symm
  have hsumge : (∑ j ∈ Finset.Icc 1 J, (j - 1)) ≤
      (∑ j ∈ Finset.Icc 1 J,
        (C.filter fun x => ((t j : ℤ)) - x ∈ C).card) :=
    Finset.sum_le_sum fun j hj => (ht j hj).2.2.2.2
  have hsumid : (∑ j ∈ Finset.Icc 1 J, (j - 1)) = ∑ i ∈ Finset.range J, i := by
    have hIco : Finset.Icc 1 J = Finset.Ico 1 (J + 1) := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_Ico]
      omega
    rw [hIco, Finset.sum_Ico_eq_sum_range]
    simp
  have h2 := Finset.sum_range_id_mul_two J
  omega

/-- **Sparse ⇒ small.**  For every `ε > 0` there is `δ > 0` such that,
eventually, every `C ⊆ {1,…,n}` with at most `δ·n²` Schur triples satisfies
`|C| ≤ (1/2 + ε)·n`.  This is the size component of the BLST18 stability
lemma; unlike the removal-lemma route it is fully elementary. -/
theorem card_le_half_add_of_schurTripleCount_le {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n : ℕ in Filter.atTop,
      ∀ C : Finset ℤ, C ⊆ interval n →
        (schurTripleCount C : ℝ) ≤ δ * (n : ℝ) ^ 2 →
        (C.card : ℝ) ≤ (1 / 2 + ε) * (n : ℝ) := by
  refine ⟨ε ^ 2, by positivity, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop ⌈2 / ε⌉₊] with n hn
  intro C hsub htri
  by_contra hlt
  rw [not_le] at hlt
  -- `J = 2·|C| − n ≥ 1`, and `(J : ℝ) > 2εn`.
  set J : ℕ := 2 * C.card - n with hJdef
  have hlt2 : n < 2 * C.card := by
    have h : (n : ℝ) < 2 * (C.card : ℝ) := by
      linarith [hlt, mul_nonneg hε.le (Nat.cast_nonneg n)]
    exact_mod_cast h
  have hJpos : 1 ≤ J := by omega
  have hJJ : n + J ≤ 2 * C.card := by omega
  have hT := two_mul_schurTripleCount_ge_of_card hsub hJJ
  -- Real-valued version of the record bound.
  have hTR : (J : ℝ) * ((J : ℝ) - 1) ≤ 2 * (schurTripleCount C : ℝ) := by
    have h : ((J * (J - 1) : ℕ) : ℝ) ≤ ((2 * schurTripleCount C : ℕ) : ℝ) := by
      exact_mod_cast hT
    rwa [Nat.cast_mul, Nat.cast_sub hJpos, Nat.cast_one, Nat.cast_mul,
      Nat.cast_ofNat] at h
  have hJR : (J : ℝ) = 2 * (C.card : ℝ) - (n : ℝ) := by
    have hle : n ≤ 2 * C.card := hlt2.le
    rw [hJdef, Nat.cast_sub hle]
    push_cast
    ring
  have hJgt : 2 * ε * (n : ℝ) < (J : ℝ) := by linarith [hlt, hJR]
  -- `ε·n ≥ 2` since `n ≥ ⌈2/ε⌉`.
  have hen : (2 : ℝ) ≤ ε * (n : ℝ) := by
    have h1 : (2 / ε : ℝ) ≤ ⌈2 / ε⌉₊ := Nat.le_ceil _
    have h2 : (⌈(2 / ε : ℝ)⌉₊ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have h3 : (2 : ℝ) ≤ (n : ℝ) * ε := (div_le_iff₀ hε).mp (h1.trans h2)
    rwa [mul_comm] at h3
  -- Hence `J(J−1) > 2ε²n² ≥ 2·schurTripleCount C`, contradicting `hTR`.
  have haux : (0 : ℝ) < (J : ℝ) + 2 * ε * (n : ℝ) - 1 := by
    linarith [hJgt, hen]
  have hprod : 2 * ε ^ 2 * (n : ℝ) ^ 2 < (J : ℝ) * ((J : ℝ) - 1) := by
    nlinarith [hJgt, hen, mul_pos (sub_pos.mpr hJgt) haux]
  linarith [hTR, hprod, htri]

end JSP000728
