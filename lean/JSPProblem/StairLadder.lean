import JSPProblem.Ladder
import JSPProblem.TwoMin
import JSPProblem.NoConsec
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# JSP-000728 — the "staircase" ladder for mod-`m` diagonal pairing

For `1 ≤ m < s ≤ 3m/2` the mod-`m` residue classes `cls n m r` carry a
different constraint shape than the mod-`s` rails of `PairRails.lean`:
the `m`-shift is *vertical* (rail-internal, `x ↦ x + m` stays on rail `r`
at level `+1`) while the `s`-shift is *diagonal* — an element
`x = r + m + m·j` of rail `r` maps to
`x + s = (r + s - m) + m + m·(j+1)`, i.e. rail `r + (s - m)` at level
`+1`.  Pairing the mod-`m` rails `{r, r + s - m}` for `r ∈ Icc 1 (s - m)`
covers `Icc 1 (2(s - m))`; the leftover `Icc (2(s - m) + 1) m` has
`3m - 2s` rails and is empty at `s = 3m/2`.

The resulting independent-set graph on `Bool × range L` (rail
`false`/`true`, level `j`) has

* verticals on both rails — `(b, j)` and `(b, j+1)` not both present;
* ascending diagonal rungs only — `(false, j)` and `(true, j+1)` not
  both present (the `s`-edges out of rail `true` leave the pair and are
  harmlessly dropped, as is the wrap-around edge `s = 3m/2` would add).

This is the *staircase* graph `stairSets L`, counted by

  `a(0) = 1`, `a(1) = 4`, `a(2) = 8`,
  `a(L+3) = a(L+2) + 3·a(L+1) + a(L)`

(sequence `1, 4, 8, 21, 49, …`; the growth rate is the root
`ρ ≈ 2.4115` of `ρ³ = ρ² + 3ρ + 1`, per-vertex `√ρ ≈ 1.5529` — a hair
below the ladder rate `√(1+√2) ≈ 1.5538`).

* `stairVert L`, `stairFree t`, `stairSets L` : vertices, predicate,
  family, mirroring `ladVert`/`ladFree`/`ladSets`.
* `stairAvoidF L` : stair-free sets avoiding `(false, L-1)` — exactly
  those extendable by `(false, L)`.  `stairAvoidE L` : sets with empty
  last column — extendable by `(true, L)` and by the pair
  `{(false, L), (true, L)}`.
* `stairSets_card_succ` : `a(L+1) = a(L) + α(L) + 2·ε(L)`;
  `stairAvoidF_card_succ` : `α(L+1) = a(L) + ε(L)`;
  `stairAvoidE_succ` : `stairAvoidE (L+1) = stairSets L`, i.e.
  `ε(L+1) = a(L)`.  Together they give `stairSets_card_add_three`.
* `stairSets_card_mul_two_pow_le` : `a(L)·2^{L-1} ≤ 4·5^{L-1}` for
  `1 ≤ L`, i.e. `a(L) ≤ 4·(5/2)^{L-1}` (the three-step induction gives
  `2·200 + 12·20 + 8·4 = 472 ≤ 500`); `stairSets_card_le_four_mul_five_pow`.
* `stairIdx` + `card_powerset_filter_shiftFree2_modm_pair_cls_le` :
  injection of the double-shift-free subsets of the mod-`m` rail pair
  `cls n m r ∪ cls n m (r + s - m)` into `stairSets L`.
* `Icc_subset_biUnion_modm_pairCls` : the pairing cover of
  `Icc (m + 1) n`, and `card_powerset_filter_shiftFree2_Icc_le_stairProd`
  the conditional product bound over pairs and leftover rails.
-/

namespace JSP000728

/-- The vertex set of the `2 × L` staircase: `Bool × range L`. -/
def stairVert (L : ℕ) : Finset (Bool × ℕ) :=
  Finset.univ.product (Finset.range L)

/-- Membership in `stairVert L` is just `i < L`. -/
theorem mem_stairVert {b : Bool} {i L : ℕ} :
    (b, i) ∈ stairVert L ↔ i < L := by
  simp [stairVert]

/-- `stairVert 0` is empty. -/
theorem stairVert_zero : stairVert 0 = ∅ := by
  ext ⟨c, j⟩
  simp [mem_stairVert]

/-- `stairVert` is monotone in `L`. -/
theorem stairVert_mono (L : ℕ) : stairVert L ⊆ stairVert (L + 1) := by
  rintro ⟨c, j⟩ hp
  rw [mem_stairVert] at hp ⊢
  omega

/-- `t` is *stair-free*: no cell carries its rail-successor `(b, j+1)`
(the verticals, from the `m`-shift) and no `false`-cell carries the
`true`-cell one level up (the ascending rungs, from the `s`-shift). -/
def stairFree (t : Finset (Bool × ℕ)) : Prop :=
  (∀ p ∈ t, (p.1, p.2 + 1) ∉ t) ∧
    ∀ p ∈ t, p.1 = false → (true, p.2 + 1) ∉ t

/-- `stairFree` is decidable. -/
instance decidableStairFree (t : Finset (Bool × ℕ)) :
    Decidable (stairFree t) := by
  unfold stairFree; infer_instance

/-- `stairFree` is downward-closed. -/
theorem stairFree.mono {t u : Finset (Bool × ℕ)} (ht : stairFree t)
    (hu : u ⊆ t) : stairFree u :=
  ⟨fun p hp hC => ht.1 p (hu hp) (hu hC),
   fun p hp hf hC => ht.2 p (hu hp) hf (hu hC)⟩

/-- The family of independent sets of the `2 × L` staircase. -/
def stairSets (L : ℕ) : Finset (Finset (Bool × ℕ)) :=
  (stairVert L).powerset.filter stairFree

/-- Membership in `stairSets L`: stair-free subsets of the vertex set. -/
theorem mem_stairSets {L : ℕ} {t : Finset (Bool × ℕ)} :
    t ∈ stairSets L ↔ t ⊆ stairVert L ∧ stairFree t := by
  simp [stairSets]

/-- A level-`L` cell is absent from `u ⊆ stairVert L`. -/
theorem notMem_of_subset_stairVert {L : ℕ} {u : Finset (Bool × ℕ)}
    (hu : u ⊆ stairVert L) (c : Bool) : (c, L) ∉ u := by
  intro hC
  have hv := hu hC
  rw [mem_stairVert] at hv
  exact absurd hv (lt_irrefl _)

/-- Stair-free sets avoiding `(false, L-1)`: exactly those that can be
extended by inserting `(false, L)` into column `L` (a `false` cell is
obstructed only by its vertical predecessor). -/
def stairAvoidF (L : ℕ) : Finset (Finset (Bool × ℕ)) :=
  (stairSets L).filter fun t => (false, L - 1) ∉ t

/-- Membership in `stairAvoidF L`. -/
theorem mem_stairAvoidF {L : ℕ} {t : Finset (Bool × ℕ)} :
    t ∈ stairAvoidF L ↔ t ∈ stairSets L ∧ (false, L - 1) ∉ t :=
  Finset.mem_filter

/-- Stair-free sets with empty last column: extendable by `(true, L)`
(the vertical `(true, L-1)` and the rung source `(false, L-1)` are both
absent) and by `{(false, L), (true, L)}`. -/
def stairAvoidE (L : ℕ) : Finset (Finset (Bool × ℕ)) :=
  (stairSets L).filter fun t => (false, L - 1) ∉ t ∧ (true, L - 1) ∉ t

/-- Membership in `stairAvoidE L`. -/
theorem mem_stairAvoidE {L : ℕ} {t : Finset (Bool × ℕ)} :
    t ∈ stairAvoidE L ↔
      t ∈ stairSets L ∧ (false, L - 1) ∉ t ∧ (true, L - 1) ∉ t :=
  Finset.mem_filter

/-- `stairSets` is monotone in `L`. -/
theorem stairSets_mono (L : ℕ) : stairSets L ⊆ stairSets (L + 1) := by
  intro t ht
  rw [mem_stairSets] at ht ⊢
  exact ⟨ht.1.trans (stairVert_mono L), ht.2⟩

/-- Members of `stairSets (L+1)` with an empty last column are exactly the
stair-free sets of the `2 × L` staircase. -/
theorem mem_stairSets_of_succ {L : ℕ} {t : Finset (Bool × ℕ)}
    (ht : t ∈ stairSets (L + 1)) (hf : (false, L) ∉ t)
    (hT : (true, L) ∉ t) : t ∈ stairSets L := by
  rw [mem_stairSets] at ht ⊢
  obtain ⟨hsub, hfree⟩ := ht
  refine ⟨?_, hfree⟩
  rintro ⟨c, j⟩ hp
  have hv := hsub hp
  rw [mem_stairVert] at hv ⊢
  rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hv) with h | h
  · exact h
  · rw [h] at hp
    rcases Bool.dichotomy c with rfl | rfl
    · exact absurd hp hf
    · exact absurd hp hT

/-- Erasing `(false, L)` from a stair-free set that contains it (but not
`(true, L)`) leaves an `F`-avoiding set. -/
theorem erase_mem_stairAvoidF {L : ℕ} {t : Finset (Bool × ℕ)}
    (ht : t ∈ stairSets (L + 1)) (hf : (false, L) ∈ t)
    (hT : (true, L) ∉ t) :
    t.erase (false, L) ∈ stairAvoidF L := by
  rw [mem_stairSets] at ht
  obtain ⟨hsub, hfree⟩ := ht
  have hU : t.erase (false, L) ⊆ stairVert L := by
    rintro ⟨c, j⟩ hp
    rw [Finset.mem_erase] at hp
    obtain ⟨hne, hp⟩ := hp
    have hv := hsub hp
    rw [mem_stairVert] at hv ⊢
    rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hv) with h | h
    · exact h
    · rw [h] at hp hne
      rcases Bool.dichotomy c with rfl | rfl
      · exact absurd rfl hne
      · exact absurd hp hT
  rw [mem_stairAvoidF, mem_stairSets]
  refine ⟨⟨hU, hfree.mono (Finset.erase_subset _ _)⟩, ?_⟩
  intro hC
  have hmem := Finset.mem_of_mem_erase hC
  have hv := hU hC
  rw [mem_stairVert] at hv
  have hL : 1 ≤ L := by omega
  have h1 := hfree.1 (false, L - 1) hmem
  rw [Nat.sub_add_cancel hL] at h1
  exact h1 hf

/-- Erasing `(true, L)` from a stair-free set that contains it (but not
`(false, L)`) leaves an `E`-avoiding set: the vertical predecessor
`(true, L-1)` and the rung source `(false, L-1)` are both forbidden. -/
theorem erase_mem_stairAvoidE {L : ℕ} {t : Finset (Bool × ℕ)}
    (ht : t ∈ stairSets (L + 1)) (hT : (true, L) ∈ t)
    (hf : (false, L) ∉ t) :
    t.erase (true, L) ∈ stairAvoidE L := by
  rw [mem_stairSets] at ht
  obtain ⟨hsub, hfree⟩ := ht
  have hU : t.erase (true, L) ⊆ stairVert L := by
    rintro ⟨c, j⟩ hp
    rw [Finset.mem_erase] at hp
    obtain ⟨hne, hp⟩ := hp
    have hv := hsub hp
    rw [mem_stairVert] at hv ⊢
    rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hv) with h | h
    · exact h
    · rw [h] at hp hne
      rcases Bool.dichotomy c with rfl | rfl
      · exact absurd hp hf
      · exact absurd rfl hne
  rw [mem_stairAvoidE, mem_stairSets]
  refine ⟨⟨hU, hfree.mono (Finset.erase_subset _ _)⟩, ?_, ?_⟩
  · intro hC
    have hmem := Finset.mem_of_mem_erase hC
    have hv := hU hC
    rw [mem_stairVert] at hv
    have hL : 1 ≤ L := by omega
    have h1 := hfree.2 (false, L - 1) hmem rfl
    rw [Nat.sub_add_cancel hL] at h1
    exact h1 hT
  · intro hC
    have hmem := Finset.mem_of_mem_erase hC
    have hv := hU hC
    rw [mem_stairVert] at hv
    have hL : 1 ≤ L := by omega
    have h1 := hfree.1 (true, L - 1) hmem
    rw [Nat.sub_add_cancel hL] at h1
    exact h1 hT

/-- Erasing both level-`L` cells from a stair-free set containing them
leaves an `E`-avoiding set. -/
theorem erase_erase_mem_stairAvoidE {L : ℕ} {t : Finset (Bool × ℕ)}
    (ht : t ∈ stairSets (L + 1)) (hf : (false, L) ∈ t)
    (hT : (true, L) ∈ t) :
    (t.erase (false, L)).erase (true, L) ∈ stairAvoidE L := by
  rw [mem_stairSets] at ht
  obtain ⟨hsub, hfree⟩ := ht
  have hU : (t.erase (false, L)).erase (true, L) ⊆ stairVert L := by
    rintro ⟨c, j⟩ hp
    rw [Finset.mem_erase, Finset.mem_erase] at hp
    obtain ⟨hneT, hneF, hp⟩ := hp
    have hv := hsub hp
    rw [mem_stairVert] at hv ⊢
    rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hv) with h | h
    · exact h
    · rw [h] at hneT hneF
      rcases Bool.dichotomy c with rfl | rfl
      · exact absurd rfl hneF
      · exact absurd rfl hneT
  rw [mem_stairAvoidE, mem_stairSets]
  refine ⟨⟨hU, hfree.mono ((Finset.erase_subset _ _).trans
    (Finset.erase_subset _ _))⟩, ?_, ?_⟩
  · intro hC
    have hmem : (false, L - 1) ∈ t :=
      Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hC)
    have hv := hU hC
    rw [mem_stairVert] at hv
    have hL : 1 ≤ L := by omega
    have h1 := hfree.1 (false, L - 1) hmem
    rw [Nat.sub_add_cancel hL] at h1
    exact h1 hf
  · intro hC
    have hmem : (true, L - 1) ∈ t :=
      Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hC)
    have hv := hU hC
    rw [mem_stairVert] at hv
    have hL : 1 ≤ L := by omega
    have h1 := hfree.1 (true, L - 1) hmem
    rw [Nat.sub_add_cancel hL] at h1
    exact h1 hT

/-- Inserting `(false, L)` into an `F`-avoiding set stays stair-free:
only the vertical predecessor `(false, L-1)` could obstruct it. -/
theorem mem_stairSets_succ_of_mem_stairAvoidF {L : ℕ}
    {u : Finset (Bool × ℕ)} (hu : u ∈ stairAvoidF L) :
    insert (false, L) u ∈ stairSets (L + 1) := by
  rw [mem_stairAvoidF, mem_stairSets] at hu
  obtain ⟨⟨hsub, hfree⟩, hf⟩ := hu
  rw [mem_stairSets]
  refine ⟨?_, ⟨?_, ?_⟩⟩
  · rintro ⟨c, j⟩ hp
    rw [Finset.mem_insert] at hp
    rw [mem_stairVert]
    rcases hp with hp | hp
    · have e2 : j = L := (Prod.ext_iff.mp hp).2
      rw [e2]
      exact Nat.lt_succ_self L
    · have hv := hsub hp
      rw [mem_stairVert] at hv
      omega
  · rintro ⟨c, j⟩ hp hC
    rw [Finset.mem_insert] at hp hC
    rcases hC with hC | hC
    · have e1 : c = false := (Prod.ext_iff.mp hC).1
      have e2 : j + 1 = L := (Prod.ext_iff.mp hC).2
      rcases hp with hp | hp
      · have e4 : j = L := (Prod.ext_iff.mp hp).2
        omega
      · rw [e1, show j = L - 1 from by omega] at hp
        exact hf hp
    · rcases hp with hp | hp
      · have e1 : c = false := (Prod.ext_iff.mp hp).1
        have e2 : j = L := (Prod.ext_iff.mp hp).2
        rw [e1, e2] at hC
        have hv := hsub hC
        rw [mem_stairVert] at hv
        exact absurd hv (by omega)
      · exact hfree.1 (c, j) hp hC
  · rintro ⟨c, j⟩ hp hcf hC
    rw [Finset.mem_insert] at hp hC
    rcases hC with hC | hC
    · exact Bool.noConfusion (Prod.ext_iff.mp hC).1
    · rcases hp with hp | hp
      · have e2 : j = L := (Prod.ext_iff.mp hp).2
        rw [e2] at hC
        have hv := hsub hC
        rw [mem_stairVert] at hv
        exact absurd hv (by omega)
      · exact hfree.2 (c, j) hp hcf hC

/-- Inserting `(true, L)` into an `E`-avoiding set stays stair-free: the
vertical predecessor `(true, L-1)` and the rung source `(false, L-1)`
are both absent. -/
theorem mem_stairSets_succ_of_mem_stairAvoidE {L : ℕ}
    {u : Finset (Bool × ℕ)} (hu : u ∈ stairAvoidE L) :
    insert (true, L) u ∈ stairSets (L + 1) := by
  rw [mem_stairAvoidE, mem_stairSets] at hu
  obtain ⟨⟨hsub, hfree⟩, hf, ht⟩ := hu
  rw [mem_stairSets]
  refine ⟨?_, ⟨?_, ?_⟩⟩
  · rintro ⟨c, j⟩ hp
    rw [Finset.mem_insert] at hp
    rw [mem_stairVert]
    rcases hp with hp | hp
    · have e2 : j = L := (Prod.ext_iff.mp hp).2
      rw [e2]
      exact Nat.lt_succ_self L
    · have hv := hsub hp
      rw [mem_stairVert] at hv
      omega
  · rintro ⟨c, j⟩ hp hC
    rw [Finset.mem_insert] at hp hC
    rcases hC with hC | hC
    · have e1 : c = true := (Prod.ext_iff.mp hC).1
      have e2 : j + 1 = L := (Prod.ext_iff.mp hC).2
      rcases hp with hp | hp
      · have e4 : j = L := (Prod.ext_iff.mp hp).2
        omega
      · rw [e1, show j = L - 1 from by omega] at hp
        exact ht hp
    · rcases hp with hp | hp
      · have e1 : c = true := (Prod.ext_iff.mp hp).1
        have e2 : j = L := (Prod.ext_iff.mp hp).2
        rw [e1, e2] at hC
        have hv := hsub hC
        rw [mem_stairVert] at hv
        exact absurd hv (by omega)
      · exact hfree.1 (c, j) hp hC
  · rintro ⟨c, j⟩ hp hcf hC
    rw [Finset.mem_insert] at hp hC
    rcases hp with hp | hp
    · have e1 : c = true := (Prod.ext_iff.mp hp).1
      have hcf' : c = false := hcf
      rw [e1] at hcf'
      exact absurd hcf' (by decide)
    · rcases hC with hC | hC
      · have e2 : j + 1 = L := (Prod.ext_iff.mp hC).2
        have hcf' : c = false := hcf
        rw [hcf', show j = L - 1 from by omega] at hp
        exact hf hp
      · exact hfree.2 (c, j) hp hcf hC

/-- Inserting `{(false, L), (true, L)}` into an `E`-avoiding set stays
stair-free. -/
theorem mem_stairSets_succ_of_mem_stairAvoidE_pair {L : ℕ}
    {u : Finset (Bool × ℕ)} (hu : u ∈ stairAvoidE L) :
    insert (false, L) (insert (true, L) u) ∈ stairSets (L + 1) := by
  rw [mem_stairAvoidE, mem_stairSets] at hu
  obtain ⟨⟨hsub, hfree⟩, hf, ht⟩ := hu
  rw [mem_stairSets]
  refine ⟨?_, ⟨?_, ?_⟩⟩
  · rintro ⟨c, j⟩ hp
    rw [Finset.mem_insert, Finset.mem_insert] at hp
    rw [mem_stairVert]
    rcases hp with hp | hp | hp
    · have e2 : j = L := (Prod.ext_iff.mp hp).2
      rw [e2]
      exact Nat.lt_succ_self L
    · have e2 : j = L := (Prod.ext_iff.mp hp).2
      rw [e2]
      exact Nat.lt_succ_self L
    · have hv := hsub hp
      rw [mem_stairVert] at hv
      omega
  · rintro ⟨c, j⟩ hp hC
    rw [Finset.mem_insert, Finset.mem_insert] at hp hC
    rcases hC with hC | hC | hC
    · have e1 : c = false := (Prod.ext_iff.mp hC).1
      have e2 : j + 1 = L := (Prod.ext_iff.mp hC).2
      rcases hp with hp | hp | hp
      · have e4 : j = L := (Prod.ext_iff.mp hp).2
        omega
      · have e4 : c = true := (Prod.ext_iff.mp hp).1
        rw [e4] at e1
        exact absurd e1 (by decide)
      · rw [e1, show j = L - 1 from by omega] at hp
        exact hf hp
    · have e1 : c = true := (Prod.ext_iff.mp hC).1
      have e2 : j + 1 = L := (Prod.ext_iff.mp hC).2
      rcases hp with hp | hp | hp
      · have e4 : c = false := (Prod.ext_iff.mp hp).1
        rw [e4] at e1
        exact absurd e1 (by decide)
      · have e4 : j = L := (Prod.ext_iff.mp hp).2
        omega
      · rw [e1, show j = L - 1 from by omega] at hp
        exact ht hp
    · rcases hp with hp | hp | hp
      · have e1 : c = false := (Prod.ext_iff.mp hp).1
        have e2 : j = L := (Prod.ext_iff.mp hp).2
        rw [e1, e2] at hC
        have hv := hsub hC
        rw [mem_stairVert] at hv
        exact absurd hv (by omega)
      · have e1 : c = true := (Prod.ext_iff.mp hp).1
        have e2 : j = L := (Prod.ext_iff.mp hp).2
        rw [e1, e2] at hC
        have hv := hsub hC
        rw [mem_stairVert] at hv
        exact absurd hv (by omega)
      · exact hfree.1 (c, j) hp hC
  · rintro ⟨c, j⟩ hp hcf hC
    have hcf' : c = false := hcf
    rw [Finset.mem_insert, Finset.mem_insert] at hp hC
    rcases hp with hp | hp | hp
    · have e2 : j = L := (Prod.ext_iff.mp hp).2
      rw [e2] at hC
      rcases hC with hC | hC | hC
      · exact Bool.noConfusion (Prod.ext_iff.mp hC).1
      · have e3 : L + 1 = L := (Prod.ext_iff.mp hC).2
        omega
      · have hv := hsub hC
        rw [mem_stairVert] at hv
        exact absurd hv (by omega)
    · have e1 : c = true := (Prod.ext_iff.mp hp).1
      rw [e1] at hcf'
      exact absurd hcf' (by decide)
    · rcases hC with hC | hC | hC
      · exact Bool.noConfusion (Prod.ext_iff.mp hC).1
      · have e2 : j + 1 = L := (Prod.ext_iff.mp hC).2
        rw [hcf', show j = L - 1 from by omega] at hp
        exact hf hp
      · exact hfree.2 (c, j) hp hcf hC

/-- **Column decomposition.**  `stairSets (L+1)` is the disjoint union of
the sets with empty last column (`stairSets L`), the sets ending in
`{(false, L)}` (extensions of `stairAvoidF L`), the sets ending in
`{(true, L)}` and the sets ending in `{(false, L), (true, L)}` (both
extensions of `stairAvoidE L`). -/
theorem stairSets_succ (L : ℕ) :
    stairSets (L + 1) =
      stairSets L ∪
        ((stairAvoidF L).image (fun t => insert (false, L) t) ∪
          ((stairAvoidE L).image (fun t => insert (true, L) t) ∪
            (stairAvoidE L).image
              fun t => insert (false, L) (insert (true, L) t))) := by
  ext t
  simp only [Finset.mem_union, Finset.mem_image]
  constructor
  · intro ht
    by_cases hf : (false, L) ∈ t
    · by_cases hT : (true, L) ∈ t
      · refine Or.inr (Or.inr (Or.inr
          ⟨(t.erase (false, L)).erase (true, L),
            erase_erase_mem_stairAvoidE ht hf hT, ?_⟩))
        have htr : (true, L) ∈ t.erase (false, L) :=
          Finset.mem_erase.mpr
            ⟨fun h => Bool.noConfusion (Prod.ext_iff.mp h).1, hT⟩
        calc insert (false, L)
              (insert (true, L) ((t.erase (false, L)).erase (true, L)))
            = insert (false, L) (t.erase (false, L)) := by
              rw [Finset.insert_erase htr]
          _ = t := Finset.insert_erase hf
      · exact Or.inr (Or.inl ⟨t.erase (false, L),
          erase_mem_stairAvoidF ht hf hT, Finset.insert_erase hf⟩)
    · by_cases hT : (true, L) ∈ t
      · exact Or.inr (Or.inr (Or.inl ⟨t.erase (true, L),
          erase_mem_stairAvoidE ht hT hf, Finset.insert_erase hT⟩))
      · exact Or.inl (mem_stairSets_of_succ ht hf hT)
  · rintro (ht | ⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩)
    · exact stairSets_mono L ht
    · exact mem_stairSets_succ_of_mem_stairAvoidF hu
    · exact mem_stairSets_succ_of_mem_stairAvoidE hu
    · exact mem_stairSets_succ_of_mem_stairAvoidE_pair hu

/-- `insert (false, L)` is injective on `stairAvoidF L`: erasing
`(false, L)` inverts it. -/
theorem stair_card_image_insert_false (L : ℕ) :
    ((stairAvoidF L).image fun t => insert (false, L) t).card =
      (stairAvoidF L).card := by
  apply Finset.card_image_of_injOn
  intro t₁ ht₁ t₂ ht₂ h
  rw [Finset.mem_coe, mem_stairAvoidF, mem_stairSets] at ht₁ ht₂
  have h1 := notMem_of_subset_stairVert ht₁.1.1 false
  have h2 := notMem_of_subset_stairVert ht₂.1.1 false
  have e := congrArg (Finset.erase · (false, L)) h
  rwa [Finset.erase_insert h1, Finset.erase_insert h2] at e

/-- `insert (true, L)` is injective on `stairAvoidE L`. -/
theorem stair_card_image_insert_true (L : ℕ) :
    ((stairAvoidE L).image fun t => insert (true, L) t).card =
      (stairAvoidE L).card := by
  apply Finset.card_image_of_injOn
  intro t₁ ht₁ t₂ ht₂ h
  rw [Finset.mem_coe, mem_stairAvoidE, mem_stairSets] at ht₁ ht₂
  have h1 := notMem_of_subset_stairVert ht₁.1.1 true
  have h2 := notMem_of_subset_stairVert ht₂.1.1 true
  have e := congrArg (Finset.erase · (true, L)) h
  rwa [Finset.erase_insert h1, Finset.erase_insert h2] at e

/-- `t ↦ {(false, L), (true, L)} ∪ t` is injective on `stairAvoidE L`:
erasing both new cells inverts it. -/
theorem stair_card_image_insert_pair (L : ℕ) :
    ((stairAvoidE L).image
        fun t => insert (false, L) (insert (true, L) t)).card =
      (stairAvoidE L).card := by
  apply Finset.card_image_of_injOn
  intro t₁ ht₁ t₂ ht₂ h
  rw [Finset.mem_coe, mem_stairAvoidE, mem_stairSets] at ht₁ ht₂
  have hf1 := notMem_of_subset_stairVert ht₁.1.1 false
  have hf2 := notMem_of_subset_stairVert ht₂.1.1 false
  have ht1 := notMem_of_subset_stairVert ht₁.1.1 true
  have ht2 := notMem_of_subset_stairVert ht₂.1.1 true
  have hf1' : (false, L) ∉ insert (true, L) t₁ := by
    rw [Finset.mem_insert]
    rintro (hC | hC)
    · exact Bool.noConfusion (Prod.ext_iff.mp hC).1
    · exact hf1 hC
  have hf2' : (false, L) ∉ insert (true, L) t₂ := by
    rw [Finset.mem_insert]
    rintro (hC | hC)
    · exact Bool.noConfusion (Prod.ext_iff.mp hC).1
    · exact hf2 hC
  have e := congrArg (Finset.erase · (false, L)) h
  rw [Finset.erase_insert hf1', Finset.erase_insert hf2'] at e
  have e' := congrArg (Finset.erase · (true, L)) e
  rwa [Finset.erase_insert ht1, Finset.erase_insert ht2] at e'

/-- `a(L+1) = a(L) + α(L) + 2·ε(L)`: one choice for the empty last
column, `α` for `{(false, L)}`, and `ε` each for `{(true, L)}` and
`{(false, L), (true, L)}`. -/
theorem stairSets_card_succ (L : ℕ) :
    (stairSets (L + 1)).card =
      (stairSets L).card + (stairAvoidF L).card +
        2 * (stairAvoidE L).card := by
  have d1 : Disjoint (stairSets L)
      ((stairAvoidF L).image (fun t => insert (false, L) t) ∪
        ((stairAvoidE L).image (fun t => insert (true, L) t) ∪
          (stairAvoidE L).image
            fun t => insert (false, L) (insert (true, L) t))) := by
    rw [Finset.disjoint_left]
    intro t ht hB
    rw [Finset.mem_union, Finset.mem_union, Finset.mem_image,
      Finset.mem_image, Finset.mem_image] at hB
    rcases hB with ⟨u, -, rfl⟩ | ⟨u, -, rfl⟩ | ⟨u, -, rfl⟩
    · exact notMem_of_subset_stairVert (mem_stairSets.mp ht).1 false
        (Finset.mem_insert_self _ _)
    · exact notMem_of_subset_stairVert (mem_stairSets.mp ht).1 true
        (Finset.mem_insert_self _ _)
    · exact notMem_of_subset_stairVert (mem_stairSets.mp ht).1 false
        (Finset.mem_insert_self _ _)
  have d2 : Disjoint ((stairAvoidF L).image fun t => insert (false, L) t)
      ((stairAvoidE L).image (fun t => insert (true, L) t) ∪
        (stairAvoidE L).image
          fun t => insert (false, L) (insert (true, L) t)) := by
    rw [Finset.disjoint_left]
    intro t ht hB
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ht
    have hnot : (true, L) ∉ insert (false, L) u := by
      rw [Finset.mem_insert]
      rintro (h | h)
      · exact Bool.noConfusion (Prod.ext_iff.mp h).1
      · exact notMem_of_subset_stairVert
          (mem_stairSets.mp (mem_stairAvoidF.mp hu).1).1 true h
    rw [Finset.mem_union, Finset.mem_image, Finset.mem_image] at hB
    rcases hB with ⟨v, -, hC⟩ | ⟨v, -, hC⟩
    · exact hnot (hC ▸ Finset.mem_insert_self _ _)
    · exact hnot
        (hC ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have d3 : Disjoint ((stairAvoidE L).image fun t => insert (true, L) t)
      ((stairAvoidE L).image
        fun t => insert (false, L) (insert (true, L) t)) := by
    rw [Finset.disjoint_left]
    intro t ht hB
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨v, -, hC⟩ := Finset.mem_image.mp hB
    have hnot : (false, L) ∉ insert (true, L) u := by
      rw [Finset.mem_insert]
      rintro (h | h)
      · exact Bool.noConfusion (Prod.ext_iff.mp h).1
      · exact notMem_of_subset_stairVert
          (mem_stairSets.mp (mem_stairAvoidE.mp hu).1).1 false h
    exact hnot (hC ▸ Finset.mem_insert_self _ _)
  rw [stairSets_succ, Finset.card_union_of_disjoint d1,
    Finset.card_union_of_disjoint d2, Finset.card_union_of_disjoint d3,
    stair_card_image_insert_false, stair_card_image_insert_true,
    stair_card_image_insert_pair]
  ring

/-- Members of `stairSets L` never contain a cell of column `L`, so the
`(c, L) ∉ ·` filter is the identity on `stairSets L`. -/
theorem stairSets_filter_notMem (L : ℕ) (c : Bool) :
    (stairSets L).filter (fun t => (c, L) ∉ t) = stairSets L := by
  ext t
  rw [Finset.mem_filter]
  refine ⟨fun h => h.1, fun ht =>
    ⟨ht, notMem_of_subset_stairVert (mem_stairSets.mp ht).1 c⟩⟩

/-- The `insert (false, L)` image is killed by the `(false, L) ∉ ·`
filter. -/
theorem stairAvoidF_image_filter_same (L : ℕ) :
    ((stairAvoidF L).image fun t => insert (false, L) t).filter
        (fun t => (false, L) ∉ t) = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro t hC
  rw [Finset.mem_filter] at hC
  obtain ⟨ht, hb⟩ := hC
  obtain ⟨u, -, rfl⟩ := Finset.mem_image.mp ht
  exact hb (Finset.mem_insert_self _ _)

/-- The `insert (true, L)` image survives the `(false, L) ∉ ·` filter. -/
theorem stairAvoidE_image_filter_false (L : ℕ) :
    ((stairAvoidE L).image fun t => insert (true, L) t).filter
        (fun t => (false, L) ∉ t) =
      (stairAvoidE L).image fun t => insert (true, L) t := by
  ext t
  rw [Finset.mem_filter]
  refine ⟨fun h => h.1, fun ht => ⟨ht, fun hC => ?_⟩⟩
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ht
  rw [Finset.mem_insert] at hC
  rcases hC with hC | hC
  · exact Bool.noConfusion (Prod.ext_iff.mp hC).1
  · exact notMem_of_subset_stairVert
      (mem_stairSets.mp (mem_stairAvoidE.mp hu).1).1 false hC

/-- The double-insert image is killed by the `(false, L) ∉ ·` filter. -/
theorem stairAvoidE_image_pair_filter_false (L : ℕ) :
    ((stairAvoidE L).image
        fun t => insert (false, L) (insert (true, L) t)).filter
        (fun t => (false, L) ∉ t) = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro t hC
  rw [Finset.mem_filter] at hC
  obtain ⟨ht, hb⟩ := hC
  obtain ⟨u, -, rfl⟩ := Finset.mem_image.mp ht
  exact hb (Finset.mem_insert_self _ _)

/-- The `F`-avoiding family at level `L+1` consists of the sets with empty
last column (`stairSets L`) together with the sets ending in
`{(true, L)}`. -/
theorem stairAvoidF_succ (L : ℕ) :
    stairAvoidF (L + 1) =
      stairSets L ∪ (stairAvoidE L).image fun t => insert (true, L) t := by
  have key : (stairSets (L + 1)).filter (fun t => (false, L) ∉ t) =
      stairSets L ∪ (stairAvoidE L).image fun t => insert (true, L) t := by
    rw [stairSets_succ, Finset.filter_union, Finset.filter_union,
      Finset.filter_union, stairSets_filter_notMem,
      stairAvoidF_image_filter_same, stairAvoidE_image_filter_false,
      stairAvoidE_image_pair_filter_false, Finset.empty_union,
      Finset.union_empty]
  exact key

/-- `α(L+1) = a(L) + ε(L)`: an `F`-avoiding set of length `L+1` either
has empty last column or ends in `{(true, L)}`. -/
theorem stairAvoidF_card_succ (L : ℕ) :
    (stairAvoidF (L + 1)).card =
      (stairSets L).card + (stairAvoidE L).card := by
  have hd : Disjoint (stairSets L)
      ((stairAvoidE L).image fun t => insert (true, L) t) := by
    rw [Finset.disjoint_left]
    intro t ht hB
    rw [Finset.mem_image] at hB
    obtain ⟨u, -, rfl⟩ := hB
    exact notMem_of_subset_stairVert (mem_stairSets.mp ht).1 true
      (Finset.mem_insert_self _ _)
  rw [stairAvoidF_succ, Finset.card_union_of_disjoint hd,
    stair_card_image_insert_true]

/-- The `E`-avoiding family at level `L+1` is exactly `stairSets L`:
avoiding both cells of column `L` means the last column is empty. -/
theorem stairAvoidE_succ (L : ℕ) : stairAvoidE (L + 1) = stairSets L := by
  ext t
  rw [mem_stairAvoidE]
  constructor
  · rintro ⟨ht, hf, hT⟩
    exact mem_stairSets_of_succ ht hf hT
  · intro ht
    exact ⟨stairSets_mono L ht,
      notMem_of_subset_stairVert (mem_stairSets.mp ht).1 false,
      notMem_of_subset_stairVert (mem_stairSets.mp ht).1 true⟩

/-- `ε(L+1) = a(L)`. -/
theorem stairAvoidE_card_succ (L : ℕ) :
    (stairAvoidE (L + 1)).card = (stairSets L).card := by
  rw [stairAvoidE_succ]

/-- **The staircase recurrence** `a(L+3) = a(L+2) + 3·a(L+1) + a(L)`.
Indeed `a(L+3) = a(L+2) + α(L+2) + 2·ε(L+2)` with `α(L+2) = a(L+1) +
ε(L+1) = a(L+1) + a(L)` and `ε(L+2) = a(L+1)`. -/
theorem stairSets_card_add_three (L : ℕ) :
    (stairSets (L + 3)).card =
      (stairSets (L + 2)).card + 3 * (stairSets (L + 1)).card +
        (stairSets L).card := by
  have hA : (stairSets (L + 3)).card =
      (stairSets (L + 2)).card + (stairAvoidF (L + 2)).card +
        2 * (stairAvoidE (L + 2)).card :=
    stairSets_card_succ (L + 2)
  have hF : (stairAvoidF (L + 2)).card =
      (stairSets (L + 1)).card + (stairAvoidE (L + 1)).card :=
    stairAvoidF_card_succ (L + 1)
  have hE : (stairAvoidE (L + 2)).card = (stairSets (L + 1)).card :=
    stairAvoidE_card_succ (L + 1)
  have hE' : (stairAvoidE (L + 1)).card = (stairSets L).card :=
    stairAvoidE_card_succ L
  calc (stairSets (L + 3)).card
      = (stairSets (L + 2)).card + (stairAvoidF (L + 2)).card +
          2 * (stairAvoidE (L + 2)).card := hA
    _ = (stairSets (L + 2)).card +
          ((stairSets (L + 1)).card + (stairAvoidE (L + 1)).card) +
          2 * (stairSets (L + 1)).card := by rw [hF, hE]
    _ = (stairSets (L + 2)).card + 3 * (stairSets (L + 1)).card +
          (stairSets L).card := by rw [hE']; ring

/-- `stairSets 0 = {∅}`. -/
theorem stairSets_zero : stairSets 0 = {∅} := by
  ext t
  rw [mem_stairSets, stairVert_zero, Finset.subset_empty,
    Finset.mem_singleton]
  refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
  subst h
  exact ⟨fun p hp => absurd hp (Finset.notMem_empty _),
    fun p hp => absurd hp (Finset.notMem_empty _)⟩

/-- `stairAvoidF 0 = {∅}`. -/
theorem stairAvoidF_zero : stairAvoidF 0 = {∅} := by
  ext t
  rw [mem_stairAvoidF, stairSets_zero, Finset.mem_singleton]
  refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
  subst h
  exact Finset.notMem_empty _

/-- `stairAvoidE 0 = {∅}`. -/
theorem stairAvoidE_zero : stairAvoidE 0 = {∅} := by
  ext t
  rw [mem_stairAvoidE, stairSets_zero, Finset.mem_singleton]
  refine ⟨fun h => h.1, fun h => ⟨h, ?_, ?_⟩⟩
  · subst h
    exact Finset.notMem_empty _
  · subst h
    exact Finset.notMem_empty _

/-- Base count: `a(0) = 1`. -/
theorem stairSets_card_zero : (stairSets 0).card = 1 := by
  rw [stairSets_zero, Finset.card_singleton]

/-- Base count: `a(1) = 4` (all four column states are allowed). -/
theorem stairSets_card_one : (stairSets 1).card = 4 := by
  have h : (stairSets 1).card =
      (stairSets 0).card + (stairAvoidF 0).card +
        2 * (stairAvoidE 0).card :=
    stairSets_card_succ 0
  rw [stairSets_card_zero, stairAvoidF_zero, stairAvoidE_zero,
    Finset.card_singleton] at h
  exact h

/-- Base count: `a(2) = 8`. -/
theorem stairSets_card_two : (stairSets 2).card = 8 := by
  have h : (stairSets 2).card =
      (stairSets 1).card + (stairAvoidF 1).card +
        2 * (stairAvoidE 1).card :=
    stairSets_card_succ 1
  have hF : (stairAvoidF 1).card =
      (stairSets 0).card + (stairAvoidE 0).card :=
    stairAvoidF_card_succ 0
  have hE : (stairAvoidE 1).card = (stairSets 0).card :=
    stairAvoidE_card_succ 0
  simp only [stairSets_card_one, stairSets_card_zero, stairAvoidE_zero,
    Finset.card_singleton] at h hF hE
  omega

/-- Base count: `a(3) = 21`. -/
theorem stairSets_card_three : (stairSets 3).card = 21 := by
  have h : (stairSets 3).card =
      (stairSets 2).card + 3 * (stairSets 1).card + (stairSets 0).card :=
    stairSets_card_add_three 0
  rw [stairSets_card_two, stairSets_card_one, stairSets_card_zero] at h
  exact h

/-- **Integer-normalised bound.**  `a(L)·2^{L-1} ≤ 4·5^{L-1}` for
`1 ≤ L`, i.e. `a(L) ≤ 4·(5/2)^{L-1}`: the three-step induction gives
`a(k+4)·2^{k+3} = 2·(a(k+3)·2^{k+2}) + 12·(a(k+2)·2^{k+1}) +
8·(a(k+1)·2^k) ≤ 8·5^{k+2} + 48·5^{k+1} + 32·5^k = 472·5^k ≤ 500·5^k =
4·5^{k+3}`. -/
theorem stairSets_card_mul_two_pow_le {L : ℕ} (hL : 1 ≤ L) :
    (stairSets L).card * 2 ^ (L - 1) ≤ 4 * 5 ^ (L - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, L = k + 1 := ⟨L - 1, by omega⟩
  clear hL
  suffices h : ∀ k : ℕ, (stairSets (k + 1)).card * 2 ^ k ≤ 4 * 5 ^ k ∧
      (stairSets (k + 2)).card * 2 ^ (k + 1) ≤ 4 * 5 ^ (k + 1) ∧
      (stairSets (k + 3)).card * 2 ^ (k + 2) ≤ 4 * 5 ^ (k + 2) from
    (h k).1
  intro k
  induction k with
  | zero =>
      refine ⟨?_, ?_, ?_⟩
      · show (stairSets 1).card * 2 ^ 0 ≤ 4 * 5 ^ 0
        rw [stairSets_card_one]
        norm_num
      · show (stairSets 2).card * 2 ^ 1 ≤ 4 * 5 ^ 1
        rw [stairSets_card_two]
        norm_num
      · show (stairSets 3).card * 2 ^ 2 ≤ 4 * 5 ^ 2
        rw [stairSets_card_three]
        norm_num
  | succ k ih =>
      obtain ⟨ih0, ih1, ih2⟩ := ih
      refine ⟨ih1, ih2, ?_⟩
      show (stairSets (k + 4)).card * 2 ^ (k + 3) ≤ 4 * 5 ^ (k + 3)
      have hrec : (stairSets (k + 4)).card =
          (stairSets (k + 3)).card + 3 * (stairSets (k + 2)).card +
            (stairSets (k + 1)).card :=
        stairSets_card_add_three (k + 1)
      calc (stairSets (k + 4)).card * 2 ^ (k + 3)
          = 2 * ((stairSets (k + 3)).card * 2 ^ (k + 2)) +
              12 * ((stairSets (k + 2)).card * 2 ^ (k + 1)) +
              8 * ((stairSets (k + 1)).card * 2 ^ k) := by
            have e1 : (2 : ℕ) ^ (k + 3) = 8 * 2 ^ k := by
              rw [pow_add]; ring
            have e2 : (2 : ℕ) ^ (k + 2) = 4 * 2 ^ k := by
              rw [pow_add]; ring
            have e3 : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := pow_succ' _ _
            rw [hrec, e1, e2, e3]
            ring
        _ ≤ 2 * (4 * 5 ^ (k + 2)) + 12 * (4 * 5 ^ (k + 1)) +
              8 * (4 * 5 ^ k) :=
            add_le_add (add_le_add (Nat.mul_le_mul (le_refl 2) ih2)
              (Nat.mul_le_mul (le_refl 12) ih1))
              (Nat.mul_le_mul (le_refl 8) ih0)
        _ = 472 * 5 ^ k := by
            rw [show (5 : ℕ) ^ (k + 2) = 25 * 5 ^ k from by
              rw [pow_add]; ring,
              show (5 : ℕ) ^ (k + 1) = 5 * 5 ^ k from pow_succ' _ _]
            ring
        _ ≤ 4 * 5 ^ (k + 3) := by
            have e : (5 : ℕ) ^ (k + 3) = 125 * 5 ^ k := by
              rw [pow_add]; ring
            rw [e]
            calc 472 * 5 ^ k ≤ 500 * 5 ^ k :=
                  Nat.mul_le_mul (by norm_num) (le_refl _)
              _ = 4 * (125 * 5 ^ k) := by ring

/-- Loose corollary for later use: `a(L) ≤ 4·5^L`. -/
theorem stairSets_card_le_four_mul_five_pow (L : ℕ) :
    (stairSets L).card ≤ 4 * 5 ^ L := by
  rcases Nat.eq_zero_or_pos L with rfl | hL
  · rw [stairSets_card_zero]; norm_num
  · calc (stairSets L).card
        ≤ (stairSets L).card * 2 ^ (L - 1) := by
          apply Nat.le_mul_of_pos_right
          exact pow_pos (by norm_num) _
      _ ≤ 4 * 5 ^ (L - 1) := stairSets_card_mul_two_pow_le hL
      _ ≤ 4 * 5 ^ L :=
          Nat.mul_le_mul (le_refl 4)
            (pow_le_pow_right₀ (by norm_num) (Nat.sub_le L 1))

/-! ### The mod-`m` diagonal pairing bridge -/

/-- Membership in a residue class, as an indexed progression (a local
copy of `mem_cls_iff` from `PairRails.lean`, restated under a fresh name
to keep the import list minimal). -/
theorem stair_mem_cls_iff {n : ℕ} {m r : ℤ} {x : ℤ} :
    x ∈ cls n m r ↔
      ∃ k : ℕ, k < (((n : ℤ) - r) / m).toNat ∧ x = r + m + m * (k : ℤ) := by
  rw [cls_eq_prog, prog_eq_image, Finset.mem_image]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, Finset.mem_range.mp hk, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, Finset.mem_range.mpr hk, rfl⟩

/-- The rail/index coordinates of an element of
`cls n m r ∪ cls n m (r + s - m)`: elements of the first rail map to
`(false, k)` and elements of the second to `(true, k)`, where `k` is the
position along the progression. -/
def stairIdx (n : ℕ) (m s r : ℤ) (x : ℤ) : Bool × ℕ :=
  if x ∈ cls n m r then (false, ((x - r - m) / m).toNat)
    else (true, ((x - (r + s - m) - m) / m).toNat)

/-- The index map on a member of the `r`-rail lands on `false`. -/
theorem stairIdx_of_mem {n : ℕ} {m s r : ℤ} {x : ℤ} (hx : x ∈ cls n m r) :
    stairIdx n m s r x = (false, ((x - r - m) / m).toNat) :=
  ite_eq_left hx

/-- The index map on a non-member of the `r`-rail lands on `true`. -/
theorem stairIdx_of_not_mem {n : ℕ} {m s r : ℤ} {x : ℤ}
    (hx : x ∉ cls n m r) :
    stairIdx n m s r x = (true, ((x - (r + s - m) - m) / m).toNat) :=
  ite_eq_right hx

/-- The index map on the `r`-rail: `r + m + m·k ↦ (false, k)`. -/
theorem stairIdx_cls {n : ℕ} {m s r : ℤ} (hm : m ≠ 0) {k : ℕ}
    (hk : r + m + m * (k : ℤ) ∈ cls n m r) :
    stairIdx n m s r (r + m + m * (k : ℤ)) = (false, k) := by
  rw [stairIdx_of_mem hk]
  have e : (r + m + m * (k : ℤ) - r - m) / m = (k : ℤ) := by
    rw [show r + m + m * (k : ℤ) - r - m = m * (k : ℤ) from by ring,
      mul_comm m (k : ℤ)]
    exact Int.mul_ediv_cancel _ hm
  rw [e, Int.toNat_natCast]

/-- The index map on the `(r + s - m)`-rail:
`(r + s - m) + m + m·k ↦ (true, k)` (the point is not on the `r`-rail
since the rails are disjoint). -/
theorem stairIdx_cls2 {n : ℕ} {m s r : ℤ} (hm : m ≠ 0) {k : ℕ}
    (hk : (r + s - m) + m + m * (k : ℤ) ∉ cls n m r) :
    stairIdx n m s r ((r + s - m) + m + m * (k : ℤ)) = (true, k) := by
  rw [stairIdx_of_not_mem hk]
  have e : ((r + s - m) + m + m * (k : ℤ) - (r + s - m) - m) / m =
      (k : ℤ) := by
    rw [show (r + s - m) + m + m * (k : ℤ) - (r + s - m) - m =
        m * (k : ℤ) from by ring, mul_comm m (k : ℤ)]
    exact Int.mul_ediv_cancel _ hm
  rw [e, Int.toNat_natCast]

/-- The two mod-`m` rails `r` and `r + s - m` are disjoint: both residues
lie in `Icc 1 m` (using `r ≤ s - m` and `2s ≤ 3m`) and differ since
`s > m`. -/
theorem cls_r_not_mem_of_mem_cls_rsm {n : ℕ} {m s r : ℤ}
    (hm : 1 ≤ m) (hms : m < s) (hsm : 2 * s ≤ 3 * m) (hr : 1 ≤ r)
    (hrsm : r ≤ s - m) {x : ℤ} (hx : x ∈ cls n m (r + s - m)) :
    x ∉ cls n m r := by
  have hd : Disjoint (cls n m r) (cls n m (r + s - m)) :=
    cls_pairwise (n := n) (m := m) hm
      (Finset.mem_coe.mpr (Finset.mem_Icc.mpr ⟨hr, by omega⟩))
      (Finset.mem_coe.mpr (Finset.mem_Icc.mpr ⟨by omega, by omega⟩))
      (by omega)
  exact Finset.disjoint_left.mp hd.symm hx

/-- The index map is injective on the union of the two rails. -/
theorem stairIdx_injOn {n : ℕ} {m s r : ℤ} (hm : 1 ≤ m) (hms : m < s)
    (hsm : 2 * s ≤ 3 * m) (hr : 1 ≤ r) (hrsm : r ≤ s - m) :
    Set.InjOn (stairIdx n m s r)
      (↑(cls n m r ∪ cls n m (r + s - m)) : Set ℤ) := by
  have hm0 : m ≠ 0 := by omega
  intro x hx y hy hxy
  rw [Finset.mem_coe, Finset.mem_union] at hx hy
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · obtain ⟨kx, -, rfl⟩ := stair_mem_cls_iff.mp hx
    obtain ⟨ky, -, rfl⟩ := stair_mem_cls_iff.mp hy
    rw [stairIdx_cls hm0 hx, stairIdx_cls hm0 hy] at hxy
    have h2 : kx = ky := (Prod.ext_iff.mp hxy).2
    rw [h2]
  · obtain ⟨kx, -, rfl⟩ := stair_mem_cls_iff.mp hx
    obtain ⟨ky, -, rfl⟩ := stair_mem_cls_iff.mp hy
    have hyr := cls_r_not_mem_of_mem_cls_rsm hm hms hsm hr hrsm hy
    rw [stairIdx_cls hm0 hx, stairIdx_cls2 hm0 hyr] at hxy
    exact Bool.noConfusion (Prod.ext_iff.mp hxy).1
  · obtain ⟨kx, -, rfl⟩ := stair_mem_cls_iff.mp hx
    obtain ⟨ky, -, rfl⟩ := stair_mem_cls_iff.mp hy
    have hxr := cls_r_not_mem_of_mem_cls_rsm hm hms hsm hr hrsm hx
    rw [stairIdx_cls2 hm0 hxr, stairIdx_cls hm0 hy] at hxy
    exact Bool.noConfusion (Prod.ext_iff.mp hxy).1
  · obtain ⟨kx, -, rfl⟩ := stair_mem_cls_iff.mp hx
    obtain ⟨ky, -, rfl⟩ := stair_mem_cls_iff.mp hy
    have hxr := cls_r_not_mem_of_mem_cls_rsm hm hms hsm hr hrsm hx
    have hyr := cls_r_not_mem_of_mem_cls_rsm hm hms hsm hr hrsm hy
    rw [stairIdx_cls2 hm0 hxr, stairIdx_cls2 hm0 hyr] at hxy
    have h2 : kx = ky := (Prod.ext_iff.mp hxy).2
    rw [h2]

/-- **The staircase bound.**  Double-shift-free subsets of the mod-`m`
rail union inject (via the index map) into the independent sets of the
`2 × L` staircase, where `L = ((n - r)/m).toNat` is the length of the
`r`-rail (the longer of the two).  The `m`-shift gives the verticals on
both rails and the `s`-shift gives the ascending rung
`(false, j) ↦ (true, j+1)`; `s`-edges out of the second rail leave the
pair and are harmlessly dropped. -/
theorem card_powerset_filter_shiftFree2_modm_pair_cls_le {n : ℕ} {m s r : ℤ}
    (hm : 1 ≤ m) (hms : m < s) (hsm : 2 * s ≤ 3 * m) (hr : 1 ≤ r)
    (hrsm : r ≤ s - m) :
    ((cls n m r ∪ cls n m (r + s - m)).powerset.filter
        (shiftFree2 m s)).card ≤
      (stairSets (((n : ℤ) - r) / m).toNat).card := by
  have hmpos : 0 < m := by omega
  have hm0 : m ≠ 0 := ne_of_gt hmpos
  have hL : (((n : ℤ) - (r + s - m)) / m).toNat ≤
      (((n : ℤ) - r) / m).toNat :=
    Int.toNat_le_toNat (Int.ediv_le_ediv hmpos (by omega))
  have hinj := stairIdx_injOn (n := n) hm hms hsm hr hrsm
  refine Finset.card_le_card_of_injOn (Finset.image (stairIdx n m s r))
    ?_ ?_
  · intro T hT
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset] at hT
    obtain ⟨hTU, hsmT, hssT⟩ := hT
    rw [Finset.mem_coe, mem_stairSets]
    refine ⟨?_, ?_, ?_⟩
    · -- the image lies in the `2 × L` vertex set
      rintro ⟨b, k⟩ hp
      rw [Finset.mem_image] at hp
      obtain ⟨x, hxT, hxeq⟩ := hp
      rw [mem_stairVert]
      have hxU := hTU hxT
      rw [Finset.mem_union] at hxU
      rcases hxU with hx | hx
      · obtain ⟨kx, hkx, rfl⟩ := stair_mem_cls_iff.mp hx
        rw [stairIdx_cls hm0 hx] at hxeq
        have hk : k = kx := (Prod.ext_iff.mp hxeq).2.symm
        rw [hk]
        exact hkx
      · obtain ⟨kx, hkx, rfl⟩ := stair_mem_cls_iff.mp hx
        have hxr := cls_r_not_mem_of_mem_cls_rsm hm hms hsm hr hrsm hx
        rw [stairIdx_cls2 hm0 hxr] at hxeq
        have hk : k = kx := (Prod.ext_iff.mp hxeq).2.symm
        rw [hk]
        exact lt_of_lt_of_le hkx hL
    · -- no rail-successor: `x ∈ T` forces `x + m ∉ T`
      intro p hp hC
      rw [Finset.mem_image] at hp hC
      obtain ⟨x, hxT, hpx⟩ := hp
      obtain ⟨y, hyT, hpy⟩ := hC
      have hxU := hTU hxT
      have hyU := hTU hyT
      rw [Finset.mem_union] at hxU hyU
      rcases hxU with hx | hx
      · obtain ⟨kx, -, rfl⟩ := stair_mem_cls_iff.mp hx
        rw [stairIdx_cls hm0 hx] at hpx
        rw [← hpx] at hpy
        rcases hyU with hy | hy
        · obtain ⟨ky, -, rfl⟩ := stair_mem_cls_iff.mp hy
          rw [stairIdx_cls hm0 hy] at hpy
          have hky : ky = kx + 1 := congrArg Prod.snd hpy
          have hEq : r + m + m * (ky : ℤ) =
              (r + m + m * (kx : ℤ)) + m := by
            rw [hky]; push_cast; ring
          rw [hEq] at hyT
          exact hsmT _ hxT hyT
        · obtain ⟨ky, -, rfl⟩ := stair_mem_cls_iff.mp hy
          have hyr := cls_r_not_mem_of_mem_cls_rsm hm hms hsm hr hrsm hy
          rw [stairIdx_cls2 hm0 hyr] at hpy
          exact Bool.noConfusion (Prod.ext_iff.mp hpy).1
      · obtain ⟨kx, -, rfl⟩ := stair_mem_cls_iff.mp hx
        have hxr := cls_r_not_mem_of_mem_cls_rsm hm hms hsm hr hrsm hx
        rw [stairIdx_cls2 hm0 hxr] at hpx
        rw [← hpx] at hpy
        rcases hyU with hy | hy
        · obtain ⟨ky, -, rfl⟩ := stair_mem_cls_iff.mp hy
          rw [stairIdx_cls hm0 hy] at hpy
          exact Bool.noConfusion (Prod.ext_iff.mp hpy).1
        · obtain ⟨ky, -, rfl⟩ := stair_mem_cls_iff.mp hy
          have hyr := cls_r_not_mem_of_mem_cls_rsm hm hms hsm hr hrsm hy
          rw [stairIdx_cls2 hm0 hyr] at hpy
          have hky : ky = kx + 1 := congrArg Prod.snd hpy
          have hEq : (r + s - m) + m + m * (ky : ℤ) =
              ((r + s - m) + m + m * (kx : ℤ)) + m := by
            rw [hky]; push_cast; ring
          rw [hEq] at hyT
          exact hsmT _ hxT hyT
    · -- no ascending rung: `x ∈ T` on rail `r` forces `x + s ∉ T`
      intro p hp hpf hC
      rw [Finset.mem_image] at hp hC
      obtain ⟨x, hxT, hpx⟩ := hp
      obtain ⟨y, hyT, hpy⟩ := hC
      have hxU := hTU hxT
      have hyU := hTU hyT
      rw [Finset.mem_union] at hxU hyU
      rcases hxU with hx | hx
      · obtain ⟨kx, -, rfl⟩ := stair_mem_cls_iff.mp hx
        rw [stairIdx_cls hm0 hx] at hpx
        rw [← hpx] at hpy
        rcases hyU with hy | hy
        · obtain ⟨ky, -, rfl⟩ := stair_mem_cls_iff.mp hy
          rw [stairIdx_cls hm0 hy] at hpy
          exact Bool.noConfusion (Prod.ext_iff.mp hpy).1
        · obtain ⟨ky, -, rfl⟩ := stair_mem_cls_iff.mp hy
          have hyr := cls_r_not_mem_of_mem_cls_rsm hm hms hsm hr hrsm hy
          rw [stairIdx_cls2 hm0 hyr] at hpy
          have hky : ky = kx + 1 := congrArg Prod.snd hpy
          have hEq : (r + s - m) + m + m * (ky : ℤ) =
              (r + m + m * (kx : ℤ)) + s := by
            rw [hky]; push_cast; ring
          rw [hEq] at hyT
          exact hssT _ hxT hyT
      · -- `p.1 = true` contradicts `hpf : p.1 = false`
        obtain ⟨kx, -, rfl⟩ := stair_mem_cls_iff.mp hx
        have hxr := cls_r_not_mem_of_mem_cls_rsm hm hms hsm hr hrsm hx
        rw [stairIdx_cls2 hm0 hxr] at hpx
        rw [← hpx] at hpf
        exact Bool.noConfusion hpf
  · -- `T ↦ T.image stairIdx` is injective on subsets of the rail union
    intro T₁ hT₁ T₂ hT₂ h
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset] at hT₁ hT₂
    ext x
    constructor
    · intro hx
      have hxU : x ∈ cls n m r ∪ cls n m (r + s - m) := hT₁.1 hx
      have hmem : stairIdx n m s r x ∈ T₂.image (stairIdx n m s r) := by
        rw [← h]
        exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
      obtain ⟨y, hyT, hyeq⟩ := Finset.mem_image.mp hmem
      have hyU : y ∈ cls n m r ∪ cls n m (r + s - m) := hT₂.1 hyT
      have hxy : x = y := hinj hxU hyU hyeq.symm
      rwa [hxy]
    · intro hx
      have hxU : x ∈ cls n m r ∪ cls n m (r + s - m) := hT₂.1 hx
      have hmem : stairIdx n m s r x ∈ T₁.image (stairIdx n m s r) := by
        rw [h]
        exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
      obtain ⟨y, hyT, hyeq⟩ := Finset.mem_image.mp hmem
      have hyU : y ∈ cls n m r ∪ cls n m (r + s - m) := hT₁.1 hyT
      have hxy : x = y := hinj hxU hyU hyeq.symm
      rwa [hxy]

/-- **Power-of-5 corollary** for product assembly: the pair factor is at
most `4 * 5 ^ L` where `L` is the `r`-rail length. -/
theorem card_powerset_filter_shiftFree2_modm_pair_cls_le_five_pow {n : ℕ}
    {m s r : ℤ} (hm : 1 ≤ m) (hms : m < s) (hsm : 2 * s ≤ 3 * m)
    (hr : 1 ≤ r) (hrsm : r ≤ s - m) :
    ((cls n m r ∪ cls n m (r + s - m)).powerset.filter
        (shiftFree2 m s)).card ≤
      4 * 5 ^ (((n : ℤ) - r) / m).toNat :=
  (card_powerset_filter_shiftFree2_modm_pair_cls_le hm hms hsm hr
    hrsm).trans (stairSets_card_le_four_mul_five_pow _)

/-- **Pairing cover for the mod-`m` rails.**  Every `x ∈ Icc (m+1) n`
lies in some class `cls n m r` with `r ∈ Icc 1 m`; if `r ≤ s - m` it is
the first member of pair `r`, if `s - m < r ≤ 2(s - m)` it is the second
member of pair `r - (s - m)`, and otherwise `2(s - m) < r ≤ m` is a
leftover rail (of which there are `3m - 2s`, empty when `s = 3m/2`). -/
theorem Icc_subset_biUnion_modm_pairCls {n : ℕ} {m s : ℤ} (hm : 1 ≤ m)
    (_hms : m < s) (_hsm : 2 * s ≤ 3 * m) :
    Finset.Icc (m + 1) (n : ℤ) ⊆
      (Finset.Icc 1 (s - m)).biUnion
          (fun r => cls n m r ∪ cls n m (r + s - m)) ∪
        (Finset.Icc (2 * (s - m) + 1) m).biUnion (cls n m) := by
  intro x hx
  obtain ⟨r, hr, hxr⟩ := Finset.mem_biUnion.mp (Icc_subset_biUnion_cls hm hx)
  rw [Finset.mem_Icc] at hr
  rw [Finset.mem_union, Finset.mem_biUnion, Finset.mem_biUnion]
  rcases lt_or_ge (s - m) r with h | h
  · rcases lt_or_ge (2 * (s - m)) r with h2 | h2
    · exact Or.inr ⟨r, by rw [Finset.mem_Icc]; omega, hxr⟩
    · refine Or.inl ⟨r - (s - m), ?_, ?_⟩
      · rw [Finset.mem_Icc]
        omega
      · rw [Finset.mem_union]
        refine Or.inr ?_
        have e : r - (s - m) + s - m = r := by omega
        rwa [e]
  · exact Or.inl ⟨r, by rw [Finset.mem_Icc]; omega,
      Finset.mem_union.mpr (Or.inl hxr)⟩

/-- **Conditional paired product bound.**  If each pair of mod-`m` rails
`cls n m r ∪ cls n m (r + s - m)` admits the staircase estimate, the
double-shift-free subsets of `Icc (m+1) n` are bounded by the product
over pairs times the Fibonacci counts of the leftover rails (which only
retain the `m`-shift constraint, `shiftFree2.1`). -/
theorem card_powerset_filter_shiftFree2_Icc_le_stairProd {n : ℕ} {m s : ℤ}
    (hm : 1 ≤ m) (hms : m < s) (hsm : 2 * s ≤ 3 * m)
    (hpair : ∀ r ∈ Finset.Icc 1 (s - m),
      ((cls n m r ∪ cls n m (r + s - m)).powerset.filter
          (shiftFree2 m s)).card ≤
        (stairSets (((n : ℤ) - r) / m).toNat).card) :
    ((Finset.Icc (m + 1) (n : ℤ)).powerset.filter (shiftFree2 m s)).card ≤
      (∏ r ∈ Finset.Icc 1 (s - m),
          (stairSets (((n : ℤ) - r) / m).toNat).card) *
        ∏ ρ ∈ Finset.Icc (2 * (s - m) + 1) m,
          Nat.fib ((((n : ℤ) - ρ) / m).toNat + 2) := by
  have hT := Icc_subset_biUnion_modm_pairCls (n := n) hm hms hsm
  have hA := card_powerset_filter_shiftFree2_le_prod (m := m) (s := s)
    (Finset.Icc 1 (s - m)) (fun r => cls n m r ∪ cls n m (r + s - m)) _
    Finset.Subset.rfl
  have hB := card_powerset_filter_shiftFree2_le_prod (m := m) (s := s)
    (Finset.Icc (2 * (s - m) + 1) m) (cls n m) _ Finset.Subset.rfl
  have hA' : (((Finset.Icc 1 (s - m)).biUnion
        (fun r => cls n m r ∪ cls n m (r + s - m))).powerset.filter
        (shiftFree2 m s)).card ≤
      ∏ r ∈ Finset.Icc 1 (s - m),
        (stairSets (((n : ℤ) - r) / m).toNat).card :=
    hA.trans (Finset.prod_le_prod fun r hr => hpair r hr)
  have hB' : (((Finset.Icc (2 * (s - m) + 1) m).biUnion
        (cls n m)).powerset.filter (shiftFree2 m s)).card ≤
      ∏ ρ ∈ Finset.Icc (2 * (s - m) + 1) m,
        Nat.fib ((((n : ℤ) - ρ) / m).toNat + 2) := by
    refine hB.trans (Finset.prod_le_prod fun ρ hρ => ?_)
    have hmono : (cls n m ρ).powerset.filter (shiftFree2 m s) ⊆
        (cls n m ρ).powerset.filter (shiftFree m) := by
      intro t ht
      rw [Finset.mem_filter] at ht ⊢
      exact ⟨ht.1, ht.2.1⟩
    exact (Finset.card_le_card hmono).trans
      (le_of_eq (card_powerset_filter_shiftFree_cls (n := n) (m := m)
        (r := ρ) hm))
  exact (card_powerset_filter_shiftFree2_le_mul hT).trans
    (Nat.mul_le_mul hA' hB')

end JSP000728
