import JSPProblem.Ladder
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Logic.Equiv.Basic

/-!
# JSP-000728 — independent sets of the `3 × L` cyclic strip

The *3-rail cyclic strip* of length `L` has vertex set `Fin 3 × range L`
(three rails of `L` cells) with edges between consecutive cells on the
same rail and between *every* pair of cells in the same column — each
column is a triangle.  An independent set therefore carries **at most one
vertex per column**, and the same rail cannot be occupied in two
consecutive columns.  Column states are `none | some 0 | some 1 | some 2`
(four states) and `some r → some r` is forbidden.

The counts `T(L) = (triSets L).card` satisfy

  `T(0) = 1`, `T(1) = 4`, `T(L+2) = 3·T(L+1) + T(L)`

(`1, 4, 13, 43, 142, …`, growth rate `2 + √3 ≈ 3.732` per column, i.e.
`(7/2)^{1/3} ≈ 1.518` per vertex — below the ladder rate `√(5/2) ≈
1.5811`).

* `triVert L` : the vertex finset `Finset.univ ×ˢ Finset.range L`.
* `triFree t` : the independent-set predicate; decidable.
* `triSets L` : all independent sets, as a `powerset.filter`.
* `triAvoid r L` : independent sets avoiding `(r, L-1)` — exactly those
  that can be extended by placing `(r, L)` in column `L`.  Splitting
  `triSets (L+1)` by the last column (empty, or `{r}` for one of the
  three rails) gives `T(L+1) = T(L) + Σ_r A_r(L)`, and each avoiding
  family satisfies `A_r(L+1) = T(L) + Σ_{c≠r} A_c(L)`.
* `triSwap a b` : the rail transposition `(swap a b r, i)`, an involution
  giving `|triAvoid r L| = |triAvoid r' L|` for all `r r'`
  (`triAvoid_card_eq`).  Hence `T(L+1) = T(L) + 3·A(L)` and
  `A(L+1) = T(L) + 2·A(L)`, which eliminate to
  `triSets_card_add_two : T(L+2) = 3·T(L+1) + T(L)`.
* `triSets_card_mul_two_pow_le` : the integer-normalised bound
  `T(L)·2^L ≤ 4·7^L` (i.e. `T(L) ≤ 4·(7/2)^L`), by two-step induction
  mirroring `ladSets_card_mul_two_pow_le` — the induction step has slack
  (`184 ≤ 196`).
-/

namespace JSP000728

/-- The vertex set of the 3-rail strip: `Fin 3 × range L`. -/
def triVert (L : ℕ) : Finset (Fin 3 × ℕ) :=
  Finset.univ.product (Finset.range L)

theorem mem_triVert {r : Fin 3} {j L : ℕ} :
    (r, j) ∈ triVert L ↔ j < L := by
  simp [triVert]

theorem triVert_zero : triVert 0 = ∅ := by
  ext ⟨c, j⟩
  simp [mem_triVert]

theorem triVert_mono (L : ℕ) : triVert L ⊆ triVert (L + 1) := by
  rintro ⟨c, j⟩ hp
  rw [mem_triVert] at hp ⊢
  omega

/-- `t` is an *independent set* of the strip: no cell carries its
rail-successor `(r, j+1)` and no column carries two cells (the column is
a triangle). -/
def triFree (t : Finset (Fin 3 × ℕ)) : Prop :=
  (∀ p ∈ t, (p.1, p.2 + 1) ∉ t) ∧
    ∀ p ∈ t, ∀ q ∈ t, p.2 = q.2 → p.1 = q.1

instance decidableTriFree (t : Finset (Fin 3 × ℕ)) : Decidable (triFree t) := by
  unfold triFree; infer_instance

theorem triFree.mono {t u : Finset (Fin 3 × ℕ)} (ht : triFree t) (hu : u ⊆ t) :
    triFree u :=
  ⟨fun p hp hC => ht.1 p (hu hp) (hu hC),
   fun p hp q hq hpq => ht.2 p (hu hp) q (hu hq) hpq⟩

/-- The family of independent sets of the `3 × L` strip. -/
def triSets (L : ℕ) : Finset (Finset (Fin 3 × ℕ)) :=
  (triVert L).powerset.filter triFree

theorem mem_triSets {L : ℕ} {t : Finset (Fin 3 × ℕ)} :
    t ∈ triSets L ↔ t ⊆ triVert L ∧ triFree t := by
  simp [triSets]

theorem triSets_mono (L : ℕ) : triSets L ⊆ triSets (L + 1) := by
  intro t ht
  rw [mem_triSets] at ht ⊢
  exact ⟨ht.1.trans (triVert_mono L), ht.2⟩

/-- The independent sets avoiding `(r, L-1)`: exactly those that can be
extended by placing `(r, L)` in column `L`. -/
def triAvoid (r : Fin 3) (L : ℕ) : Finset (Finset (Fin 3 × ℕ)) :=
  (triSets L).filter fun t => (r, L - 1) ∉ t

theorem mem_triAvoid {r : Fin 3} {L : ℕ} {t : Finset (Fin 3 × ℕ)} :
    t ∈ triAvoid r L ↔ t ∈ triSets L ∧ (r, L - 1) ∉ t :=
  Finset.mem_filter

/-- The rail transposition `(swap a b r, j)`, fixing the column. -/
def triSwap (a b : Fin 3) : Fin 3 × ℕ → Fin 3 × ℕ :=
  fun p => (Equiv.swap a b p.1, p.2)

theorem triSwap_involutive (a b : Fin 3) : Function.Involutive (triSwap a b) := by
  rintro ⟨c, j⟩
  show (Equiv.swap a b (Equiv.swap a b c), j) = (c, j)
  rw [Equiv.swap_apply_self]

theorem triSwap_injective (a b : Fin 3) : Function.Injective (triSwap a b) :=
  (triSwap_involutive a b).injective

theorem mem_image_triSwap {a b : Fin 3} {p : Fin 3 × ℕ}
    {t : Finset (Fin 3 × ℕ)} :
    p ∈ t.image (triSwap a b) ↔ triSwap a b p ∈ t := by
  rw [Finset.mem_image]
  constructor
  · rintro ⟨q, hq, rfl⟩
    rwa [triSwap_involutive]
  · intro hp
    exact ⟨triSwap a b p, hp, triSwap_involutive a b p⟩

theorem triVert_image_triSwap {a b : Fin 3} {L : ℕ} {t : Finset (Fin 3 × ℕ)}
    (ht : t ⊆ triVert L) : t.image (triSwap a b) ⊆ triVert L := by
  rintro ⟨c, j⟩ hp
  rw [mem_image_triSwap] at hp
  have hv := ht hp
  rw [mem_triVert] at hv ⊢
  exact hv

theorem triFree_image_triSwap {a b : Fin 3} {t : Finset (Fin 3 × ℕ)}
    (ht : triFree t) : triFree (t.image (triSwap a b)) := by
  constructor
  · rintro ⟨c, j⟩ hp hC
    rw [mem_image_triSwap] at hp hC
    exact ht.1 (Equiv.swap a b c, j) hp hC
  · rintro ⟨c, j⟩ hp ⟨c', j'⟩ hq hjj'
    rw [mem_image_triSwap] at hp hq
    have h : Equiv.swap a b c = Equiv.swap a b c' :=
      ht.2 (Equiv.swap a b c, j) hp (Equiv.swap a b c', j') hq hjj'
    exact (Equiv.swap a b).injective h

theorem mem_triSets_image_triSwap {a b : Fin 3} {L : ℕ}
    {u : Finset (Fin 3 × ℕ)} (hu : u ∈ triSets L) :
    u.image (triSwap a b) ∈ triSets L := by
  rw [mem_triSets] at hu ⊢
  exact ⟨triVert_image_triSwap hu.1, triFree_image_triSwap hu.2⟩

theorem image_triSwap_triSwap (a b : Fin 3) (t : Finset (Fin 3 × ℕ)) :
    (t.image (triSwap a b)).image (triSwap a b) = t := by
  ext p
  rw [mem_image_triSwap, mem_image_triSwap, triSwap_involutive]

/-- **Rail symmetry.**  Transposing two rails identifies the
corresponding avoiding families. -/
theorem triAvoid_swap_eq_image (a b r : Fin 3) (L : ℕ) :
    triAvoid (Equiv.swap a b r) L =
      (triAvoid r L).image fun t => t.image (triSwap a b) := by
  ext u
  rw [mem_triAvoid, Finset.mem_image]
  constructor
  · rintro ⟨hu, hb⟩
    refine ⟨u.image (triSwap a b), ?_, image_triSwap_triSwap a b u⟩
    rw [mem_triAvoid]
    exact ⟨mem_triSets_image_triSwap hu,
      fun hC => hb (mem_image_triSwap.mp hC)⟩
  · rintro ⟨t, ht, rfl⟩
    rw [mem_triAvoid] at ht
    obtain ⟨ht, hb⟩ := ht
    refine ⟨mem_triSets_image_triSwap ht, fun hC => hb ?_⟩
    rw [mem_image_triSwap] at hC
    have e : triSwap a b (Equiv.swap a b r, L - 1) = (r, L - 1) :=
      triSwap_involutive a b (r, L - 1)
    rwa [e] at hC

theorem triAvoid_card_eq (r r' : Fin 3) (L : ℕ) :
    (triAvoid r L).card = (triAvoid r' L).card := by
  have h : Equiv.swap r' r r' = r := Equiv.swap_apply_left r' r
  rw [← h, triAvoid_swap_eq_image]
  exact Finset.card_image_of_injective _
    (Finset.image_injective (triSwap_injective r' r))

/-- Members of `triSets (L+1)` with an empty last column are exactly the
independent sets of the `3 × L` strip. -/
theorem mem_triSets_of_succ {L : ℕ} {t : Finset (Fin 3 × ℕ)}
    (ht : t ∈ triSets (L + 1)) (hf : ∀ r : Fin 3, (r, L) ∉ t) :
    t ∈ triSets L := by
  rw [mem_triSets] at ht ⊢
  obtain ⟨hsub, hfree⟩ := ht
  refine ⟨?_, hfree⟩
  rintro ⟨c, j⟩ hp
  have hv := hsub hp
  rw [mem_triVert] at hv ⊢
  rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hv) with h | h
  · exact h
  · rw [h] at hp
    exact absurd hp (hf c)

/-- Erasing `(r, L)` from an independent set containing it leaves an
element of `triAvoid r L` (the triangle condition kills any other cell
of column `L`). -/
theorem erase_mem_triAvoid {r : Fin 3} {L : ℕ} {t : Finset (Fin 3 × ℕ)}
    (ht : t ∈ triSets (L + 1)) (hb : (r, L) ∈ t) :
    t.erase (r, L) ∈ triAvoid r L := by
  rw [mem_triSets] at ht
  obtain ⟨hsub, hfree⟩ := ht
  have hU : t.erase (r, L) ⊆ triVert L := by
    rintro ⟨c, j⟩ hp
    rw [Finset.mem_erase] at hp
    obtain ⟨hne, hp⟩ := hp
    have hv := hsub hp
    rw [mem_triVert] at hv ⊢
    rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hv) with h | h
    · exact h
    · rw [h] at hp hne
      have hrc := hfree.2 (r, L) hb (c, L) hp rfl
      exact absurd (Prod.ext_iff.mpr ⟨hrc.symm, rfl⟩) hne
  rw [mem_triAvoid, mem_triSets]
  refine ⟨⟨hU, hfree.mono (Finset.erase_subset _ _)⟩, ?_⟩
  intro hC
  have hmem := Finset.mem_of_mem_erase hC
  have hv := hU hC
  rw [mem_triVert] at hv
  have hL : 1 ≤ L := by omega
  have h1 := hfree.1 (r, L - 1) hmem
  rw [Nat.sub_add_cancel hL] at h1
  exact h1 hb

/-- Inserting `(r, L)` into an element of `triAvoid r L` stays
independent: the other column-`L` cells and the rail predecessor
`(r, L-1)` are absent. -/
theorem mem_triSets_succ_of_mem_triAvoid {r : Fin 3} {L : ℕ}
    {u : Finset (Fin 3 × ℕ)} (hu : u ∈ triAvoid r L) :
    insert (r, L) u ∈ triSets (L + 1) := by
  rw [mem_triAvoid, mem_triSets] at hu
  obtain ⟨⟨hsub, hfree⟩, hb⟩ := hu
  rw [mem_triSets]
  refine ⟨?_, ⟨?_, ?_⟩⟩
  · rintro ⟨c, j⟩ hp
    rw [Finset.mem_insert] at hp
    rw [mem_triVert]
    rcases hp with hp | hp
    · have e2 : j = L := (Prod.ext_iff.mp hp).2
      rw [e2]
      exact Nat.lt_succ_self L
    · have hv := hsub hp
      rw [mem_triVert] at hv
      omega
  · rintro ⟨c, j⟩ hp hC
    rw [Finset.mem_insert] at hp hC
    rcases hC with hC | hC
    · have e1 : c = r := (Prod.ext_iff.mp hC).1
      have e2 : j + 1 = L := (Prod.ext_iff.mp hC).2
      rcases hp with hp | hp
      · have e4 : j = L := (Prod.ext_iff.mp hp).2
        omega
      · rw [e1, show j = L - 1 from by omega] at hp
        exact hb hp
    · rcases hp with hp | hp
      · have e2 : j = L := (Prod.ext_iff.mp hp).2
        rw [e2] at hC
        have hv := hsub hC
        rw [mem_triVert] at hv
        omega
      · exact hfree.1 (c, j) hp hC
  · rintro ⟨c, j⟩ hp ⟨c', j'⟩ hq hjj'
    rw [Finset.mem_insert] at hp hq
    rcases hp with hp | hp
    · have ec : c = r := (Prod.ext_iff.mp hp).1
      have ej : j = L := (Prod.ext_iff.mp hp).2
      rcases hq with hq | hq
      · have ec' : c' = r := (Prod.ext_iff.mp hq).1
        exact ec.trans ec'.symm
      · rw [ej] at hjj'
        have hv := hsub hq
        rw [mem_triVert] at hv
        omega
    · rcases hq with hq | hq
      · have ej' : j' = L := (Prod.ext_iff.mp hq).2
        rw [ej'] at hjj'
        have hv := hsub hp
        rw [mem_triVert] at hv
        omega
      · exact hfree.2 (c, j) hp (c', j') hq hjj'

/-- **Column decomposition.**  `triSets (L+1)` is the disjoint union of
the sets with empty last column (`triSets L`) and, for each rail `r`,
the sets ending in `{(r, L)}`. -/
theorem triSets_succ (L : ℕ) :
    triSets (L + 1) =
      triSets L ∪ (Finset.univ : Finset (Fin 3)).biUnion
        (fun r => (triAvoid r L).image fun t => insert (r, L) t) := by
  ext t
  rw [Finset.mem_union, Finset.mem_biUnion]
  constructor
  · intro ht
    by_cases h : ∃ r : Fin 3, (r, L) ∈ t
    · obtain ⟨r, hr⟩ := h
      refine Or.inr ⟨r, Finset.mem_univ r, ?_⟩
      rw [Finset.mem_image]
      exact ⟨t.erase (r, L), erase_mem_triAvoid ht hr, Finset.insert_erase hr⟩
    · exact Or.inl (mem_triSets_of_succ ht fun r hr => h ⟨r, hr⟩)
  · rintro (ht | ⟨r, -, hr⟩)
    · exact triSets_mono L ht
    · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hr
      exact mem_triSets_succ_of_mem_triAvoid hu

/-- The `insert (r, L)` image of `triAvoid r L` has the same cardinality:
`erase (r, L)` inverts it since `(r, L) ∉ t` for `t ⊆ triVert L`. -/
theorem triCard_image_insert (r : Fin 3) (L : ℕ) :
    ((triAvoid r L).image fun t => insert (r, L) t).card =
      (triAvoid r L).card := by
  apply Finset.card_image_of_injOn
  intro t₁ ht₁ t₂ ht₂ h
  rw [Finset.mem_coe, mem_triAvoid, mem_triSets] at ht₁ ht₂
  have h1 : (r, L) ∉ t₁ := by
    intro hC
    have hv := ht₁.1.1 hC
    rw [mem_triVert] at hv
    exact absurd hv (lt_irrefl _)
  have h2 : (r, L) ∉ t₂ := by
    intro hC
    have hv := ht₂.1.1 hC
    rw [mem_triVert] at hv
    exact absurd hv (lt_irrefl _)
  have e := congrArg (Finset.erase · (r, L)) h
  rwa [Finset.erase_insert h1, Finset.erase_insert h2] at e

/-- `T(L+1) = T(L) + 3·A(L)`: one choice for the empty last column and
three symmetric choices for the singly-occupied one. -/
theorem triSets_card_succ (L : ℕ) :
    (triSets (L + 1)).card = (triSets L).card + 3 * (triAvoid 0 L).card := by
  have d1 : Disjoint (triSets L)
      ((Finset.univ : Finset (Fin 3)).biUnion
        fun r => (triAvoid r L).image fun t => insert (r, L) t) := by
    rw [Finset.disjoint_left]
    intro t ht hB
    rw [Finset.mem_biUnion] at hB
    obtain ⟨r, -, hr⟩ := hB
    obtain ⟨u, -, rfl⟩ := Finset.mem_image.mp hr
    have hv := (mem_triSets.mp ht).1 (Finset.mem_insert_self (r, L) u)
    rw [mem_triVert] at hv
    exact absurd hv (lt_irrefl _)
  have d2 : ((Finset.univ : Finset (Fin 3)) : Set (Fin 3)).PairwiseDisjoint
      fun r => (triAvoid r L).image fun t => insert (r, L) t := by
    rintro r - r' - hrr
    show Disjoint ((triAvoid r L).image fun t => insert (r, L) t)
      ((triAvoid r' L).image fun t => insert (r', L) t)
    rw [Finset.disjoint_left]
    intro t ht hB
    obtain ⟨u, -, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨v, hv, heq⟩ := Finset.mem_image.mp hB
    have hmem : (r, L) ∈ insert (r', L) v := by
      rw [heq]
      exact Finset.mem_insert_self _ _
    rw [Finset.mem_insert] at hmem
    rcases hmem with hmem | hmem
    · exact absurd (Prod.ext_iff.mp hmem).1 hrr
    · have hv' := (mem_triSets.mp (mem_triAvoid.mp hv).1).1 hmem
      rw [mem_triVert] at hv'
      exact absurd hv' (lt_irrefl _)
  rw [triSets_succ, Finset.card_union_of_disjoint d1, Finset.card_biUnion d2]
  have hsum : (∑ r ∈ Finset.univ,
        ((triAvoid r L).image fun t => insert (r, L) t).card)
      = ∑ _r ∈ (Finset.univ : Finset (Fin 3)), (triAvoid 0 L).card := by
    apply Finset.sum_congr rfl
    intro r _
    rw [triCard_image_insert]
    exact triAvoid_card_eq r 0 L
  rw [hsum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    Nat.nsmul_eq_mul]

/-- The avoiding family at level `L+1` consists of the sets with empty
last column (`triSets L`) together with the sets ending in `{(c, L)}`
for `c ≠ r`. -/
theorem triAvoid_succ (L : ℕ) (r : Fin 3) :
    triAvoid r (L + 1) =
      triSets L ∪ ((Finset.univ.filter fun c => c ≠ r).biUnion
        fun c => (triAvoid c L).image fun t => insert (c, L) t) := by
  ext t
  simp only [mem_triAvoid, Nat.add_sub_cancel, Finset.mem_union,
    Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
    true_and]
  constructor
  · rintro ⟨ht, hr⟩
    by_cases h : ∃ c : Fin 3, (c, L) ∈ t
    · obtain ⟨c, hc⟩ := h
      have hcr : c ≠ r := by
        rintro rfl
        exact hr hc
      exact Or.inr ⟨c, hcr, t.erase (c, L),
        mem_triAvoid.mp (erase_mem_triAvoid ht hc), Finset.insert_erase hc⟩
    · exact Or.inl (mem_triSets_of_succ ht fun c hc => h ⟨c, hc⟩)
  · rintro (ht | ⟨c, hcr, u, hu, rfl⟩)
    · refine ⟨triSets_mono L ht, fun hC => ?_⟩
      have hv := (mem_triSets.mp ht).1 hC
      rw [mem_triVert] at hv
      exact absurd hv (lt_irrefl _)
    · refine ⟨mem_triSets_succ_of_mem_triAvoid (mem_triAvoid.mpr hu),
        fun hC => ?_⟩
      rw [Finset.mem_insert] at hC
      rcases hC with hC | hC
      · exact hcr (Prod.ext_iff.mp hC).1.symm
      · have hv := (mem_triSets.mp hu.1).1 hC
        rw [mem_triVert] at hv
        exact absurd hv (lt_irrefl _)

/-- `A(L+1) = T(L) + 2·A(L)`: an `r`-avoiding set of length `L+1` either
has empty last column or ends in one of the two other rails, whose
avoiding counts equal `A(L)` by rail symmetry. -/
theorem triAvoid_succ_card (L : ℕ) (r : Fin 3) :
    (triAvoid r (L + 1)).card =
      (triSets L).card + 2 * (triAvoid r L).card := by
  have d1 : Disjoint (triSets L)
      (((Finset.univ : Finset (Fin 3)).filter fun c => c ≠ r).biUnion
        fun c => (triAvoid c L).image fun t => insert (c, L) t) := by
    rw [Finset.disjoint_left]
    intro t ht hB
    rw [Finset.mem_biUnion] at hB
    obtain ⟨c, -, hr⟩ := hB
    obtain ⟨u, -, rfl⟩ := Finset.mem_image.mp hr
    have hv := (mem_triSets.mp ht).1 (Finset.mem_insert_self (c, L) u)
    rw [mem_triVert] at hv
    exact absurd hv (lt_irrefl _)
  have d2 : (((Finset.univ : Finset (Fin 3)).filter fun c => c ≠ r) :
      Set (Fin 3)).PairwiseDisjoint
      fun c => (triAvoid c L).image fun t => insert (c, L) t := by
    rintro c - c' - hcc
    show Disjoint ((triAvoid c L).image fun t => insert (c, L) t)
      ((triAvoid c' L).image fun t => insert (c', L) t)
    rw [Finset.disjoint_left]
    intro t ht hB
    obtain ⟨u, -, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨v, hv, heq⟩ := Finset.mem_image.mp hB
    have hmem : (c, L) ∈ insert (c', L) v := by
      rw [heq]
      exact Finset.mem_insert_self _ _
    rw [Finset.mem_insert] at hmem
    rcases hmem with hmem | hmem
    · exact absurd (Prod.ext_iff.mp hmem).1 hcc
    · have hv' := (mem_triSets.mp (mem_triAvoid.mp hv).1).1 hmem
      rw [mem_triVert] at hv'
      exact absurd hv' (lt_irrefl _)
  have hcard : ((Finset.univ : Finset (Fin 3)).filter fun c => c ≠ r).card
      = 2 := by
    rw [Finset.filter_ne' _ r,
      Finset.card_erase_of_mem (Finset.mem_univ r), Finset.card_univ,
      Fintype.card_fin]
  rw [triAvoid_succ, Finset.card_union_of_disjoint d1,
    Finset.card_biUnion d2]
  have hsum : (∑ c ∈ Finset.univ.filter fun c => c ≠ r,
        ((triAvoid c L).image fun t => insert (c, L) t).card)
      = ∑ _c ∈ Finset.univ.filter (fun c => c ≠ r), (triAvoid r L).card := by
    apply Finset.sum_congr rfl
    intro c _
    rw [triCard_image_insert]
    exact triAvoid_card_eq c r L
  rw [hsum, Finset.sum_const, hcard, Nat.nsmul_eq_mul]

/-- **The recurrence** `T(L+2) = 3·T(L+1) + T(L)`. -/
theorem triSets_card_add_two (L : ℕ) :
    (triSets (L + 2)).card =
      3 * (triSets (L + 1)).card + (triSets L).card := by
  have hA : (triSets (L + 2)).card =
      (triSets (L + 1)).card + 3 * (triAvoid 0 (L + 1)).card :=
    triSets_card_succ (L + 1)
  have hB := triSets_card_succ L
  have hF := triAvoid_succ_card L 0
  omega

theorem triSets_zero : triSets 0 = {∅} := by
  ext t
  rw [mem_triSets, triVert_zero, Finset.subset_empty, Finset.mem_singleton]
  refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
  subst h
  exact ⟨fun p hp => absurd hp (Finset.notMem_empty _),
    fun p hp => absurd hp (Finset.notMem_empty _)⟩

theorem triAvoid_zero (r : Fin 3) : triAvoid r 0 = {∅} := by
  ext t
  rw [mem_triAvoid, triSets_zero, Finset.mem_singleton]
  refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
  subst h
  exact Finset.notMem_empty _

/-- Base count: `T(0) = 1`. -/
theorem triSets_card_zero : (triSets 0).card = 1 := by
  rw [triSets_zero, Finset.card_singleton]

/-- Base count: `T(1) = 4` (the empty set and three singletons). -/
theorem triSets_card_one : (triSets 1).card = 4 := by
  have h : (triSets 1).card = (triSets 0).card + 3 * (triAvoid 0 0).card :=
    triSets_card_succ 0
  rw [triSets_card_zero, triAvoid_zero, Finset.card_singleton] at h
  exact h

/-- Base count: `T(2) = 13`. -/
theorem triSets_card_two : (triSets 2).card = 13 := by
  have h2 : (triSets 2).card = (triSets 1).card + 3 * (triAvoid 0 1).card :=
    triSets_card_succ 1
  have hF : (triAvoid 0 1).card =
      (triSets 0).card + 2 * (triAvoid 0 0).card :=
    triAvoid_succ_card 0 (0 : Fin 3)
  simp only [triSets_card_one, triSets_card_zero, triAvoid_zero,
    Finset.card_singleton] at h2 hF
  omega

/-- **Integer-normalised bound.**  `T(L)·2^L ≤ 4·7^L` for all `L`, i.e.
`T(L) ≤ 4·(7/2)^L`: the two-step induction gives
`T(k+2)·2^{k+2} = 6·(T(k+1)·2^{k+1}) + 4·(T(k)·2^k) ≤ 24·7^{k+1} +
16·7^k = 184·7^k ≤ 196·7^k = 4·7^{k+2}`. -/
theorem triSets_card_mul_two_pow_le (L : ℕ) :
    (triSets L).card * 2 ^ L ≤ 4 * 7 ^ L := by
  induction L using Nat.twoStepInduction with
  | zero =>
      rw [triSets_card_zero]
      norm_num
  | one =>
      rw [triSets_card_one]
      norm_num
  | more k ih ih1 =>
      have hrec : (triSets (k + 2)).card =
          3 * (triSets (k + 1)).card + (triSets k).card :=
        triSets_card_add_two k
      calc (triSets (k + 2)).card * 2 ^ (k + 2)
          = 6 * ((triSets (k + 1)).card * 2 ^ (k + 1)) +
              4 * ((triSets k).card * 2 ^ k) := by
            have e1 : (2 : ℕ) ^ (k + 2) = 4 * 2 ^ k := by
              rw [pow_add]; ring
            have e2 : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := pow_succ' _ _
            rw [hrec, e1, e2]
            ring
        _ ≤ 6 * (4 * 7 ^ (k + 1)) + 4 * (4 * 7 ^ k) :=
            add_le_add (Nat.mul_le_mul (le_refl 6) ih1)
              (Nat.mul_le_mul (le_refl 4) ih)
        _ = 184 * 7 ^ k := by
            rw [show (7 : ℕ) ^ (k + 1) = 7 * 7 ^ k from pow_succ' _ _]; ring
        _ ≤ 4 * 7 ^ (k + 2) := by
            have e : (7 : ℕ) ^ (k + 2) = 49 * 7 ^ k := by
              rw [pow_add]; ring
            rw [e]
            calc 184 * 7 ^ k ≤ 196 * 7 ^ k :=
                  Nat.mul_le_mul (by norm_num) (le_refl _)
              _ = 4 * (49 * 7 ^ k) := by ring

/-- Cruder bound from the same recurrence: `T(L) ≤ 4^L` (four column
states per column), with slack `13 ≤ 16`. -/
theorem triSets_card_le_four_pow (L : ℕ) : (triSets L).card ≤ 4 ^ L := by
  induction L using Nat.twoStepInduction with
  | zero =>
      rw [triSets_card_zero]
      norm_num
  | one =>
      rw [triSets_card_one]
      norm_num
  | more k ih ih1 =>
      have hrec : (triSets (k + 2)).card =
          3 * (triSets (k + 1)).card + (triSets k).card :=
        triSets_card_add_two k
      calc (triSets (k + 2)).card
          = 3 * (triSets (k + 1)).card + (triSets k).card := hrec
        _ ≤ 3 * 4 ^ (k + 1) + 4 ^ k :=
            add_le_add (Nat.mul_le_mul (le_refl 3) ih1) ih
        _ = 13 * 4 ^ k := by
            rw [show (4 : ℕ) ^ (k + 1) = 4 * 4 ^ k from pow_succ' _ _]; ring
        _ ≤ 4 ^ (k + 2) := by
            have e : (4 : ℕ) ^ (k + 2) = 16 * 4 ^ k := by
              rw [pow_add]; ring
            rw [e]
            exact Nat.mul_le_mul (by norm_num) (le_refl _)

/-- Loose corollary for later use: `T(L) ≤ 4·4^L`. -/
theorem triSets_card_le (L : ℕ) : (triSets L).card ≤ 4 * 4 ^ L := by
  apply (triSets_card_le_four_pow L).trans
  have h : (4 : ℕ) ^ L ≤ 4 ^ L * 4 :=
    Nat.le_mul_of_pos_right _ (by norm_num)
  rwa [mul_comm] at h

end JSP000728
