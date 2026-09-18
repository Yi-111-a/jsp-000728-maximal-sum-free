import JSPProblem.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Bool.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# JSP-000728 — independent sets of the `2 × L` ladder

The `2 × L` ladder graph has vertex set `Bool × range L` (two rails of
`L` cells) with edges between the two cells of each column (the rungs)
and between consecutive cells on the same rail.  Its independent sets —
subsets `t` with no rung-mate `(!b, i)` and no rail-successor `(b, i+1)`
— are counted by

  `a(0) = 1`, `a(1) = 3`, `a(L+2) = 2·a(L+1) + a(L)`

(the Pell/NSW sequence `1, 3, 7, 17, 41, …`).  This is the key
combinatorial input for pushing the `maxSumFreeCount` upper bound below
the golden-ratio bound.

* `ladVert L` : the vertex finset `Finset.univ ×ˢ Finset.range L`.
* `ladFree t` : the independent-set predicate; decidable.
* `ladSets L` : all independent sets, as a `powerset.filter`.
* `ladAvoid b L` : independent sets avoiding `(b, L-1)` — exactly those
  that can be extended by inserting `(b, L)`.  Splitting
  `ladSets (L+1)` by the state of the last column (empty, `{false}`,
  `{true}`) gives `a(L+1) = a(L) + 2·f(L)`, and `f` itself satisfies
  `f(L+1) = a(L) + f(L)` by the same split; together they yield
  `ladSets_card_add_two`.
* `ladSwap` : the rail-swap involution `(!b, i)`, giving
  `|ladAvoid true L| = |ladAvoid false L|` (`ladAvoid_card_eq`).
* `ladSets_card_mul_two_pow_le` : the integer-normalised bound
  `a(L)·2^{L-1} ≤ 3·5^{L-1}` for `1 ≤ L` (i.e. `a(L) ≤ 3·(5/2)^{L-1}`),
  by two-step induction mirroring `g3Sets_card_mul_two_pow_le` in
  `TwoMin.lean` — the induction step has slack (`72 ≤ 75`).

A `Real`-valued corollary `a(L) ≤ 3·(5/2)^{L-1}`, or the sharp growth
rate `(1 + √2)^L`, is left as future work.
-/

namespace JSP000728

/-- The vertex set of the `2 × L` ladder: `Bool × range L`. -/
def ladVert (L : ℕ) : Finset (Bool × ℕ) :=
  Finset.univ.product (Finset.range L)

theorem mem_ladVert {b : Bool} {i L : ℕ} :
    (b, i) ∈ ladVert L ↔ i < L := by
  simp [ladVert]

theorem ladVert_zero : ladVert 0 = ∅ := by
  ext ⟨c, j⟩
  simp [mem_ladVert]

theorem ladVert_mono (L : ℕ) : ladVert L ⊆ ladVert (L + 1) := by
  rintro ⟨c, j⟩ hp
  rw [mem_ladVert] at hp ⊢
  omega

/-- `t` is an *independent set* of the ladder: no cell carries its
rung-mate `(!b, i)` and no cell carries its rail-successor `(b, i+1)`. -/
def ladFree (t : Finset (Bool × ℕ)) : Prop :=
  (∀ p ∈ t, (p.1, p.2 + 1) ∉ t) ∧ ∀ p ∈ t, (!p.1, p.2) ∉ t

instance decidableLadFree (t : Finset (Bool × ℕ)) : Decidable (ladFree t) := by
  unfold ladFree; infer_instance

theorem ladFree.mono {t u : Finset (Bool × ℕ)} (ht : ladFree t) (hu : u ⊆ t) :
    ladFree u :=
  ⟨fun p hp hC => ht.1 p (hu hp) (hu hC),
   fun p hp hC => ht.2 p (hu hp) (hu hC)⟩

/-- The family of independent sets of the `2 × L` ladder. -/
def ladSets (L : ℕ) : Finset (Finset (Bool × ℕ)) :=
  (ladVert L).powerset.filter ladFree

theorem mem_ladSets {L : ℕ} {t : Finset (Bool × ℕ)} :
    t ∈ ladSets L ↔ t ⊆ ladVert L ∧ ladFree t := by
  simp [ladSets]

/-- The independent sets avoiding `(b, L-1)`: exactly those that can be
extended by inserting `(b, L)` into column `L`.  The `L - 1` convention
also works at `L = 0`, where every (empty) set is extendable. -/
def ladAvoid (b : Bool) (L : ℕ) : Finset (Finset (Bool × ℕ)) :=
  (ladSets L).filter fun t => (b, L - 1) ∉ t

theorem mem_ladAvoid {b : Bool} {L : ℕ} {t : Finset (Bool × ℕ)} :
    t ∈ ladAvoid b L ↔ t ∈ ladSets L ∧ (b, L - 1) ∉ t :=
  Finset.mem_filter

/-- The rail-swap involution `(!b, i)`. -/
def ladSwap : Bool × ℕ → Bool × ℕ := fun p => (!p.1, p.2)

theorem ladSwap_involutive : Function.Involutive ladSwap := by
  rintro ⟨c, j⟩
  show (! ! c, j) = (c, j)
  rw [Bool.not_not]

theorem ladSwap_injective : Function.Injective ladSwap :=
  ladSwap_involutive.injective

theorem mem_image_ladSwap {p : Bool × ℕ} {t : Finset (Bool × ℕ)} :
    p ∈ t.image ladSwap ↔ ladSwap p ∈ t := by
  rw [Finset.mem_image]
  constructor
  · rintro ⟨q, hq, rfl⟩
    rwa [ladSwap_involutive]
  · intro hp
    exact ⟨ladSwap p, hp, ladSwap_involutive p⟩

theorem ladVert_image_ladSwap {L : ℕ} {t : Finset (Bool × ℕ)}
    (ht : t ⊆ ladVert L) : t.image ladSwap ⊆ ladVert L := by
  rintro ⟨c, j⟩ hp
  rw [mem_image_ladSwap] at hp
  have hv : (!c, j) ∈ ladVert L := ht hp
  rw [mem_ladVert] at hv ⊢
  exact hv

theorem ladFree_image_ladSwap {t : Finset (Bool × ℕ)} (ht : ladFree t) :
    ladFree (t.image ladSwap) := by
  constructor
  · rintro ⟨c, j⟩ hp hC
    rw [mem_image_ladSwap] at hp hC
    exact ht.1 (!c, j) hp hC
  · rintro ⟨c, j⟩ hp hC
    rw [mem_image_ladSwap] at hp hC
    exact ht.2 (!c, j) hp hC

theorem mem_ladSets_image_ladSwap {L : ℕ} {u : Finset (Bool × ℕ)}
    (hu : u ∈ ladSets L) : u.image ladSwap ∈ ladSets L := by
  rw [mem_ladSets] at hu ⊢
  exact ⟨ladVert_image_ladSwap hu.1, ladFree_image_ladSwap hu.2⟩

theorem image_ladSwap_ladSwap (t : Finset (Bool × ℕ)) :
    (t.image ladSwap).image ladSwap = t := by
  ext p
  rw [mem_image_ladSwap, mem_image_ladSwap, ladSwap_involutive]

/-- **Rail symmetry.**  Swapping the rails identifies the `true`-avoiding
and `false`-avoiding families. -/
theorem ladAvoid_true_eq_image (L : ℕ) :
    ladAvoid true L = (ladAvoid false L).image fun t => t.image ladSwap := by
  ext u
  rw [mem_ladAvoid, Finset.mem_image]
  constructor
  · rintro ⟨hu, hb⟩
    refine ⟨u.image ladSwap, ?_, image_ladSwap_ladSwap u⟩
    rw [mem_ladAvoid]
    exact ⟨mem_ladSets_image_ladSwap hu, fun hC => hb (mem_image_ladSwap.mp hC)⟩
  · rintro ⟨t, ht, rfl⟩
    rw [mem_ladAvoid] at ht
    exact ⟨mem_ladSets_image_ladSwap ht.1,
      fun hC => ht.2 (mem_image_ladSwap.mp hC)⟩

theorem ladAvoid_card_eq (L : ℕ) :
    (ladAvoid true L).card = (ladAvoid false L).card := by
  rw [ladAvoid_true_eq_image]
  exact Finset.card_image_of_injective _ (Finset.image_injective ladSwap_injective)

theorem ladSets_mono (L : ℕ) : ladSets L ⊆ ladSets (L + 1) := by
  intro t ht
  rw [mem_ladSets] at ht ⊢
  exact ⟨ht.1.trans (ladVert_mono L), ht.2⟩

/-- Members of `ladSets (L+1)` with an empty last column are exactly the
independent sets of the `2 × L` ladder. -/
theorem mem_ladSets_of_succ {L : ℕ} {t : Finset (Bool × ℕ)}
    (ht : t ∈ ladSets (L + 1)) (hf : (false, L) ∉ t) (hT : (true, L) ∉ t) :
    t ∈ ladSets L := by
  rw [mem_ladSets] at ht ⊢
  obtain ⟨hsub, hfree⟩ := ht
  refine ⟨?_, hfree⟩
  rintro ⟨c, j⟩ hp
  have hv := hsub hp
  rw [mem_ladVert] at hv ⊢
  rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hv) with h | h
  · exact h
  · rw [h] at hp
    rcases Bool.dichotomy c with rfl | rfl
    · exact absurd hp hf
    · exact absurd hp hT

/-- Erasing `(b, L)` from an independent set containing it leaves an
element of `ladAvoid b L`. -/
theorem erase_mem_ladAvoid {b : Bool} {L : ℕ} {t : Finset (Bool × ℕ)}
    (ht : t ∈ ladSets (L + 1)) (hb : (b, L) ∈ t) :
    t.erase (b, L) ∈ ladAvoid b L := by
  rw [mem_ladSets] at ht
  obtain ⟨hsub, hfree⟩ := ht
  have hU : t.erase (b, L) ⊆ ladVert L := by
    rintro ⟨c, j⟩ hp
    rw [Finset.mem_erase] at hp
    obtain ⟨hne, hp⟩ := hp
    have hv := hsub hp
    rw [mem_ladVert] at hv ⊢
    rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hv) with h | h
    · exact h
    · rw [h] at hp hne
      have h2 := hfree.2 (b, L) hb
      have hcb : c = !b := by
        rcases Bool.dichotomy c with rfl | rfl <;>
          rcases Bool.dichotomy b with rfl | rfl
        · exact absurd rfl hne
        · rfl
        · rfl
        · exact absurd rfl hne
      rw [hcb] at hp
      exact absurd hp h2
  rw [mem_ladAvoid, mem_ladSets]
  refine ⟨⟨hU, hfree.mono (Finset.erase_subset _ _)⟩, ?_⟩
  intro hC
  have hmem := Finset.mem_of_mem_erase hC
  have hv := hU hC
  rw [mem_ladVert] at hv
  have hL : 1 ≤ L := by omega
  have h1 := hfree.1 (b, L - 1) hmem
  rw [Nat.sub_add_cancel hL] at h1
  exact h1 hb

/-- Inserting `(b, L)` into an element of `ladAvoid b L` stays
independent: the rung cell `(!b, L)` and the rail predecessor
`(b, L-1)` are absent. -/
theorem mem_ladSets_succ_of_mem_ladAvoid {b : Bool} {L : ℕ}
    {u : Finset (Bool × ℕ)} (hu : u ∈ ladAvoid b L) :
    insert (b, L) u ∈ ladSets (L + 1) := by
  rw [mem_ladAvoid, mem_ladSets] at hu
  obtain ⟨⟨hsub, hfree⟩, hb⟩ := hu
  rw [mem_ladSets]
  refine ⟨?_, ⟨?_, ?_⟩⟩
  · rintro ⟨c, j⟩ hp
    rw [Finset.mem_insert] at hp
    rw [mem_ladVert]
    rcases hp with hp | hp
    · have e2 : j = L := (Prod.ext_iff.mp hp).2
      rw [e2]
      exact Nat.lt_succ_self L
    · have hv := hsub hp
      rw [mem_ladVert] at hv
      omega
  · rintro ⟨c, j⟩ hp hC
    rw [Finset.mem_insert] at hp hC
    rcases hC with hC | hC
    · have e1 : c = b := (Prod.ext_iff.mp hC).1
      have e2 : j + 1 = L := (Prod.ext_iff.mp hC).2
      rcases hp with hp | hp
      · have e4 : j = L := (Prod.ext_iff.mp hp).2
        omega
      · rw [e1, show j = L - 1 from by omega] at hp
        exact hb hp
    · rcases hp with hp | hp
      · have e1 : c = b := (Prod.ext_iff.mp hp).1
        have e2 : j = L := (Prod.ext_iff.mp hp).2
        rw [e1, e2] at hC
        have hv := hsub hC
        rw [mem_ladVert] at hv
        exact absurd hv (by omega)
      · exact hfree.1 (c, j) hp hC
  · rintro ⟨c, j⟩ hp hC
    rw [Finset.mem_insert] at hp hC
    rcases hC with hC | hC
    · have e1 : (!c) = b := (Prod.ext_iff.mp hC).1
      have e2 : j = L := (Prod.ext_iff.mp hC).2
      rcases hp with hp | hp
      · have e3 : c = b := (Prod.ext_iff.mp hp).1
        rw [e3] at e1
        rcases Bool.dichotomy b with rfl | rfl <;>
          exact absurd e1 (by decide)
      · rw [e2] at hp
        have hv := hsub hp
        rw [mem_ladVert] at hv
        exact absurd hv (by omega)
    · rcases hp with hp | hp
      · have e2 : j = L := (Prod.ext_iff.mp hp).2
        rw [e2] at hC
        have hv := hsub hC
        rw [mem_ladVert] at hv
        exact absurd hv (by omega)
      · exact hfree.2 (c, j) hp hC

/-- **Column decomposition.**  `ladSets (L+1)` is the disjoint union of
the sets with empty last column (`ladSets L`), the sets ending in
`{(false, L)}` and the sets ending in `{(true, L)}`. -/
theorem ladSets_succ (L : ℕ) :
    ladSets (L + 1) =
      ladSets L ∪
        ((ladAvoid false L).image (fun t => insert (false, L) t) ∪
          (ladAvoid true L).image fun t => insert (true, L) t) := by
  ext t
  simp only [Finset.mem_union, Finset.mem_image]
  constructor
  · intro ht
    by_cases hf : (false, L) ∈ t
    · exact Or.inr (Or.inl ⟨t.erase (false, L), erase_mem_ladAvoid ht hf,
        Finset.insert_erase hf⟩)
    · by_cases htr : (true, L) ∈ t
      · exact Or.inr (Or.inr ⟨t.erase (true, L), erase_mem_ladAvoid ht htr,
          Finset.insert_erase htr⟩)
      · exact Or.inl (mem_ladSets_of_succ ht hf htr)
  · rintro (ht | ⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩)
    · exact ladSets_mono L ht
    · exact mem_ladSets_succ_of_mem_ladAvoid hu
    · exact mem_ladSets_succ_of_mem_ladAvoid hu

/-- The `insert (b, L)` image of `ladAvoid b L` has the same cardinality:
`erase (b, L)` inverts it since `(b, L) ∉ t` for `t ⊆ ladVert L`. -/
theorem card_image_insert (b : Bool) (L : ℕ) :
    ((ladAvoid b L).image fun t => insert (b, L) t).card =
      (ladAvoid b L).card := by
  apply Finset.card_image_of_injOn
  intro t₁ ht₁ t₂ ht₂ h
  rw [Finset.mem_coe, mem_ladAvoid, mem_ladSets] at ht₁ ht₂
  have h1 : (b, L) ∉ t₁ := by
    intro hC
    have hv := ht₁.1.1 hC
    rw [mem_ladVert] at hv
    exact absurd hv (lt_irrefl _)
  have h2 : (b, L) ∉ t₂ := by
    intro hC
    have hv := ht₂.1.1 hC
    rw [mem_ladVert] at hv
    exact absurd hv (lt_irrefl _)
  have e := congrArg (Finset.erase · (b, L)) h
  rwa [Finset.erase_insert h1, Finset.erase_insert h2] at e

/-- `a(L+1) = a(L) + 2·f(L)`: one choice for the empty last column and
two for the singly-occupied one (the two rails are symmetric). -/
theorem ladSets_card_succ (L : ℕ) :
    (ladSets (L + 1)).card = (ladSets L).card + 2 * (ladAvoid false L).card := by
  have d1 : Disjoint (ladSets L)
      ((ladAvoid false L).image (fun t => insert (false, L) t) ∪
        (ladAvoid true L).image fun t => insert (true, L) t) := by
    rw [Finset.disjoint_left]
    intro t ht hB
    rw [Finset.mem_union, Finset.mem_image, Finset.mem_image] at hB
    rcases hB with ⟨u, -, rfl⟩ | ⟨u, -, rfl⟩
    · have hv := (mem_ladSets.mp ht).1 (Finset.mem_insert_self (false, L) u)
      rw [mem_ladVert] at hv
      exact absurd hv (lt_irrefl _)
    · have hv := (mem_ladSets.mp ht).1 (Finset.mem_insert_self (true, L) u)
      rw [mem_ladVert] at hv
      exact absurd hv (lt_irrefl _)
  have d2 : Disjoint ((ladAvoid false L).image fun t => insert (false, L) t)
      ((ladAvoid true L).image fun t => insert (true, L) t) := by
    rw [Finset.disjoint_left]
    intro t ht hB
    obtain ⟨u₁, -, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨u₂, hu₂, hC⟩ := Finset.mem_image.mp hB
    have hmem : (false, L) ∈ insert (true, L) u₂ := by
      rw [hC]
      exact Finset.mem_insert_self _ _
    rw [Finset.mem_insert] at hmem
    rcases hmem with hmem | hmem
    · have e1 : false = true := (Prod.ext_iff.mp hmem).1
      exact absurd e1 (by decide)
    · have hv := (mem_ladSets.mp (mem_ladAvoid.mp hu₂).1).1 hmem
      rw [mem_ladVert] at hv
      exact absurd hv (lt_irrefl _)
  rw [ladSets_succ, Finset.card_union_of_disjoint d1,
    Finset.card_union_of_disjoint d2, card_image_insert, card_image_insert,
    ladAvoid_card_eq]
  ring

/-- Elements of `ladSets L` never contain a cell of column `L`, so the
`(c, L) ∉ ·` filter is the identity on `ladSets L`. -/
theorem ladSets_filter_notMem (L : ℕ) (c : Bool) :
    (ladSets L).filter (fun t => (c, L) ∉ t) = ladSets L := by
  ext t
  rw [Finset.mem_filter]
  refine ⟨fun h => h.1, fun ht => ⟨ht, fun hC => ?_⟩⟩
  have hv := (mem_ladSets.mp ht).1 hC
  rw [mem_ladVert] at hv
  exact absurd hv (lt_irrefl _)

/-- The `insert (b, L)` image is killed by the `(b, L) ∉ ·` filter. -/
theorem ladAvoid_image_filter_same (L : ℕ) (b : Bool) :
    ((ladAvoid b L).image fun t => insert (b, L) t).filter
        (fun t => (b, L) ∉ t) = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro t hC
  rw [Finset.mem_filter] at hC
  obtain ⟨ht, hb⟩ := hC
  obtain ⟨u, -, rfl⟩ := Finset.mem_image.mp ht
  exact hb (Finset.mem_insert_self _ _)

/-- The `insert (c, L)` image with `c ≠ b` survives the `(b, L) ∉ ·`
filter. -/
theorem ladAvoid_image_filter_other (L : ℕ) (b c : Bool) (hbc : b ≠ c) :
    ((ladAvoid c L).image fun t => insert (c, L) t).filter
        (fun t => (b, L) ∉ t) =
      (ladAvoid c L).image fun t => insert (c, L) t := by
  ext t
  rw [Finset.mem_filter]
  refine ⟨fun h => h.1, fun ht => ⟨ht, fun hC => ?_⟩⟩
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ht
  rw [Finset.mem_insert] at hC
  rcases hC with hC | hC
  · have e1 : b = c := (Prod.ext_iff.mp hC).1
    exact absurd e1 hbc
  · have hv := (mem_ladSets.mp (mem_ladAvoid.mp hu).1).1 hC
    rw [mem_ladVert] at hv
    exact absurd hv (lt_irrefl _)

/-- The avoiding family at level `L+1` consists of the sets with empty
last column (`ladSets L`) together with the sets ending in `{(!b, L)}`. -/
theorem ladAvoid_succ (L : ℕ) (b : Bool) :
    ladAvoid b (L + 1) =
      ladSets L ∪ (ladAvoid (!b) L).image fun t => insert (!b, L) t := by
  have key : ∀ c : Bool,
      (ladSets (L + 1)).filter (fun t => (c, L) ∉ t) =
        ladSets L ∪ (ladAvoid (!c) L).image fun t => insert (!c, L) t := by
    intro c
    rw [ladSets_succ, Finset.filter_union, Finset.filter_union]
    rcases Bool.dichotomy c with rfl | rfl
    · rw [ladSets_filter_notMem, ladAvoid_image_filter_same,
        ladAvoid_image_filter_other L false true (by decide : false ≠ true),
        Finset.empty_union, Bool.not_false]
    · rw [ladSets_filter_notMem,
        ladAvoid_image_filter_other L true false (by decide : true ≠ false),
        ladAvoid_image_filter_same, Finset.union_empty, Bool.not_true]
  exact key b

/-- `f(L+1) = a(L) + f(L)`: an avoiding set of length `L+1` either has
empty last column or ends in `{(!b, L)}`. -/
theorem ladAvoid_succ_card (L : ℕ) (b : Bool) :
    (ladAvoid b (L + 1)).card = (ladSets L).card + (ladAvoid (!b) L).card := by
  have hd : Disjoint (ladSets L)
      ((ladAvoid (!b) L).image fun t => insert (!b, L) t) := by
    rw [Finset.disjoint_left]
    intro t ht hB
    rw [Finset.mem_image] at hB
    obtain ⟨u, -, rfl⟩ := hB
    have hv := (mem_ladSets.mp ht).1 (Finset.mem_insert_self (!b, L) u)
    rw [mem_ladVert] at hv
    exact absurd hv (lt_irrefl _)
  rw [ladAvoid_succ, Finset.card_union_of_disjoint hd, card_image_insert]

/-- **The Pell recurrence** `a(L+2) = 2·a(L+1) + a(L)`. -/
theorem ladSets_card_add_two (L : ℕ) :
    (ladSets (L + 2)).card = 2 * (ladSets (L + 1)).card + (ladSets L).card := by
  have hA : (ladSets (L + 2)).card =
      (ladSets (L + 1)).card + 2 * (ladAvoid false (L + 1)).card :=
    ladSets_card_succ (L + 1)
  have hB := ladSets_card_succ L
  have hF : (ladAvoid false (L + 1)).card =
      (ladSets L).card + (ladAvoid true L).card :=
    ladAvoid_succ_card L false
  have hG := ladAvoid_card_eq L
  omega

theorem ladSets_zero : ladSets 0 = {∅} := by
  ext t
  rw [mem_ladSets, ladVert_zero, Finset.subset_empty, Finset.mem_singleton]
  refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
  subst h
  exact ⟨fun p hp => absurd hp (Finset.notMem_empty _),
    fun p hp => absurd hp (Finset.notMem_empty _)⟩

theorem ladAvoid_zero (b : Bool) : ladAvoid b 0 = {∅} := by
  ext t
  rw [mem_ladAvoid, ladSets_zero, Finset.mem_singleton]
  refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
  subst h
  exact Finset.notMem_empty _

/-- Base count: `a(0) = 1`. -/
theorem ladSets_card_zero : (ladSets 0).card = 1 := by
  rw [ladSets_zero, Finset.card_singleton]

/-- Base count: `a(1) = 3`. -/
theorem ladSets_card_one : (ladSets 1).card = 3 := by
  have h : (ladSets 1).card = (ladSets 0).card + 2 * (ladAvoid false 0).card :=
    ladSets_card_succ 0
  rw [ladSets_card_zero, ladAvoid_zero, Finset.card_singleton] at h
  exact h

/-- Base count: `a(2) = 7`. -/
theorem ladSets_card_two : (ladSets 2).card = 7 := by
  have h2 : (ladSets 2).card = (ladSets 1).card + 2 * (ladAvoid false 1).card :=
    ladSets_card_succ 1
  have hF : (ladAvoid false 1).card = (ladSets 0).card + (ladAvoid true 0).card :=
    ladAvoid_succ_card 0 false
  simp only [ladSets_card_one, ladSets_card_zero, ladAvoid_zero,
    Finset.card_singleton] at h2 hF
  omega

/-- **Integer-normalised bound.**  `a(L)·2^{L-1} ≤ 3·5^{L-1}` for
`1 ≤ L`, i.e. `a(L) ≤ 3·(5/2)^{L-1}`: the two-step induction gives
`a(k+3)·2^{k+2} = 4·(a(k+2)·2^{k+1}) + 4·(a(k+1)·2^k) ≤ 12·5^{k+1} +
12·5^k = 72·5^k ≤ 75·5^k = 3·5^{k+2}`. -/
theorem ladSets_card_mul_two_pow_le {L : ℕ} (hL : 1 ≤ L) :
    (ladSets L).card * 2 ^ (L - 1) ≤ 3 * 5 ^ (L - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, L = k + 1 := ⟨L - 1, by omega⟩
  clear hL
  show (ladSets (k + 1)).card * 2 ^ k ≤ 3 * 5 ^ k
  induction k using Nat.twoStepInduction with
  | zero =>
      show (ladSets (0 + 1)).card * 2 ^ 0 ≤ 3 * 5 ^ 0
      rw [show (0 : ℕ) + 1 = 1 from rfl, ladSets_card_one]
      norm_num
  | one =>
      show (ladSets (1 + 1)).card * 2 ^ 1 ≤ 3 * 5 ^ 1
      rw [show (1 : ℕ) + 1 = 2 from rfl, ladSets_card_two]
      norm_num
  | more k ih ih1 =>
      have hrec : (ladSets (k + 3)).card =
          2 * (ladSets (k + 2)).card + (ladSets (k + 1)).card :=
        ladSets_card_add_two (k + 1)
      show (ladSets (k + 2 + 1)).card * 2 ^ (k + 2) ≤ 3 * 5 ^ (k + 2)
      calc (ladSets (k + 2 + 1)).card * 2 ^ (k + 2)
          = 4 * ((ladSets (k + 2)).card * 2 ^ (k + 1)) +
              4 * ((ladSets (k + 1)).card * 2 ^ k) := by
            have e1 : (2 : ℕ) ^ (k + 2) = 4 * 2 ^ k := by
              rw [pow_add]; ring
            have e2 : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := pow_succ' _ _
            rw [show k + 2 + 1 = k + 3 from rfl, hrec, e1, e2]
            ring
        _ ≤ 4 * (3 * 5 ^ (k + 1)) + 4 * (3 * 5 ^ k) :=
            add_le_add (Nat.mul_le_mul (le_refl 4) ih1)
              (Nat.mul_le_mul (le_refl 4) ih)
        _ = 72 * 5 ^ k := by
            rw [show (5 : ℕ) ^ (k + 1) = 5 * 5 ^ k from pow_succ' _ _]; ring
        _ ≤ 3 * 5 ^ (k + 2) := by
            have e : (5 : ℕ) ^ (k + 2) = 25 * 5 ^ k := by
              rw [pow_add]; ring
            rw [e]
            calc 72 * 5 ^ k ≤ 75 * 5 ^ k :=
                  Nat.mul_le_mul (by norm_num) (le_refl _)
              _ = 3 * (25 * 5 ^ k) := by ring

/-- Loose corollary for later use: `a(L) ≤ 3·5^L`. -/
theorem ladSets_card_le_three_mul_five_pow (L : ℕ) :
    (ladSets L).card ≤ 3 * 5 ^ L := by
  rcases Nat.eq_zero_or_pos L with rfl | hL
  · rw [ladSets_card_zero]; norm_num
  · calc (ladSets L).card
        ≤ (ladSets L).card * 2 ^ (L - 1) := by
          apply Nat.le_mul_of_pos_right
          exact pow_pos (by norm_num) _
      _ ≤ 3 * 5 ^ (L - 1) := ladSets_card_mul_two_pow_le hL
      _ ≤ 3 * 5 ^ L :=
          Nat.mul_le_mul (le_refl 3)
            (pow_le_pow_right₀ (by norm_num) (Nat.sub_le L 1))

end JSP000728
