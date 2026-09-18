import JSPProblem.QuadCyl
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.FinCases

/-!
# JSP-000728 — independent sets of the `5 × L` cyclic strip

The *5-rail cyclic strip* of length `L` has vertex set `Fin 5 × range L`
(five rails of `L` cells) with edges between consecutive cells on the
same rail and between *adjacent* cells in the same column — each column
carries a copy of the cycle `C5`, not a clique.  An independent set
therefore carries at most two vertices per column, and two co-columnar
cells must be at *cyclic distance two*: the legal column states are

  `∅`, `{0}`, `{1}`, `{2}`, `{3}`, `{4}`,
  `{0,2}`, `{1,3}`, `{2,4}`, `{3,0}`, `{4,1}`

(eleven states), and a state may follow `X` iff it is disjoint from `X`
(the vertical edges).  Every distance-2 pair has the unique
representative `{a, a+2}` for `a ∈ Fin 5`.  The counts
`T(L) = (pentSets L).card` satisfy

  `T(0) = 1`, `T(1) = 11`, `T(2) = 81`,
  `T(L+3) + T(L) = 7·T(L+2) + 5·T(L+1)`

(`1, 11, 81, 621, 4741, …`, growth rate `≈ 7.617` per column, the
Perron root of `λ³ = 7λ² + 5λ − 1`, i.e. `≈ 1.505` per vertex —
below the ladder rate `√(1 + √2) ≈ 1.5538`).

* `pentVert L` : the vertex finset `Finset.univ ×ˢ Finset.range L`.
* `pentFree t` : the independent-set predicate; decidable.
* `pentSets L` : all independent sets, as a `powerset.filter`.
* `pentAvoid r L` : independent sets avoiding `(r, L-1)` — those that
  can be extended by the singleton `{(r, L)}`.
* `pentAvoid2 a L` : independent sets avoiding both `(a, L-1)` and
  `(a + 2, L-1)` — those extendable by the distance-2 pair
  `{(a, L), (a+2, L)}`.
* `pentRotF k` / `pentRotN k` : rotation of the five rails by `k`
  positions (`i ↦ i + k` modulo `5`, realised through `Fin.val`
  arithmetic), a bijection preserving `pentFree`; it identifies the
  avoiding families of any two rails (`pentAvoid_card_eq`) and of any
  two distance-2 pairs (`pentAvoid2_card_eq`).
* Splitting `pentSets (L+1)` by the last column gives
  `T(L+1) = T(L) + 5·A(L) + 5·B(L)`; the avoiding families satisfy
  `A(L+1) = T(L) + 4·A(L) + 3·B(L)` and
  `B(L+1) = T(L) + 3·A(L) + 2·B(L)`
  (`pentSets_card_succ`, `pentAvoid_succ_card`, `pentAvoid2_succ_card`).
  Eliminating yields the exact third-order recurrence
  `pentSets_card_add_three` and the two-step bound
  `T(L+2) ≤ 6·T(L+1) + 15·T(L)` (`pentSets_card_add_two_le`).
* `pentSets_card_mul_four_pow_le` : the integer-normalised bound
  `T(L)·4^L ≤ 2·31^L` (i.e. `T(L) ≤ 2·(31/4)^L`), per-vertex rate
  `(31/4)^{1/5} ≈ 1.505` — strictly below the ladder rate.
-/

namespace JSP000728

/-- The vertex set of the 5-rail strip: `Fin 5 × range L`. -/
def pentVert (L : ℕ) : Finset (Fin 5 × ℕ) :=
  Finset.univ.product (Finset.range L)

theorem mem_pentVert {r : Fin 5} {j L : ℕ} :
    (r, j) ∈ pentVert L ↔ j < L := by
  simp [pentVert]

theorem pentVert_zero : pentVert 0 = ∅ := by
  ext ⟨c, j⟩
  simp [mem_pentVert]

theorem pentVert_mono (L : ℕ) : pentVert L ⊆ pentVert (L + 1) := by
  rintro ⟨c, j⟩ hp
  rw [mem_pentVert] at hp ⊢
  omega

/-- `t` is an *independent set* of the `5 × L` strip: no cell carries
its rail-successor `(r, j+1)`, and two cells of the same column must be
equal or at cyclic distance two (`r` and `r + 2`, i.e. non-adjacent in
`C5`). -/
def pentFree (t : Finset (Fin 5 × ℕ)) : Prop :=
  (∀ p ∈ t, (p.1, p.2 + 1) ∉ t) ∧
    ∀ p ∈ t, ∀ q ∈ t, p.2 = q.2 →
      p.1 = q.1 ∨ p.1 + 2 = q.1 ∨ q.1 + 2 = p.1

instance decidablePentFree (t : Finset (Fin 5 × ℕ)) :
    Decidable (pentFree t) := by
  unfold pentFree; infer_instance

theorem pentFree.mono {t u : Finset (Fin 5 × ℕ)} (ht : pentFree t)
    (hu : u ⊆ t) : pentFree u :=
  ⟨fun p hp hC => ht.1 p (hu hp) (hu hC),
   fun p hp q hq hpq => ht.2 p (hu hp) q (hu hq) hpq⟩

/-- The family of independent sets of the `5 × L` strip. -/
def pentSets (L : ℕ) : Finset (Finset (Fin 5 × ℕ)) :=
  (pentVert L).powerset.filter pentFree

theorem mem_pentSets {L : ℕ} {t : Finset (Fin 5 × ℕ)} :
    t ∈ pentSets L ↔ t ⊆ pentVert L ∧ pentFree t := by
  simp [pentSets]

theorem pentSets_mono (L : ℕ) : pentSets L ⊆ pentSets (L + 1) := by
  intro t ht
  rw [mem_pentSets] at ht ⊢
  exact ⟨ht.1.trans (pentVert_mono L), ht.2⟩

/-- The independent sets avoiding `(r, L-1)`: exactly those that can be
extended by placing `(r, L)` in column `L`. -/
def pentAvoid (r : Fin 5) (L : ℕ) : Finset (Finset (Fin 5 × ℕ)) :=
  (pentSets L).filter fun t => (r, L - 1) ∉ t

theorem mem_pentAvoid {r : Fin 5} {L : ℕ} {t : Finset (Fin 5 × ℕ)} :
    t ∈ pentAvoid r L ↔ t ∈ pentSets L ∧ (r, L - 1) ∉ t :=
  Finset.mem_filter

/-- The independent sets avoiding both `(a, L-1)` and `(a+2, L-1)`:
exactly those that can be extended by the distance-2 pair
`{(a, L), (a+2, L)}`. -/
def pentAvoid2 (a : Fin 5) (L : ℕ) : Finset (Finset (Fin 5 × ℕ)) :=
  (pentSets L).filter fun t => (a, L - 1) ∉ t ∧ (a + 2, L - 1) ∉ t

theorem mem_pentAvoid2 {a : Fin 5} {L : ℕ} {t : Finset (Fin 5 × ℕ)} :
    t ∈ pentAvoid2 a L ↔
      t ∈ pentSets L ∧ (a, L - 1) ∉ t ∧ (a + 2, L - 1) ∉ t :=
  Finset.mem_filter

/-! ### `Fin 5` distance-2 arithmetic -/

theorem pent_val_add_two (c : Fin 5) : (c + 2).val = (c.val + 2) % 5 := by
  rw [Fin.val_add, show (2 : Fin 5).val = 2 from by decide]

theorem pent_val_add_three (c : Fin 5) : (c + 3).val = (c.val + 3) % 5 := by
  rw [Fin.val_add, show (3 : Fin 5).val = 3 from by decide]

/-- The *other* distance-2 neighbour: `c + 2 = r ↔ c = r + 3` on
`Fin 5` (subtracting `2` is adding `3`). -/
theorem pent_add_two_eq_iff {c r : Fin 5} : c + 2 = r ↔ c = r + 3 := by
  constructor
  · intro h
    apply Fin.ext
    have hv := congrArg Fin.val h
    rw [pent_val_add_two] at hv
    rw [pent_val_add_three]
    have h1 := c.isLt; have h2 := r.isLt
    omega
  · intro h
    apply Fin.ext
    have hv := congrArg Fin.val h
    rw [pent_val_add_three] at hv
    rw [pent_val_add_two]
    have h1 := c.isLt; have h2 := r.isLt
    omega

/-- `c + 3 + 2 = c` on `Fin 5`. -/
theorem pent_add_three_add_two (c : Fin 5) : c + 3 + 2 = c := by
  apply Fin.ext
  rw [pent_val_add_two, pent_val_add_three]
  have h := c.isLt
  omega

theorem pent_add_two_ne_self (a : Fin 5) : a + 2 ≠ a := by
  intro h
  have hv := congrArg Fin.val h
  rw [pent_val_add_two] at hv
  have h1 := a.isLt
  omega

theorem pent_self_ne_add_two (a : Fin 5) : a ≠ a + 2 := by
  intro h
  exact pent_add_two_ne_self a h.symm

/-- Exhaustion of `Fin 5`: every rail is `0`, `1`, `2`, `3`, or `4`. -/
theorem fin5_cases (c : Fin 5) :
    c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 := by
  have hv : c.val = 0 ∨ c.val = 1 ∨ c.val = 2 ∨ c.val = 3 ∨ c.val = 4 := by
    have h := c.isLt; omega
  rcases hv with h | h | h | h | h
  · exact Or.inl (Fin.ext (h.trans (by decide)))
  · exact Or.inr (Or.inl (Fin.ext (h.trans (by decide))))
  · exact Or.inr (Or.inr (Or.inl (Fin.ext (h.trans (by decide)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext (h.trans (by decide))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Fin.ext (h.trans (by decide))))))

/-! ### Rail rotation -/

/-- Rotation of the five rails by `k` positions: `i ↦ i + k` modulo `5`,
realised through `Fin.val` arithmetic. -/
def pentRotF (k : ℕ) : Fin 5 → Fin 5 :=
  fun c => ⟨(c.val + k) % 5, Nat.mod_lt _ (by norm_num)⟩

theorem pentRotF_val (k : ℕ) (c : Fin 5) :
    (pentRotF k c).val = (c.val + k) % 5 := rfl

theorem pentRotF_add_two (k : ℕ) (c : Fin 5) :
    pentRotF k c + 2 = pentRotF k (c + 2) := by
  apply Fin.ext
  rw [pent_val_add_two]
  show ((c.val + k) % 5 + 2) % 5 = ((c + 2).val + k) % 5
  rw [pent_val_add_two]
  omega

/-- The point map rotating rails by `k`, fixing the column. -/
def pentRotN (k : ℕ) : Fin 5 × ℕ → Fin 5 × ℕ :=
  fun p => (pentRotF k p.1, p.2)

theorem pentRotN_comp (k k' : ℕ) (p : Fin 5 × ℕ) :
    pentRotN k (pentRotN k' p) = pentRotN (k' + k) p := by
  rcases p with ⟨c, j⟩
  refine Prod.ext_iff.mpr ⟨Fin.ext ?_, rfl⟩
  show ((c.val + k') % 5 + k) % 5 = (c.val + (k' + k)) % 5
  omega

theorem pentRotN_mod (k : ℕ) (p : Fin 5 × ℕ) :
    pentRotN k p = pentRotN (k % 5) p := by
  rcases p with ⟨c, j⟩
  refine Prod.ext_iff.mpr ⟨Fin.ext ?_, rfl⟩
  show (c.val + k) % 5 = (c.val + k % 5) % 5
  omega

theorem pentRotN_injective (k : ℕ) : Function.Injective (pentRotN k) := by
  rintro ⟨c, j⟩ ⟨c', j'⟩ h
  obtain ⟨h1, h2⟩ := Prod.ext_iff.mp h
  have hc : c = c' := by
    apply Fin.ext
    have h3 : (c.val + k) % 5 = (c'.val + k) % 5 := congrArg Fin.val h1
    have h4 := c.isLt; have h5 := c'.isLt
    omega
  exact Prod.ext_iff.mpr ⟨hc, h2⟩

theorem pentRotN_leftInv (k : ℕ) :
    Function.LeftInverse (pentRotN (5 - k % 5)) (pentRotN k) := by
  intro p
  rw [pentRotN_comp]
  rcases p with ⟨c, j⟩
  refine Prod.ext_iff.mpr ⟨Fin.ext ?_, rfl⟩
  show (c.val + (k + (5 - k % 5))) % 5 = c.val
  have h := c.isLt
  omega

theorem mem_image_pentRotN {k : ℕ} {p : Fin 5 × ℕ}
    {t : Finset (Fin 5 × ℕ)} :
    p ∈ t.image (pentRotN k) ↔ pentRotN (5 - k % 5) p ∈ t := by
  rw [Finset.mem_image]
  constructor
  · rintro ⟨q, hq, rfl⟩
    rwa [pentRotN_leftInv]
  · intro hp
    refine ⟨pentRotN (5 - k % 5) p, hp, ?_⟩
    rw [pentRotN_comp]
    rcases p with ⟨c, j⟩
    refine Prod.ext_iff.mpr ⟨Fin.ext ?_, rfl⟩
    show (c.val + ((5 - k % 5) + k)) % 5 = c.val
    have h := c.isLt
    omega

theorem image_pentRotN_image (k k' : ℕ) (t : Finset (Fin 5 × ℕ)) :
    (t.image (pentRotN k)).image (pentRotN k') =
      t.image (pentRotN (k + k')) := by
  rw [Finset.image_image]
  congr 1
  funext p
  exact pentRotN_comp k' k p

theorem pentRotN_zero : pentRotN 0 = id := by
  funext ⟨c, j⟩
  refine Prod.ext_iff.mpr ⟨Fin.ext ?_, rfl⟩
  show (c.val + 0) % 5 = c.val
  have h := c.isLt
  omega

theorem pentRotN_eq_fun (k : ℕ) : pentRotN k = pentRotN (k % 5) :=
  funext fun p => pentRotN_mod k p

/-- Rotating by `k` and then by `5 - k % 5` is the identity image. -/
theorem image_pentRotN_self (k : ℕ) (t : Finset (Fin 5 × ℕ)) :
    (t.image (pentRotN k)).image (pentRotN (5 - k % 5)) = t := by
  rw [image_pentRotN_image]
  have e : k + (5 - k % 5) = 5 * (k / 5 + 1) := by omega
  rw [e]
  have hid : pentRotN (5 * (k / 5 + 1)) = id := by
    rw [pentRotN_eq_fun, show (5 * (k / 5 + 1)) % 5 = 0 by omega,
      pentRotN_zero]
  rw [hid, Finset.image_id]

theorem image_pentRotN_self' (k : ℕ) (t : Finset (Fin 5 × ℕ)) :
    (t.image (pentRotN (5 - k % 5))).image (pentRotN k) = t := by
  rw [image_pentRotN_image]
  have e : (5 - k % 5) + k = 5 * (k / 5 + 1) := by omega
  rw [e]
  have hid : pentRotN (5 * (k / 5 + 1)) = id := by
    rw [pentRotN_eq_fun, show (5 * (k / 5 + 1)) % 5 = 0 by omega,
      pentRotN_zero]
  rw [hid, Finset.image_id]

theorem pentVert_image_pentRotN {k : ℕ} {L : ℕ} {t : Finset (Fin 5 × ℕ)}
    (ht : t ⊆ pentVert L) : t.image (pentRotN k) ⊆ pentVert L := by
  rintro ⟨c, j⟩ hp
  rw [mem_image_pentRotN] at hp
  have hv := ht hp
  rw [mem_pentVert] at hv ⊢
  exact hv

theorem pentFree_image_pentRotN {k : ℕ} {t : Finset (Fin 5 × ℕ)}
    (ht : pentFree t) : pentFree (t.image (pentRotN k)) := by
  constructor
  · rintro ⟨c, j⟩ hp hC
    rw [mem_image_pentRotN] at hp hC
    exact ht.1 (pentRotN (5 - k % 5) (c, j)) hp hC
  · rintro ⟨c, j⟩ hp ⟨c', j'⟩ hq hjj'
    rw [mem_image_pentRotN] at hp hq
    have h := ht.2 (pentRotN (5 - k % 5) (c, j)) hp
      (pentRotN (5 - k % 5) (c', j')) hq hjj'
    rcases h with h | h | h
    · refine Or.inl ?_
      have e : (c.val + (5 - k % 5)) % 5 = (c'.val + (5 - k % 5)) % 5 :=
        congrArg Fin.val h
      have hcc : c = c' := by
        apply Fin.ext
        have h1 := c.isLt; have h2 := c'.isLt
        omega
      exact hcc
    · refine Or.inr (Or.inl ?_)
      have e : ((c.val + (5 - k % 5)) % 5 + 2) % 5 =
          (c'.val + (5 - k % 5)) % 5 := congrArg Fin.val h
      have hcc : c + 2 = c' := by
        apply Fin.ext
        rw [pent_val_add_two]
        have h1 := c.isLt; have h2 := c'.isLt
        omega
      exact hcc
    · refine Or.inr (Or.inr ?_)
      have e : ((c'.val + (5 - k % 5)) % 5 + 2) % 5 =
          (c.val + (5 - k % 5)) % 5 := congrArg Fin.val h
      have hcc : c' + 2 = c := by
        apply Fin.ext
        rw [pent_val_add_two]
        have h1 := c.isLt; have h2 := c'.isLt
        omega
      exact hcc

theorem mem_pentSets_image_pentRotN {k : ℕ} {L : ℕ}
    {u : Finset (Fin 5 × ℕ)} (hu : u ∈ pentSets L) :
    u.image (pentRotN k) ∈ pentSets L := by
  rw [mem_pentSets] at hu ⊢
  exact ⟨pentVert_image_pentRotN hu.1, pentFree_image_pentRotN hu.2⟩

/-- **Rail symmetry.**  Rotating the rails identifies the avoiding
families of `r` and of `r + k` (mod `5`). -/
theorem pentAvoid_rotN_eq_image (r : Fin 5) (k : ℕ) (L : ℕ) :
    pentAvoid (pentRotF k r) L =
      (pentAvoid r L).image fun t => t.image (pentRotN k) := by
  ext u
  rw [mem_pentAvoid, Finset.mem_image]
  constructor
  · rintro ⟨hu, hb⟩
    refine ⟨u.image (pentRotN (5 - k % 5)), ?_, image_pentRotN_self' k u⟩
    rw [mem_pentAvoid]
    refine ⟨mem_pentSets_image_pentRotN hu, fun hC => hb ?_⟩
    have hm := mem_image_pentRotN.mp hC
    have e : pentRotN (5 - (5 - k % 5) % 5) (r, L - 1) =
        (pentRotF k r, L - 1) := by
      exact Prod.ext_iff.mpr ⟨Fin.ext (by
        show (r.val + (5 - (5 - k % 5) % 5)) % 5 = (r.val + k) % 5
        have h1 := r.isLt
        omega), rfl⟩
    exact e ▸ hm
  · rintro ⟨t, ht, rfl⟩
    rw [mem_pentAvoid] at ht
    obtain ⟨ht, hb⟩ := ht
    refine ⟨mem_pentSets_image_pentRotN ht, fun hC => hb ?_⟩
    have hm := mem_image_pentRotN.mp hC
    have e : pentRotN (5 - k % 5) (pentRotF k r, L - 1) = (r, L - 1) := by
      exact Prod.ext_iff.mpr ⟨Fin.ext (by
        show ((r.val + k) % 5 + (5 - k % 5)) % 5 = r.val
        have h1 := r.isLt
        omega), rfl⟩
    rwa [e] at hm

/-- Rotating the rails also identifies the pair-avoiding families. -/
theorem pentAvoid2_rotN_eq_image (a : Fin 5) (k : ℕ) (L : ℕ) :
    pentAvoid2 (pentRotF k a) L =
      (pentAvoid2 a L).image fun t => t.image (pentRotN k) := by
  ext u
  rw [mem_pentAvoid2, Finset.mem_image, pentRotF_add_two]
  constructor
  · rintro ⟨hu, hb1, hb2⟩
    refine ⟨u.image (pentRotN (5 - k % 5)), ?_, image_pentRotN_self' k u⟩
    rw [mem_pentAvoid2]
    refine ⟨mem_pentSets_image_pentRotN hu, fun hC => hb1 ?_,
      fun hC => hb2 ?_⟩
    · have hm := mem_image_pentRotN.mp hC
      have e : pentRotN (5 - (5 - k % 5) % 5) (a, L - 1) =
          (pentRotF k a, L - 1) := by
        exact Prod.ext_iff.mpr ⟨Fin.ext (by
          show (a.val + (5 - (5 - k % 5) % 5)) % 5 = (a.val + k) % 5
          have h1 := a.isLt
          omega), rfl⟩
      exact e ▸ hm
    · have hm := mem_image_pentRotN.mp hC
      have e : pentRotN (5 - (5 - k % 5) % 5) (a + 2, L - 1) =
          (pentRotF k (a + 2), L - 1) := by
        exact Prod.ext_iff.mpr ⟨Fin.ext (by
          show ((a + 2).val + (5 - (5 - k % 5) % 5)) % 5 =
            ((a + 2).val + k) % 5
          have h1 := a.isLt
          omega), rfl⟩
      exact e ▸ hm
  · rintro ⟨t, ht, rfl⟩
    rw [mem_pentAvoid2] at ht
    obtain ⟨ht, hb1, hb2⟩ := ht
    refine ⟨mem_pentSets_image_pentRotN ht, fun hC => hb1 ?_,
      fun hC => hb2 ?_⟩
    · have hm := mem_image_pentRotN.mp hC
      have e : pentRotN (5 - k % 5) (pentRotF k a, L - 1) = (a, L - 1) := by
        exact Prod.ext_iff.mpr ⟨Fin.ext (by
          show ((a.val + k) % 5 + (5 - k % 5)) % 5 = a.val
          have h1 := a.isLt
          omega), rfl⟩
      rwa [e] at hm
    · have hm := mem_image_pentRotN.mp hC
      have e : pentRotN (5 - k % 5) (pentRotF k (a + 2), L - 1) =
          (a + 2, L - 1) := by
        exact Prod.ext_iff.mpr ⟨Fin.ext (by
          show (((a + 2).val + k) % 5 + (5 - k % 5)) % 5 = (a + 2).val
          have h1 := a.isLt
          omega), rfl⟩
      rwa [e] at hm

/-- All five singleton-avoiding families have the same cardinality. -/
theorem pentAvoid_card_eq (r r' : Fin 5) (L : ℕ) :
    (pentAvoid r L).card = (pentAvoid r' L).card := by
  have h : pentRotF (r'.val + 5 - r.val) r = r' := by
    apply Fin.ext
    show (r.val + (r'.val + 5 - r.val)) % 5 = r'.val
    have h1 := r.isLt; have h2 := r'.isLt
    omega
  rw [← h, pentAvoid_rotN_eq_image]
  exact (Finset.card_image_of_injective _
    (Finset.image_injective (pentRotN_injective _))).symm

/-- All five distance-2-pair-avoiding families have the same
cardinality. -/
theorem pentAvoid2_card_eq (a b : Fin 5) (L : ℕ) :
    (pentAvoid2 a L).card = (pentAvoid2 b L).card := by
  have h : pentRotF (b.val + 5 - a.val) a = b := by
    apply Fin.ext
    show (a.val + (b.val + 5 - a.val)) % 5 = b.val
    have h1 := a.isLt; have h2 := b.isLt
    omega
  rw [← h, pentAvoid2_rotN_eq_image]
  exact (Finset.card_image_of_injective _
    (Finset.image_injective (pentRotN_injective _))).symm

/-! ### Column decomposition -/

/-- Members of `pentSets (L+1)` with an empty last column are exactly
the independent sets of the `5 × L` strip. -/
theorem mem_pentSets_of_succ {L : ℕ} {t : Finset (Fin 5 × ℕ)}
    (ht : t ∈ pentSets (L + 1)) (hf : ∀ r : Fin 5, (r, L) ∉ t) :
    t ∈ pentSets L := by
  rw [mem_pentSets] at ht ⊢
  obtain ⟨hsub, hfree⟩ := ht
  refine ⟨?_, hfree⟩
  rintro ⟨c, j⟩ hp
  have hv := hsub hp
  rw [mem_pentVert] at hv ⊢
  rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hv) with h | h
  · exact h
  · rw [h] at hp
    exact absurd hp (hf c)

/-- Erasing `(r, L)` from an independent set containing it — and no
other column-`L` cell, i.e. both distance-2 neighbours `(r+2, L)` and
`(r+3, L)` absent — leaves an element of `pentAvoid r L`. -/
theorem erase_mem_pentAvoid {r : Fin 5} {L : ℕ} {t : Finset (Fin 5 × ℕ)}
    (ht : t ∈ pentSets (L + 1)) (hb : (r, L) ∈ t)
    (hn2 : (r + 2, L) ∉ t) (hn3 : (r + 3, L) ∉ t) :
    t.erase (r, L) ∈ pentAvoid r L := by
  rw [mem_pentSets] at ht
  obtain ⟨hsub, hfree⟩ := ht
  have hU : t.erase (r, L) ⊆ pentVert L := by
    rintro ⟨c, j⟩ hp
    rw [Finset.mem_erase] at hp
    obtain ⟨hne, hp⟩ := hp
    have hv := hsub hp
    rw [mem_pentVert] at hv ⊢
    rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hv) with h | h
    · exact h
    · rw [h] at hp hne
      have hrc := hfree.2 (r, L) hb (c, L) hp rfl
      rcases hrc with hrc | hrc | hrc
      · have hcc : c = r := hrc.symm
        exfalso
        exact hne (Prod.ext_iff.mpr ⟨hcc, rfl⟩)
      · have hcc : c = r + 2 := hrc.symm
        exfalso
        exact hn2 (by rwa [hcc] at hp)
      · have hcc : c = r + 3 := pent_add_two_eq_iff.mp hrc
        exfalso
        exact hn3 (by rwa [hcc] at hp)
  rw [mem_pentAvoid, mem_pentSets]
  refine ⟨⟨hU, hfree.mono (Finset.erase_subset _ _)⟩, ?_⟩
  intro hC
  have hmem := Finset.mem_of_mem_erase hC
  have hv := hU hC
  rw [mem_pentVert] at hv
  have hL : 1 ≤ L := by omega
  have h1 := hfree.1 (r, L - 1) hmem
  rw [Nat.sub_add_cancel hL] at h1
  exact h1 hb

/-- Erasing the distance-2 pair `{(a, L), (a+2, L)}` from an independent
set containing it leaves an element of `pentAvoid2 a L` (the `C5`
condition kills every other cell of column `L`: a cell compatible with
both `a` and `a+2` lies in `{a, a+2, a+3} ∩ {a, a+2, a+4} = {a, a+2}`). -/
theorem erase2_mem_pentAvoid2 {a : Fin 5} {L : ℕ}
    {t : Finset (Fin 5 × ℕ)}
    (ht : t ∈ pentSets (L + 1)) (h1 : (a, L) ∈ t) (h2 : (a + 2, L) ∈ t) :
    (t.erase (a, L)).erase (a + 2, L) ∈ pentAvoid2 a L := by
  rw [mem_pentSets] at ht
  obtain ⟨hsub, hfree⟩ := ht
  have hU : (t.erase (a, L)).erase (a + 2, L) ⊆ pentVert L := by
    rintro ⟨c, j⟩ hp
    rw [Finset.mem_erase, Finset.mem_erase] at hp
    obtain ⟨hne2, hne1, hp⟩ := hp
    have hv := hsub hp
    rw [mem_pentVert] at hv ⊢
    rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hv) with h | h
    · exact h
    · rw [h] at hp hne1 hne2
      have hc1 := hfree.2 (a, L) h1 (c, L) hp rfl
      have hc2 := hfree.2 (a + 2, L) h2 (c, L) hp rfl
      rcases hc1 with e | e | e
      · exfalso
        exact hne1 (Prod.ext_iff.mpr ⟨e.symm, rfl⟩)
      · exfalso
        exact hne2 (Prod.ext_iff.mpr ⟨e.symm, rfl⟩)
      · -- e : c + 2 = a, i.e. c = a + 3; but c must also be compatible
        -- with a + 2, which forces c ∈ {a, a+2, a+4} — contradiction.
        rcases hc2 with e2 | e2 | e2
        · exfalso
          exact hne2 (Prod.ext_iff.mpr ⟨e2.symm, rfl⟩)
        · exfalso
          have hv1 := congrArg Fin.val e2
          have hv2 := congrArg Fin.val e
          simp only [pent_val_add_two] at hv1 hv2
          have ha := a.isLt; have hc := c.isLt
          omega
        · exfalso
          have e3 : a = a + 2 := e.symm.trans e2
          exact pent_self_ne_add_two a e3
  rw [mem_pentAvoid2, mem_pentSets]
  refine ⟨⟨hU, hfree.mono
    ((Finset.erase_subset _ _).trans (Finset.erase_subset _ _))⟩, ?_, ?_⟩
  · intro hC
    have hmem := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hC)
    have hv := hU hC
    rw [mem_pentVert] at hv
    have hL : 1 ≤ L := by omega
    have h3 := hfree.1 (a, L - 1) hmem
    rw [Nat.sub_add_cancel hL] at h3
    exact h3 h1
  · intro hC
    have hmem := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hC)
    have hv := hU hC
    rw [mem_pentVert] at hv
    have hL : 1 ≤ L := by omega
    have h3 := hfree.1 (a + 2, L - 1) hmem
    rw [Nat.sub_add_cancel hL] at h3
    exact h3 h2

/-- Inserting `(r, L)` into an element of `pentAvoid r L` stays
independent: the other column-`L` cells and the rail predecessor
`(r, L-1)` are absent. -/
theorem mem_pentSets_succ_of_mem_pentAvoid {r : Fin 5} {L : ℕ}
    {u : Finset (Fin 5 × ℕ)} (hu : u ∈ pentAvoid r L) :
    insert (r, L) u ∈ pentSets (L + 1) := by
  rw [mem_pentAvoid, mem_pentSets] at hu
  obtain ⟨⟨hsub, hfree⟩, hb⟩ := hu
  rw [mem_pentSets]
  refine ⟨?_, ⟨?_, ?_⟩⟩
  · rintro ⟨c, j⟩ hp
    rw [Finset.mem_insert] at hp
    rw [mem_pentVert]
    rcases hp with hp | hp
    · have e2 : j = L := (Prod.ext_iff.mp hp).2
      rw [e2]
      exact Nat.lt_succ_self L
    · have hv := hsub hp
      rw [mem_pentVert] at hv
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
        rw [mem_pentVert] at hv
        omega
      · exact hfree.1 (c, j) hp hC
  · rintro ⟨c, j⟩ hp ⟨c', j'⟩ hq hjj'
    rw [Finset.mem_insert] at hp hq
    rcases hp with hp | hp
    · have ec : c = r := (Prod.ext_iff.mp hp).1
      have ej : j = L := (Prod.ext_iff.mp hp).2
      rcases hq with hq | hq
      · have ec' : c' = r := (Prod.ext_iff.mp hq).1
        exact Or.inl (ec.trans ec'.symm)
      · rw [ej] at hjj'
        have hv := hsub hq
        rw [mem_pentVert] at hv
        omega
    · rcases hq with hq | hq
      · have ej' : j' = L := (Prod.ext_iff.mp hq).2
        rw [ej'] at hjj'
        have hv := hsub hp
        rw [mem_pentVert] at hv
        omega
      · exact hfree.2 (c, j) hp (c', j') hq hjj'

/-- Inserting the distance-2 pair `{(a, L), (a+2, L)}` into an element
of `pentAvoid2 a L` stays independent. -/
theorem mem_pentSets_succ_of_mem_pentAvoid2 {a : Fin 5} {L : ℕ}
    {u : Finset (Fin 5 × ℕ)} (hu : u ∈ pentAvoid2 a L) :
    insert (a, L) (insert (a + 2, L) u) ∈ pentSets (L + 1) := by
  rw [mem_pentAvoid2, mem_pentSets] at hu
  obtain ⟨⟨hsub, hfree⟩, hb1, hb2⟩ := hu
  rw [mem_pentSets]
  refine ⟨?_, ⟨?_, ?_⟩⟩
  · rintro ⟨c, j⟩ hp
    rw [Finset.mem_insert, Finset.mem_insert] at hp
    rw [mem_pentVert]
    rcases hp with hp | hp | hp
    · have e : j = L := (Prod.ext_iff.mp hp).2
      rw [e]; exact Nat.lt_succ_self L
    · have e : j = L := (Prod.ext_iff.mp hp).2
      rw [e]; exact Nat.lt_succ_self L
    · have hv := hsub hp
      rw [mem_pentVert] at hv
      omega
  · rintro ⟨c, j⟩ hp hC
    rw [Finset.mem_insert, Finset.mem_insert] at hp hC
    rcases hC with hC | hC | hC
    · have e1 : c = a := (Prod.ext_iff.mp hC).1
      have e2 : j + 1 = L := (Prod.ext_iff.mp hC).2
      rcases hp with hp | hp | hp
      · have e4 : j = L := (Prod.ext_iff.mp hp).2
        omega
      · have e4 : j = L := (Prod.ext_iff.mp hp).2
        omega
      · rw [e1, show j = L - 1 from by omega] at hp
        exact hb1 hp
    · have e1 : c = a + 2 := (Prod.ext_iff.mp hC).1
      have e2 : j + 1 = L := (Prod.ext_iff.mp hC).2
      rcases hp with hp | hp | hp
      · have e4 : j = L := (Prod.ext_iff.mp hp).2
        omega
      · have e4 : j = L := (Prod.ext_iff.mp hp).2
        omega
      · rw [e1, show j = L - 1 from by omega] at hp
        exact hb2 hp
    · rcases hp with hp | hp | hp
      · have e3 : c = a := (Prod.ext_iff.mp hp).1
        have e4 : j = L := (Prod.ext_iff.mp hp).2
        rw [e3, e4] at hC
        have hv : (a, L + 1) ∈ pentVert L := hsub hC
        rw [mem_pentVert] at hv
        omega
      · have e3 : c = a + 2 := (Prod.ext_iff.mp hp).1
        have e4 : j = L := (Prod.ext_iff.mp hp).2
        rw [e3, e4] at hC
        have hv : (a + 2, L + 1) ∈ pentVert L := hsub hC
        rw [mem_pentVert] at hv
        omega
      · exact hfree.1 (c, j) hp hC
  · rintro ⟨c, j⟩ hp ⟨c', j'⟩ hq hjj'
    rw [Finset.mem_insert, Finset.mem_insert] at hp hq
    rcases hp with hp | hp | hp
    · have e1 : c = a := (Prod.ext_iff.mp hp).1
      have e2 : j = L := (Prod.ext_iff.mp hp).2
      rcases hq with hq | hq | hq
      · have e3 : c' = a := (Prod.ext_iff.mp hq).1
        exact Or.inl (e1.trans e3.symm)
      · have e3 : c' = a + 2 := (Prod.ext_iff.mp hq).1
        exact Or.inr (Or.inl (by rw [e1, e3]))
      · have hjj : j = j' := hjj'
        have e5 : j' = L := by omega
        rw [e5] at hq
        have hv := hsub hq
        rw [mem_pentVert] at hv
        omega
    · have e1 : c = a + 2 := (Prod.ext_iff.mp hp).1
      have e2 : j = L := (Prod.ext_iff.mp hp).2
      rcases hq with hq | hq | hq
      · have e3 : c' = a := (Prod.ext_iff.mp hq).1
        exact Or.inr (Or.inr (by rw [e3, e1]))
      · have e3 : c' = a + 2 := (Prod.ext_iff.mp hq).1
        exact Or.inl (e1.trans e3.symm)
      · have hjj : j = j' := hjj'
        have e5 : j' = L := by omega
        rw [e5] at hq
        have hv := hsub hq
        rw [mem_pentVert] at hv
        omega
    · rcases hq with hq | hq | hq
      · have e3 : c' = a := (Prod.ext_iff.mp hq).1
        have e4 : j' = L := (Prod.ext_iff.mp hq).2
        have hjj : j = j' := hjj'
        have hv := hsub hp
        rw [mem_pentVert] at hv
        omega
      · have e3 : c' = a + 2 := (Prod.ext_iff.mp hq).1
        have e4 : j' = L := (Prod.ext_iff.mp hq).2
        have hjj : j = j' := hjj'
        have hv := hsub hp
        rw [mem_pentVert] at hv
        omega
      · exact hfree.2 (c, j) hp (c', j') hq hjj'

/-- **Pair column lemma.**  If an independent set of the `5 × (L+1)`
strip contains the distance-2 pair `{(c, L), (c+2, L)}` in its last
column, then it is the double-insert of an element of `pentAvoid2 c L`
(every distance-2 pair has a unique representative `{a, a+2}`), and the
last column contains both cells of the pair. -/
theorem pent_pair_col {L : ℕ} {t : Finset (Fin 5 × ℕ)} {c : Fin 5}
    (ht : t ∈ pentSets (L + 1)) (h1 : (c, L) ∈ t) (h2 : (c + 2, L) ∈ t) :
    ∃ u ∈ pentAvoid2 c L,
      t = insert (c, L) (insert (c + 2, L) u) ∧
        (c, L) ∈ t ∧ (c + 2, L) ∈ t := by
  refine ⟨(t.erase (c, L)).erase (c + 2, L),
    erase2_mem_pentAvoid2 ht h1 h2, ?_, h1, h2⟩
  have hne : (c + 2, L) ≠ (c, L) := fun e =>
    pent_add_two_ne_self c (Prod.ext_iff.mp e).1
  have step : insert (c + 2, L) ((t.erase (c, L)).erase (c + 2, L)) =
      t.erase (c, L) :=
    Finset.insert_erase (Finset.mem_erase.mpr ⟨hne, h2⟩)
  rw [step, Finset.insert_erase h1]

/-- **Column decomposition.**  `pentSets (L+1)` is the disjoint union of
the sets with empty last column (`pentSets L`), the sets ending in a
singleton `{(r, L)}` (five symmetric choices), and the sets ending in a
distance-2 pair `{a, a+2}` (five choices, indexed by `a ∈ Fin 5`). -/
theorem pentSets_succ (L : ℕ) :
    pentSets (L + 1) =
      pentSets L ∪ (Finset.univ : Finset (Fin 5)).biUnion
          (fun r => (pentAvoid r L).image fun t => insert (r, L) t) ∪
        ((Finset.univ : Finset (Fin 5)).biUnion fun a =>
          (pentAvoid2 a L).image
            fun t => insert (a, L) (insert (a + 2, L) t)) := by
  ext t
  simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_image,
    Finset.mem_univ, true_and]
  constructor
  · intro ht
    by_cases h : ∃ c : Fin 5, (c, L) ∈ t
    · obtain ⟨c, hc⟩ := h
      by_cases h2 : (c + 2, L) ∈ t
      · obtain ⟨u, hu, ht_eq, hm1, hm2⟩ := pent_pair_col ht hc h2
        exact Or.inr ⟨c, u, hu, ht_eq.symm⟩
      · by_cases h3 : (c + 3, L) ∈ t
        · obtain ⟨u, hu, ht_eq, hm1, hm2⟩ :=
            pent_pair_col ht h3 (by rwa [pent_add_three_add_two c])
          exact Or.inr ⟨c + 3, u, hu, ht_eq.symm⟩
        · exact Or.inl (Or.inr ⟨c, t.erase (c, L),
            erase_mem_pentAvoid ht hc h2 h3, Finset.insert_erase hc⟩)
    · exact Or.inl (Or.inl (mem_pentSets_of_succ ht fun c hc => h ⟨c, hc⟩))
  · rintro ((ht | ⟨c, u, hu, rfl⟩) | ⟨a, u, hu, rfl⟩)
    · exact pentSets_mono L ht
    · exact mem_pentSets_succ_of_mem_pentAvoid hu
    · exact mem_pentSets_succ_of_mem_pentAvoid2 hu

/-- The avoiding family at level `L+1`: sets with empty last column
(`pentSets L`), sets ending in `{(c, L)}` for `c ≠ r` (four choices),
and sets ending in a distance-2 pair disjoint from `r` (three
choices). -/
theorem pentAvoid_succ (L : ℕ) (r : Fin 5) :
    pentAvoid r (L + 1) =
      pentSets L ∪ (Finset.univ.filter fun c => c ≠ r).biUnion
          (fun c => (pentAvoid c L).image fun t => insert (c, L) t) ∪
        (((Finset.univ : Finset (Fin 5)).filter fun a =>
            r ≠ a ∧ r ≠ a + 2).biUnion
          fun a => (pentAvoid2 a L).image
            fun t => insert (a, L) (insert (a + 2, L) t)) := by
  ext t
  simp only [mem_pentAvoid, Nat.add_sub_cancel, Finset.mem_union,
    Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨ht, hr⟩
    by_cases h : ∃ c : Fin 5, (c, L) ∈ t
    · obtain ⟨c, hc⟩ := h
      by_cases h2 : (c + 2, L) ∈ t
      · obtain ⟨u, hu, ht_eq, hm1, hm2⟩ := pent_pair_col ht hc h2
        exact Or.inr ⟨c,
          ⟨fun e => hr (by rwa [← e] at hm1),
           fun e => hr (by rwa [← e] at hm2)⟩,
          u, hu, ht_eq.symm⟩
      · by_cases h3 : (c + 3, L) ∈ t
        · obtain ⟨u, hu, ht_eq, hm1, hm2⟩ :=
            pent_pair_col ht h3 (by rwa [pent_add_three_add_two c])
          exact Or.inr ⟨c + 3,
            ⟨fun e => hr (by rwa [← e] at hm1),
             fun e => hr (by rwa [← e] at hm2)⟩,
            u, hu, ht_eq.symm⟩
        · exact Or.inl (Or.inr ⟨c, fun e => hr (by rwa [e] at hc),
            t.erase (c, L), mem_pentAvoid.mp
              (erase_mem_pentAvoid ht hc h2 h3),
            Finset.insert_erase hc⟩)
    · exact Or.inl (Or.inl (mem_pentSets_of_succ ht fun c hc => h ⟨c, hc⟩))
  · rintro ((ht | ⟨c, hcr, u, hu, rfl⟩) |
      ⟨a, ⟨hra, hra2⟩, u, hu, rfl⟩)
    · refine ⟨pentSets_mono L ht, fun hC => ?_⟩
      have hv := (mem_pentSets.mp ht).1 hC
      rw [mem_pentVert] at hv
      exact absurd hv (lt_irrefl _)
    · refine ⟨mem_pentSets_succ_of_mem_pentAvoid (mem_pentAvoid.mpr hu),
        fun hC => ?_⟩
      rw [Finset.mem_insert] at hC
      rcases hC with hC | hC
      · exact hcr (Prod.ext_iff.mp hC).1.symm
      · have hv := (mem_pentSets.mp hu.1).1 hC
        rw [mem_pentVert] at hv
        exact absurd hv (lt_irrefl _)
    · refine ⟨mem_pentSets_succ_of_mem_pentAvoid2 hu, fun hC => ?_⟩
      rw [Finset.mem_insert, Finset.mem_insert] at hC
      rcases hC with hC | hC | hC
      · exact hra (Prod.ext_iff.mp hC).1
      · exact hra2 (Prod.ext_iff.mp hC).1
      · have hv := (mem_pentSets.mp (mem_pentAvoid2.mp hu).1).1 hC
        rw [mem_pentVert] at hv
        exact absurd hv (lt_irrefl _)

/-- The pair-avoiding family `pentAvoid2 0` at level `L+1`: sets with
empty last column, sets ending in `{(c, L)}` for `c ∈ {1,3,4}` (three
choices), and sets ending in one of the two distance-2 pairs disjoint
from `{0,2}` (namely `{1,3}` and `{1,4}`). -/
theorem pentAvoid2_zero_succ (L : ℕ) :
    pentAvoid2 0 (L + 1) =
      pentSets L ∪ ((Finset.univ : Finset (Fin 5)).filter
          fun c : Fin 5 => c ≠ 0 ∧ c ≠ 0 + 2).biUnion
          (fun c => (pentAvoid c L).image fun t => insert (c, L) t) ∪
        (((Finset.univ : Finset (Fin 5)).filter fun a : Fin 5 =>
            (0 : Fin 5) ≠ a ∧ 0 ≠ a + 2 ∧ (0 : Fin 5) + 2 ≠ a ∧
              (0 : Fin 5) + 2 ≠ a + 2).biUnion
          fun a => (pentAvoid2 a L).image
            fun t => insert (a, L) (insert (a + 2, L) t)) := by
  ext t
  simp only [mem_pentAvoid2, Nat.add_sub_cancel, Finset.mem_union,
    Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨ht, hb1, hb2⟩
    by_cases h : ∃ c : Fin 5, (c, L) ∈ t
    · obtain ⟨c, hc⟩ := h
      by_cases h2 : (c + 2, L) ∈ t
      · obtain ⟨u, hu, ht_eq, hm1, hm2⟩ := pent_pair_col ht hc h2
        exact Or.inr ⟨c,
          ⟨fun e => hb1 (by rwa [← e] at hm1),
           fun e => hb1 (by rwa [← e] at hm2),
           fun e => hb2 (by rwa [← e] at hm1),
           fun e => hb2 (by rwa [← e] at hm2)⟩,
          u, mem_pentAvoid2.mp hu, ht_eq.symm⟩
      · by_cases h3 : (c + 3, L) ∈ t
        · obtain ⟨u, hu, ht_eq, hm1, hm2⟩ :=
            pent_pair_col ht h3 (by rwa [pent_add_three_add_two c])
          exact Or.inr ⟨c + 3,
            ⟨fun e => hb1 (by rwa [← e] at hm1),
             fun e => hb1 (by rwa [← e] at hm2),
             fun e => hb2 (by rwa [← e] at hm1),
             fun e => hb2 (by rwa [← e] at hm2)⟩,
            u, mem_pentAvoid2.mp hu, ht_eq.symm⟩
        · exact Or.inl (Or.inr ⟨c,
            ⟨fun e => hb1 (by rwa [e] at hc),
             fun e => hb2 (by rwa [e] at hc)⟩,
            t.erase (c, L), erase_mem_pentAvoid ht hc h2 h3,
            Finset.insert_erase hc⟩)
    · exact Or.inl (Or.inl (mem_pentSets_of_succ ht fun c hc => h ⟨c, hc⟩))
  · rintro ((ht | ⟨c, ⟨hc1, hc2⟩, u, hu, rfl⟩) |
      ⟨a, ⟨ha1, ha2, ha3, ha4⟩, u, hu, rfl⟩)
    · refine ⟨pentSets_mono L ht, fun hC => ?_, fun hC => ?_⟩
      · have hv := (mem_pentSets.mp ht).1 hC
        rw [mem_pentVert] at hv
        exact absurd hv (lt_irrefl _)
      · have hv := (mem_pentSets.mp ht).1 hC
        rw [mem_pentVert] at hv
        exact absurd hv (lt_irrefl _)
    · refine ⟨mem_pentSets_succ_of_mem_pentAvoid hu, fun hC => ?_,
        fun hC => ?_⟩
      · rw [Finset.mem_insert] at hC
        rcases hC with hC | hC
        · exact hc1 (Prod.ext_iff.mp hC).1.symm
        · have hv := (mem_pentSets.mp (mem_pentAvoid.mp hu).1).1 hC
          rw [mem_pentVert] at hv
          exact absurd hv (lt_irrefl _)
      · rw [Finset.mem_insert] at hC
        rcases hC with hC | hC
        · exact hc2 (Prod.ext_iff.mp hC).1.symm
        · have hv := (mem_pentSets.mp (mem_pentAvoid.mp hu).1).1 hC
          rw [mem_pentVert] at hv
          exact absurd hv (lt_irrefl _)
    · refine ⟨mem_pentSets_succ_of_mem_pentAvoid2 (mem_pentAvoid2.mpr hu),
        fun hC => ?_, fun hC => ?_⟩
      · rw [Finset.mem_insert, Finset.mem_insert] at hC
        rcases hC with hC | hC | hC
        · exact ha1 (Prod.ext_iff.mp hC).1
        · exact ha2 (Prod.ext_iff.mp hC).1
        · have hv := (mem_pentSets.mp hu.1).1 hC
          rw [mem_pentVert] at hv
          exact absurd hv (lt_irrefl _)
      · rw [Finset.mem_insert, Finset.mem_insert] at hC
        rcases hC with hC | hC | hC
        · exact ha3 (Prod.ext_iff.mp hC).1
        · exact ha4 (Prod.ext_iff.mp hC).1
        · have hv := (mem_pentSets.mp hu.1).1 hC
          rw [mem_pentVert] at hv
          exact absurd hv (lt_irrefl _)

/-! ### Cardinality lemmas -/

/-- The `insert (r, L)` image of `pentAvoid r L` has the same
cardinality: `erase (r, L)` inverts it. -/
theorem pentCard_image_insert (r : Fin 5) (L : ℕ) :
    ((pentAvoid r L).image fun t => insert (r, L) t).card =
      (pentAvoid r L).card := by
  apply Finset.card_image_of_injOn
  intro t₁ ht₁ t₂ ht₂ h
  rw [Finset.mem_coe, mem_pentAvoid, mem_pentSets] at ht₁ ht₂
  have h1 : (r, L) ∉ t₁ := by
    intro hC
    have hv := ht₁.1.1 hC
    rw [mem_pentVert] at hv
    exact absurd hv (lt_irrefl _)
  have h2 : (r, L) ∉ t₂ := by
    intro hC
    have hv := ht₂.1.1 hC
    rw [mem_pentVert] at hv
    exact absurd hv (lt_irrefl _)
  have e := congrArg (Finset.erase · (r, L)) h
  rwa [Finset.erase_insert h1, Finset.erase_insert h2] at e

/-- The double-`insert` image of `pentAvoid2 a L` has the same
cardinality: the double `erase` inverts it. -/
theorem pentCard_image_insert2 (a : Fin 5) (L : ℕ) :
    ((pentAvoid2 a L).image fun t => insert (a, L)
        (insert (a + 2, L) t)).card =
      (pentAvoid2 a L).card := by
  apply Finset.card_image_of_injOn
  intro t₁ ht₁ t₂ ht₂ h
  rw [Finset.mem_coe, mem_pentAvoid2, mem_pentSets] at ht₁ ht₂
  have h1 : (a, L) ∉ t₁ := by
    intro hC
    have hv := ht₁.1.1 hC
    rw [mem_pentVert] at hv
    exact absurd hv (lt_irrefl _)
  have h1' : (a, L) ∉ t₂ := by
    intro hC
    have hv := ht₂.1.1 hC
    rw [mem_pentVert] at hv
    exact absurd hv (lt_irrefl _)
  have h2 : (a + 2, L) ∉ t₁ := by
    intro hC
    have hv := ht₁.1.1 hC
    rw [mem_pentVert] at hv
    exact absurd hv (lt_irrefl _)
  have h2' : (a + 2, L) ∉ t₂ := by
    intro hC
    have hv := ht₂.1.1 hC
    rw [mem_pentVert] at hv
    exact absurd hv (lt_irrefl _)
  have hn1 : (a, L) ∉ insert (a + 2, L) t₁ := fun hm =>
    (Finset.mem_insert.mp hm).elim
      (fun e => absurd (Prod.ext_iff.mp e).1.symm (pent_add_two_ne_self a)) h1
  have hn2 : (a, L) ∉ insert (a + 2, L) t₂ := fun hm =>
    (Finset.mem_insert.mp hm).elim
      (fun e => absurd (Prod.ext_iff.mp e).1.symm (pent_add_two_ne_self a)) h1'
  have e := congrArg (fun s => (s.erase (a, L)).erase (a + 2, L)) h
  rwa [Finset.erase_insert hn1, Finset.erase_insert h2,
    Finset.erase_insert hn2, Finset.erase_insert h2'] at e

/-- `pentSets L` is disjoint from any singleton-image biUnion: the
images contain a column-`L` cell, members of `pentSets L` do not. -/
theorem pent_disjoint_sets_single (L : ℕ) (s : Finset (Fin 5)) :
    Disjoint (pentSets L)
      (s.biUnion fun c => (pentAvoid c L).image
        fun t => insert (c, L) t) := by
  rw [Finset.disjoint_left]
  intro t ht hB
  rw [Finset.mem_biUnion] at hB
  obtain ⟨c, -, hr⟩ := hB
  obtain ⟨u, -, rfl⟩ := Finset.mem_image.mp hr
  have hv := (mem_pentSets.mp ht).1 (Finset.mem_insert_self (c, L) u)
  rw [mem_pentVert] at hv
  exact absurd hv (lt_irrefl _)

/-- `pentSets L` is disjoint from any pair-image biUnion. -/
theorem pent_disjoint_sets_pair (L : ℕ) (s : Finset (Fin 5)) :
    Disjoint (pentSets L)
      (s.biUnion fun a => (pentAvoid2 a L).image
        fun t => insert (a, L) (insert (a + 2, L) t)) := by
  rw [Finset.disjoint_left]
  intro t ht hB
  rw [Finset.mem_biUnion] at hB
  obtain ⟨a, -, hr⟩ := hB
  obtain ⟨u, -, rfl⟩ := Finset.mem_image.mp hr
  have hv := (mem_pentSets.mp ht).1 (Finset.mem_insert_self (a, L) _)
  rw [mem_pentVert] at hv
  exact absurd hv (lt_irrefl _)

/-- Singleton-image families over distinct rails are disjoint. -/
theorem pent_single_pw (L : ℕ) (s : Finset (Fin 5)) :
    ((s : Set (Fin 5)).PairwiseDisjoint
      fun c => (pentAvoid c L).image fun t => insert (c, L) t) := by
  rintro c - c' - hcc
  show Disjoint ((pentAvoid c L).image fun t => insert (c, L) t)
    ((pentAvoid c' L).image fun t => insert (c', L) t)
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
  · have hv' := (mem_pentSets.mp (mem_pentAvoid.mp hv).1).1 hmem
    rw [mem_pentVert] at hv'
    exact absurd hv' (lt_irrefl _)

/-- Pair-image families over distinct representatives are disjoint
(the five distance-2 pairs `{a, a+2}` are all different). -/
theorem pent_pair_pw (L : ℕ) (s : Finset (Fin 5)) :
    ((s : Set (Fin 5)).PairwiseDisjoint
      fun a => (pentAvoid2 a L).image
        fun t => insert (a, L) (insert (a + 2, L) t)) := by
  rintro a - a' - haa
  show Disjoint ((pentAvoid2 a L).image
      fun t => insert (a, L) (insert (a + 2, L) t))
    ((pentAvoid2 a' L).image
      fun t => insert (a', L) (insert (a' + 2, L) t))
  rw [Finset.disjoint_left]
  intro t ht hB
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ht
  obtain ⟨v, hv, heq⟩ := Finset.mem_image.mp hB
  have hmem : (a, L) ∈ insert (a', L) (insert (a' + 2, L) v) := by
    rw [heq]
    exact Finset.mem_insert_self _ _
  rw [Finset.mem_insert, Finset.mem_insert] at hmem
  rcases hmem with hmem | hmem | hmem
  · exact absurd (Prod.ext_iff.mp hmem).1 haa
  · have e : a = a' + 2 := (Prod.ext_iff.mp hmem).1
    have hmem2 : (a + 2, L) ∈ insert (a', L) (insert (a' + 2, L) v) := by
      rw [heq]
      exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert_self _ _))
    rw [Finset.mem_insert, Finset.mem_insert] at hmem2
    rcases hmem2 with hmem2 | hmem2 | hmem2
    · -- a + 2 = a' and a = a' + 2 give a' + 4 = a' on Fin 5
      have e2 : a + 2 = a' := (Prod.ext_iff.mp hmem2).1
      exfalso
      rw [e] at e2
      have hv := congrArg Fin.val e2
      rw [pent_val_add_two, pent_val_add_two] at hv
      have h1 := a'.isLt
      omega
    · -- a + 2 = a' + 2 gives a = a'
      have e2 : a + 2 = a' + 2 := (Prod.ext_iff.mp hmem2).1
      exfalso
      have hv := congrArg Fin.val e2
      rw [pent_val_add_two, pent_val_add_two] at hv
      have h1 := a.isLt; have h2 := a'.isLt
      have : a = a' := by
        apply Fin.ext
        omega
      exact haa this
    · have hv' := (mem_pentSets.mp (mem_pentAvoid2.mp hv).1).1 hmem2
      rw [mem_pentVert] at hv'
      exact absurd hv' (lt_irrefl _)
  · have hv' := (mem_pentSets.mp (mem_pentAvoid2.mp hv).1).1 hmem
    rw [mem_pentVert] at hv'
    exact absurd hv' (lt_irrefl _)

/-- A singleton image and a pair image are disjoint: the former has
exactly one cell in column `L`, the latter has two. -/
theorem pent_disjoint_single_pair (L : ℕ) (s₁ s₂ : Finset (Fin 5)) :
    Disjoint (s₁.biUnion fun c => (pentAvoid c L).image
        fun t => insert (c, L) t)
      (s₂.biUnion fun a => (pentAvoid2 a L).image
        fun t => insert (a, L) (insert (a + 2, L) t)) := by
  rw [Finset.disjoint_left]
  intro t ht hB
  rw [Finset.mem_biUnion] at ht hB
  obtain ⟨c, -, hc⟩ := ht
  obtain ⟨a, -, hr⟩ := hB
  obtain ⟨u, hu, heq⟩ := Finset.mem_image.mp hr
  obtain ⟨v, hv, heq2⟩ := Finset.mem_image.mp hc
  have hm1 : (a, L) ∈ insert (c, L) v := by
    have h : (a, L) ∈ insert (a, L) (insert (a + 2, L) u) :=
      Finset.mem_insert_self _ _
    rw [heq, ← heq2] at h
    exact h
  rcases Finset.mem_insert.mp hm1 with hm1 | hm1
  · have e1 : a = c := (Prod.ext_iff.mp hm1).1
    have hm2 : (a + 2, L) ∈ insert (c, L) v := by
      have h : (a + 2, L) ∈ insert (a, L) (insert (a + 2, L) u) :=
        Finset.mem_insert.mpr (Or.inr (Finset.mem_insert_self _ _))
      rw [heq, ← heq2] at h
      exact h
    rcases Finset.mem_insert.mp hm2 with hm2 | hm2
    · have e2 : a + 2 = c := (Prod.ext_iff.mp hm2).1
      exact absurd (e2.trans e1.symm) (pent_add_two_ne_self a)
    · have hv' := (mem_pentSets.mp (mem_pentAvoid.mp hv).1).1 hm2
      rw [mem_pentVert] at hv'
      exact absurd hv' (lt_irrefl _)
  · have hv' := (mem_pentSets.mp (mem_pentAvoid.mp hv).1).1 hm1
    rw [mem_pentVert] at hv'
    exact absurd hv' (lt_irrefl _)

/-- Union of the disjointness facts: `pentSets L ∪ singles` is disjoint
from the pair biUnion. -/
theorem pent_disjoint_union_pair (L : ℕ) (s₁ s₂ : Finset (Fin 5)) :
    Disjoint (pentSets L ∪ s₁.biUnion fun c => (pentAvoid c L).image
        fun t => insert (c, L) t)
      (s₂.biUnion fun a => (pentAvoid2 a L).image
        fun t => insert (a, L) (insert (a + 2, L) t)) := by
  rw [Finset.disjoint_left]
  intro t ht hB
  rcases Finset.mem_union.mp ht with ht | ht
  · exact Finset.disjoint_left.mp (pent_disjoint_sets_pair L s₂) ht hB
  · exact Finset.disjoint_left.mp (pent_disjoint_single_pair L s₁ s₂) ht hB

/-- `T(L+1) = T(L) + 5·A(L) + 5·B(L)`: one choice for the empty last
column, five symmetric singleton choices, and five distance-2-pair
choices. -/
theorem pentSets_card_succ (L : ℕ) :
    (pentSets (L + 1)).card =
      (pentSets L).card + 5 * (pentAvoid 0 L).card +
        5 * (pentAvoid2 0 L).card := by
  have d_top := pent_disjoint_union_pair L Finset.univ Finset.univ
  have d_AS := pent_disjoint_sets_single L Finset.univ
  have pw_S := pent_single_pw L Finset.univ
  have pw_P := pent_pair_pw L Finset.univ
  rw [pentSets_succ, Finset.card_union_of_disjoint d_top,
    Finset.card_union_of_disjoint d_AS, Finset.card_biUnion pw_S,
    Finset.card_biUnion pw_P]
  have hsum : (∑ r ∈ Finset.univ,
        ((pentAvoid r L).image fun t => insert (r, L) t).card)
      = ∑ _r ∈ (Finset.univ : Finset (Fin 5)), (pentAvoid 0 L).card := by
    apply Finset.sum_congr rfl
    intro r _
    rw [pentCard_image_insert]
    exact pentAvoid_card_eq r 0 L
  rw [hsum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    Nat.nsmul_eq_mul]
  have hsum2 : (∑ a ∈ (Finset.univ : Finset (Fin 5)),
        ((pentAvoid2 a L).image fun t => insert (a, L)
          (insert (a + 2, L) t)).card)
      = ∑ _a ∈ (Finset.univ : Finset (Fin 5)), (pentAvoid2 0 L).card := by
    apply Finset.sum_congr rfl
    intro a _
    rw [pentCard_image_insert2]
    exact pentAvoid2_card_eq a 0 L
  rw [hsum2, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    Nat.nsmul_eq_mul]

/-- `A(L+1) = T(L) + 4·A(L) + 3·B(L)`: an `r`-avoiding set of length
`L+1` has empty last column, ends in one of the four other rails, or
ends in one of the three distance-2 pairs disjoint from `r`. -/
theorem pentAvoid_succ_card (L : ℕ) (r : Fin 5) :
    (pentAvoid r (L + 1)).card =
      (pentSets L).card + 4 * (pentAvoid r L).card +
        3 * (pentAvoid2 0 L).card := by
  have d_top := pent_disjoint_union_pair L
    (Finset.univ.filter fun c => c ≠ r)
    ((Finset.univ : Finset (Fin 5)).filter fun a : Fin 5 =>
      r ≠ a ∧ r ≠ a + 2)
  have d_AS := pent_disjoint_sets_single L
    (Finset.univ.filter fun c => c ≠ r)
  have pw_S := pent_single_pw L (Finset.univ.filter fun c => c ≠ r)
  have pw_P := pent_pair_pw L
    ((Finset.univ : Finset (Fin 5)).filter fun a : Fin 5 =>
      r ≠ a ∧ r ≠ a + 2)
  rw [pentAvoid_succ, Finset.card_union_of_disjoint d_top,
    Finset.card_union_of_disjoint d_AS, Finset.card_biUnion pw_S,
    Finset.card_biUnion pw_P]
  have hcard : ((Finset.univ : Finset (Fin 5)).filter
      fun c => c ≠ r).card = 4 := by
    rw [Finset.filter_ne' _ r,
      Finset.card_erase_of_mem (Finset.mem_univ r), Finset.card_univ,
      Fintype.card_fin]
  have hsum : (∑ c ∈ Finset.univ.filter fun c => c ≠ r,
        ((pentAvoid c L).image fun t => insert (c, L) t).card)
      = ∑ _c ∈ Finset.univ.filter (fun c => c ≠ r),
        (pentAvoid r L).card := by
    apply Finset.sum_congr rfl
    intro c _
    rw [pentCard_image_insert]
    exact pentAvoid_card_eq c r L
  rw [hsum, Finset.sum_const, hcard, Nat.nsmul_eq_mul]
  have hcard2 : ((Finset.univ : Finset (Fin 5)).filter
      fun a : Fin 5 => r ≠ a ∧ r ≠ a + 2).card = 3 := by
    fin_cases r <;> decide
  have hsum2 : (∑ a ∈ (Finset.univ : Finset (Fin 5)).filter
        fun a : Fin 5 => r ≠ a ∧ r ≠ a + 2,
        ((pentAvoid2 a L).image fun t => insert (a, L)
          (insert (a + 2, L) t)).card)
      = ∑ _a ∈ (Finset.univ : Finset (Fin 5)).filter
          (fun a : Fin 5 => r ≠ a ∧ r ≠ a + 2), (pentAvoid2 0 L).card := by
    apply Finset.sum_congr rfl
    intro a _
    rw [pentCard_image_insert2]
    exact pentAvoid2_card_eq a 0 L
  rw [hsum2, Finset.sum_const, hcard2, Nat.nsmul_eq_mul]

/-- `B(L+1) = T(L) + 3·A(L) + 2·B(L)`: a `{0,2}`-avoiding set of length
`L+1` has empty last column, ends in rail `1`, `3`, or `4`, or ends in
one of the two pairs `{1,3}`, `{1,4}` disjoint from `{0,2}`. -/
theorem pentAvoid2_succ_card (L : ℕ) :
    (pentAvoid2 0 (L + 1)).card =
      (pentSets L).card + 3 * (pentAvoid 0 L).card +
        2 * (pentAvoid2 0 L).card := by
  have d_top := pent_disjoint_union_pair L
    ((Finset.univ : Finset (Fin 5)).filter
      fun c : Fin 5 => c ≠ 0 ∧ c ≠ 0 + 2)
    ((Finset.univ : Finset (Fin 5)).filter fun a : Fin 5 =>
      (0 : Fin 5) ≠ a ∧ (0 : Fin 5) ≠ a + 2 ∧ (0 : Fin 5) + 2 ≠ a ∧
        (0 : Fin 5) + 2 ≠ a + 2)
  have d_AS := pent_disjoint_sets_single L
    ((Finset.univ : Finset (Fin 5)).filter
      fun c : Fin 5 => c ≠ 0 ∧ c ≠ 0 + 2)
  have pw_S := pent_single_pw L
    ((Finset.univ : Finset (Fin 5)).filter
      fun c : Fin 5 => c ≠ 0 ∧ c ≠ 0 + 2)
  have pw_P := pent_pair_pw L
    ((Finset.univ : Finset (Fin 5)).filter fun a : Fin 5 =>
      (0 : Fin 5) ≠ a ∧ (0 : Fin 5) ≠ a + 2 ∧ (0 : Fin 5) + 2 ≠ a ∧
        (0 : Fin 5) + 2 ≠ a + 2)
  rw [pentAvoid2_zero_succ, Finset.card_union_of_disjoint d_top,
    Finset.card_union_of_disjoint d_AS, Finset.card_biUnion pw_S,
    Finset.card_biUnion pw_P]
  have hcard : ((Finset.univ : Finset (Fin 5)).filter
      fun c : Fin 5 => c ≠ 0 ∧ c ≠ 0 + 2).card = 3 := by
    decide
  have hsum : (∑ c ∈ (Finset.univ : Finset (Fin 5)).filter
        fun c : Fin 5 => c ≠ 0 ∧ c ≠ 0 + 2,
        ((pentAvoid c L).image fun t => insert (c, L) t).card)
      = ∑ _c ∈ (Finset.univ : Finset (Fin 5)).filter
        (fun c : Fin 5 => c ≠ 0 ∧ c ≠ 0 + 2),
        (pentAvoid 0 L).card := by
    apply Finset.sum_congr rfl
    intro c _
    rw [pentCard_image_insert]
    exact pentAvoid_card_eq c 0 L
  rw [hsum, Finset.sum_const, hcard, Nat.nsmul_eq_mul]
  have hcard2 : ((Finset.univ : Finset (Fin 5)).filter fun a : Fin 5 =>
      (0 : Fin 5) ≠ a ∧ (0 : Fin 5) ≠ a + 2 ∧ (0 : Fin 5) + 2 ≠ a ∧
        (0 : Fin 5) + 2 ≠ a + 2).card = 2 := by
    decide
  have hsum2 : (∑ a ∈ (Finset.univ : Finset (Fin 5)).filter fun a : Fin 5 =>
        (0 : Fin 5) ≠ a ∧ (0 : Fin 5) ≠ a + 2 ∧ (0 : Fin 5) + 2 ≠ a ∧
          (0 : Fin 5) + 2 ≠ a + 2,
        ((pentAvoid2 a L).image fun t => insert (a, L)
          (insert (a + 2, L) t)).card)
      = ∑ _a ∈ (Finset.univ : Finset (Fin 5)).filter (fun a : Fin 5 =>
          (0 : Fin 5) ≠ a ∧ (0 : Fin 5) ≠ a + 2 ∧ (0 : Fin 5) + 2 ≠ a ∧
            (0 : Fin 5) + 2 ≠ a + 2), (pentAvoid2 0 L).card := by
    apply Finset.sum_congr rfl
    intro a _
    rw [pentCard_image_insert2]
    exact pentAvoid2_card_eq a 0 L
  rw [hsum2, Finset.sum_const, hcard2, Nat.nsmul_eq_mul]

theorem pentSets_zero : pentSets 0 = {∅} := by
  ext t
  rw [mem_pentSets, pentVert_zero, Finset.subset_empty,
    Finset.mem_singleton]
  refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
  subst h
  exact ⟨fun p hp => absurd hp (Finset.notMem_empty _),
    fun p hp => absurd hp (Finset.notMem_empty _)⟩

theorem pentAvoid_zero (r : Fin 5) : pentAvoid r 0 = {∅} := by
  ext t
  rw [mem_pentAvoid, pentSets_zero, Finset.mem_singleton]
  refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
  subst h
  exact Finset.notMem_empty _

theorem pentAvoid2_zero (a : Fin 5) : pentAvoid2 a 0 = {∅} := by
  ext t
  rw [mem_pentAvoid2, pentSets_zero, Finset.mem_singleton]
  refine ⟨fun h => h.1, fun h => ⟨h, ?_, ?_⟩⟩ <;>
    subst h <;> exact Finset.notMem_empty _

/-- Base count: `T(0) = 1`. -/
theorem pentSets_card_zero : (pentSets 0).card = 1 := by
  rw [pentSets_zero, Finset.card_singleton]

/-- Base count: `T(1) = 11` (the empty set, five singletons, and the
five distance-2 pairs). -/
theorem pentSets_card_one : (pentSets 1).card = 11 := by
  have h : (pentSets (0 + 1)).card =
      (pentSets 0).card + 5 * (pentAvoid 0 0).card +
        5 * (pentAvoid2 0 0).card := pentSets_card_succ 0
  rw [pentSets_card_zero, pentAvoid_zero, pentAvoid2_zero,
    Finset.card_singleton] at h
  exact h

/-- Base count: `T(2) = 81`. -/
theorem pentSets_card_two : (pentSets 2).card = 81 := by
  have h2 : (pentSets (1 + 1)).card =
      (pentSets 1).card + 5 * (pentAvoid 0 1).card +
        5 * (pentAvoid2 0 1).card := pentSets_card_succ 1
  have hA : (pentAvoid 0 (0 + 1)).card =
      (pentSets 0).card + 4 * (pentAvoid 0 0).card +
        3 * (pentAvoid2 0 0).card := pentAvoid_succ_card 0 (0 : Fin 5)
  have hB : (pentAvoid2 0 (0 + 1)).card =
      (pentSets 0).card + 3 * (pentAvoid 0 0).card +
        2 * (pentAvoid2 0 0).card := pentAvoid2_succ_card 0
  rw [show (0 : ℕ) + 1 = 1 from rfl] at hA hB
  rw [show (1 : ℕ) + 1 = 2 from rfl] at h2
  simp only [pentSets_card_one, pentSets_card_zero, pentAvoid_zero,
    pentAvoid2_zero, Finset.card_singleton] at h2 hA hB
  omega

/-- **The two-step bound** `T(L+2) ≤ 6·T(L+1) + 15·T(L)`, obtained by
eliminating the avoiding counts (`T(L+2) = 6·T(L+1) + 5·T(L) + 10·A(L)`
and `A(L) ≤ T(L)`). -/
theorem pentSets_card_add_two_le (L : ℕ) :
    (pentSets (L + 2)).card ≤
      6 * (pentSets (L + 1)).card + 15 * (pentSets L).card := by
  have hT1 := pentSets_card_succ L
  have hT2 := pentSets_card_succ (L + 1)
  have hA := pentAvoid_succ_card L (0 : Fin 5)
  have hB := pentAvoid2_succ_card L
  have hsub : (pentAvoid 0 L).card ≤ (pentSets L).card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  rw [show L + 1 + 1 = L + 2 from rfl] at hT2
  omega

/-- **The exact recurrence** `T(L+3) + T(L) = 7·T(L+2) + 5·T(L+1)`, the
order-3 recurrence of the `11`-state transfer matrix (characteristic
polynomial `λ³ = 7λ² + 5λ - 1`, Perron root `≈ 7.617`). -/
theorem pentSets_card_add_three (L : ℕ) :
    (pentSets (L + 3)).card + (pentSets L).card =
      7 * (pentSets (L + 2)).card + 5 * (pentSets (L + 1)).card := by
  have hT1 := pentSets_card_succ L
  have hT2 := pentSets_card_succ (L + 1)
  have hT3 := pentSets_card_succ (L + 2)
  have hA1 := pentAvoid_succ_card L (0 : Fin 5)
  have hA2 := pentAvoid_succ_card (L + 1) (0 : Fin 5)
  have hA3 := pentAvoid_succ_card (L + 2) (0 : Fin 5)
  have hB1 := pentAvoid2_succ_card L
  have hB2 := pentAvoid2_succ_card (L + 1)
  have hB3 := pentAvoid2_succ_card (L + 2)
  rw [show L + 1 + 1 = L + 2 from rfl] at hT2 hA2 hB2
  rw [show L + 2 + 1 = L + 3 from rfl] at hT3 hA3 hB3
  omega

/-- **Integer-normalised bound** (sharp form).  `T(L)·4^L ≤ 2·31^L` for
all `L`, i.e. `T(L) ≤ 2·(31/4)^L`: the three-step induction gives
`T(k+3)·4^{k+3} ≤ 28·(T(k+2)·4^{k+2}) + 80·(T(k+1)·4^{k+1}) ≤
56·31^{k+2} + 160·31^{k+1} = 1896·31^{k+1} ≤ 1922·31^{k+1} = 2·31^{k+3}`.
Per vertex this is the rate `(31/4)^{1/5} ≈ 1.505`, strictly below the
ladder rate `√(1 + √2) ≈ 1.5538`. -/
theorem pentSets_card_mul_four_pow_le (L : ℕ) :
    (pentSets L).card * 4 ^ L ≤ 2 * 31 ^ L := by
  have key : ∀ n, (pentSets n).card * 4 ^ n ≤ 2 * 31 ^ n ∧
      (pentSets (n + 1)).card * 4 ^ (n + 1) ≤ 2 * 31 ^ (n + 1) ∧
      (pentSets (n + 2)).card * 4 ^ (n + 2) ≤ 2 * 31 ^ (n + 2) := by
    intro n
    induction n with
    | zero =>
      refine ⟨?_, ?_, ?_⟩
      · rw [pentSets_card_zero]; norm_num
      · rw [pentSets_card_one]; norm_num
      · rw [pentSets_card_two]; norm_num
    | succ n ih =>
      obtain ⟨h0, h1, h2⟩ := ih
      refine ⟨h1, h2, ?_⟩
      have hrec := pentSets_card_add_three n
      have hle : (pentSets (n + 3)).card ≤
          7 * (pentSets (n + 2)).card + 5 * (pentSets (n + 1)).card := by
        omega
      calc (pentSets (n + 1 + 2)).card * 4 ^ (n + 1 + 2)
          = (pentSets (n + 3)).card * 4 ^ (n + 3) := rfl
        _ ≤ (7 * (pentSets (n + 2)).card + 5 * (pentSets (n + 1)).card) *
              4 ^ (n + 3) := Nat.mul_le_mul hle (le_refl _)
        _ = 28 * ((pentSets (n + 2)).card * 4 ^ (n + 2)) +
              80 * ((pentSets (n + 1)).card * 4 ^ (n + 1)) := by
            rw [Nat.add_mul]
            have e1 : (4 : ℕ) ^ (n + 3) = 64 * 4 ^ n := by
              rw [pow_add]; ring
            have e2 : (4 : ℕ) ^ (n + 2) = 16 * 4 ^ n := by
              rw [pow_add]; ring
            have e3 : (4 : ℕ) ^ (n + 1) = 4 * 4 ^ n := pow_succ' _ _
            rw [e1, e2, e3]
            ring
        _ ≤ 28 * (2 * 31 ^ (n + 2)) + 80 * (2 * 31 ^ (n + 1)) :=
            add_le_add (Nat.mul_le_mul (le_refl 28) h2)
              (Nat.mul_le_mul (le_refl 80) h1)
        _ = 1896 * 31 ^ (n + 1) := by
            rw [show (31 : ℕ) ^ (n + 2) = 31 * 31 ^ (n + 1) from
              pow_succ' _ _]
            ring
        _ ≤ 2 * 31 ^ (n + 1 + 2) := by
            have e : (31 : ℕ) ^ (n + 3) = 961 * 31 ^ (n + 1) := by
              rw [pow_add]; ring
            show 1896 * 31 ^ (n + 1) ≤ 2 * 31 ^ (n + 3)
            rw [e]
            calc 1896 * 31 ^ (n + 1) ≤ 1922 * 31 ^ (n + 1) :=
                  Nat.mul_le_mul (by norm_num) (le_refl _)
              _ = 2 * (961 * 31 ^ (n + 1)) := by ring
  exact (key L).1

/-- Loose corollary: `T(L) ≤ 2·8^L` — itself already a per-vertex rate
of `8^{1/5} ≈ 1.516`, below the ladder rate. -/
theorem pentSets_card_le (L : ℕ) : (pentSets L).card ≤ 2 * 8 ^ L := by
  induction L using Nat.twoStepInduction with
  | zero =>
      rw [pentSets_card_zero]
      norm_num
  | one =>
      rw [pentSets_card_one]
      norm_num
  | more k ih ih1 =>
      have hrec := pentSets_card_add_two_le k
      calc (pentSets (k + 2)).card
          ≤ 6 * (pentSets (k + 1)).card + 15 * (pentSets k).card := hrec
        _ ≤ 6 * (2 * 8 ^ (k + 1)) + 15 * (2 * 8 ^ k) :=
            add_le_add (Nat.mul_le_mul (le_refl 6) ih1)
              (Nat.mul_le_mul (le_refl 15) ih)
        _ = 126 * 8 ^ k := by
            rw [show (8 : ℕ) ^ (k + 1) = 8 * 8 ^ k from pow_succ' _ _]
            ring
        _ ≤ 2 * 8 ^ (k + 2) := by
            have e : (8 : ℕ) ^ (k + 2) = 64 * 8 ^ k := by
              rw [pow_add]; ring
            rw [e]
            calc 126 * 8 ^ k ≤ 128 * 8 ^ k :=
                  Nat.mul_le_mul (by norm_num) (le_refl _)
              _ = 2 * (64 * 8 ^ k) := by ring

end JSP000728
