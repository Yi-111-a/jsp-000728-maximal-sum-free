import JSPProblem.TriCyl
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Tactic.FinCases

/-!
# JSP-000728 — independent sets of the `4 × L` cyclic strip

The *4-rail cyclic strip* of length `L` has vertex set `Fin 4 × range L`
(four rails of `L` cells) with edges between consecutive cells on the
same rail and between *adjacent* cells in the same column — each column
carries a copy of the cycle `C4`, not a clique.  An independent set
therefore carries at most two vertices per column, and two co-columnar
cells must be *antipodal*: the legal column states are

  `∅`, `{0}`, `{1}`, `{2}`, `{3}`, `{0,2}`, `{1,3}`

(seven states), and a state may follow `X` iff it is disjoint from `X`
(the vertical edges).  The counts `T(L) = (quadSets L).card` satisfy

  `T(0) = 1`, `T(1) = 7`, `T(2) = 35`,
  `T(L+3) = 5·T(L+2) + T(L+1) - T(L)`

(`1, 7, 35, 181, 933, …`, growth rate `≈ 5.156` per column, the Perron
root of `λ³ = 5λ² + λ - 1`, i.e. `≈ 1.507` per vertex — below the ladder
rate `√(1 + √2) ≈ 1.5538`).

* `quadVert L` : the vertex finset `Finset.univ ×ˢ Finset.range L`.
* `quadFree t` : the independent-set predicate; decidable.
* `quadSets L` : all independent sets, as a `powerset.filter`.
* `quadAvoid r L` : independent sets avoiding `(r, L-1)` — those that
  can be extended by the singleton `{(r, L)}`.
* `quadAvoid2 a L` : independent sets avoiding both `(a, L-1)` and
  `(a + 2, L-1)` — those extendable by the antipodal pair
  `{(a, L), (a+2, L)}`.
* `quadRotF k` / `quadRotN k` : rotation of the four rails by `k`
  positions (`i ↦ i + k` modulo `4`, realised through `Fin.val`
  arithmetic), a bijection preserving `quadFree`; it identifies the
  avoiding families of any two rails (`quadAvoid_card_eq`) and of any
  two antipodal pairs (`quadAvoid2_card_eq`).
* Splitting `quadSets (L+1)` by the last column gives
  `T(L+1) = T(L) + 4·A(L) + 2·B(L)`; the avoiding families satisfy
  `A(L+1) = T(L) + 3·A(L) + B(L)` and `B(L+1) = T(L) + 2·A(L) + B(L)`
  (`quadSets_card_succ`, `quadAvoid_succ_card`, `quadAvoid2_succ_card`).
  Eliminating yields the exact third-order recurrence
  `quadSets_card_add_three` and the two-step bound
  `T(L+2) ≤ 5·T(L+1) + 2·T(L)` (`quadSets_card_add_two_le`).
* `quadSets_card_mul_two_pow_le` : the integer-normalised bound
  `T(L)·2^L ≤ 2·11^L` (i.e. `T(L) ≤ 2·(11/2)^L`), per-vertex rate
  `(11/2)^{1/4} ≈ 1.5317` — strictly below the ladder rate.
-/

namespace JSP000728

/-- The vertex set of the 4-rail strip: `Fin 4 × range L`. -/
def quadVert (L : ℕ) : Finset (Fin 4 × ℕ) :=
  Finset.univ.product (Finset.range L)

theorem mem_quadVert {r : Fin 4} {j L : ℕ} :
    (r, j) ∈ quadVert L ↔ j < L := by
  simp [quadVert]

theorem quadVert_zero : quadVert 0 = ∅ := by
  ext ⟨c, j⟩
  simp [mem_quadVert]

theorem quadVert_mono (L : ℕ) : quadVert L ⊆ quadVert (L + 1) := by
  rintro ⟨c, j⟩ hp
  rw [mem_quadVert] at hp ⊢
  omega

/-- `t` is an *independent set* of the `4 × L` strip: no cell carries
its rail-successor `(r, j+1)`, and two cells of the same column must be
equal or antipodal (`r` and `r + 2`). -/
def quadFree (t : Finset (Fin 4 × ℕ)) : Prop :=
  (∀ p ∈ t, (p.1, p.2 + 1) ∉ t) ∧
    ∀ p ∈ t, ∀ q ∈ t, p.2 = q.2 →
      p.1 = q.1 ∨ p.1 + 2 = q.1 ∨ q.1 + 2 = p.1

instance decidableQuadFree (t : Finset (Fin 4 × ℕ)) :
    Decidable (quadFree t) := by
  unfold quadFree; infer_instance

theorem quadFree.mono {t u : Finset (Fin 4 × ℕ)} (ht : quadFree t)
    (hu : u ⊆ t) : quadFree u :=
  ⟨fun p hp hC => ht.1 p (hu hp) (hu hC),
   fun p hp q hq hpq => ht.2 p (hu hp) q (hu hq) hpq⟩

/-- The family of independent sets of the `4 × L` strip. -/
def quadSets (L : ℕ) : Finset (Finset (Fin 4 × ℕ)) :=
  (quadVert L).powerset.filter quadFree

theorem mem_quadSets {L : ℕ} {t : Finset (Fin 4 × ℕ)} :
    t ∈ quadSets L ↔ t ⊆ quadVert L ∧ quadFree t := by
  simp [quadSets]

theorem quadSets_mono (L : ℕ) : quadSets L ⊆ quadSets (L + 1) := by
  intro t ht
  rw [mem_quadSets] at ht ⊢
  exact ⟨ht.1.trans (quadVert_mono L), ht.2⟩

/-- The independent sets avoiding `(r, L-1)`: exactly those that can be
extended by placing `(r, L)` in column `L`. -/
def quadAvoid (r : Fin 4) (L : ℕ) : Finset (Finset (Fin 4 × ℕ)) :=
  (quadSets L).filter fun t => (r, L - 1) ∉ t

theorem mem_quadAvoid {r : Fin 4} {L : ℕ} {t : Finset (Fin 4 × ℕ)} :
    t ∈ quadAvoid r L ↔ t ∈ quadSets L ∧ (r, L - 1) ∉ t :=
  Finset.mem_filter

/-- The independent sets avoiding both `(a, L-1)` and `(a+2, L-1)`:
exactly those that can be extended by the antipodal pair
`{(a, L), (a+2, L)}`. -/
def quadAvoid2 (a : Fin 4) (L : ℕ) : Finset (Finset (Fin 4 × ℕ)) :=
  (quadSets L).filter fun t => (a, L - 1) ∉ t ∧ (a + 2, L - 1) ∉ t

theorem mem_quadAvoid2 {a : Fin 4} {L : ℕ} {t : Finset (Fin 4 × ℕ)} :
    t ∈ quadAvoid2 a L ↔
      t ∈ quadSets L ∧ (a, L - 1) ∉ t ∧ (a + 2, L - 1) ∉ t :=
  Finset.mem_filter

/-! ### `Fin 4` antipode arithmetic -/

theorem val_add_two (c : Fin 4) : (c + 2).val = (c.val + 2) % 4 := by
  rw [Fin.val_add, show (2 : Fin 4).val = 2 from by decide]

/-- Adding `2` twice is the identity on `Fin 4`. -/
theorem add_two_add_two (c : Fin 4) : c + 2 + 2 = c := by
  apply Fin.ext
  rw [val_add_two, val_add_two]
  omega

/-- Antipodality is symmetric: `a + 2 = b ↔ b + 2 = a`. -/
theorem add_two_eq_iff {a b : Fin 4} : a + 2 = b ↔ b + 2 = a :=
  ⟨fun h => by rw [← h]; exact add_two_add_two a,
   fun h => by rw [← h]; exact add_two_add_two b⟩

theorem add_two_ne_self (a : Fin 4) : a + 2 ≠ a := by
  intro h
  have hv := congrArg Fin.val h
  rw [val_add_two] at hv
  omega

theorem self_ne_add_two (a : Fin 4) : a ≠ a + 2 := by
  intro h
  exact add_two_ne_self a h.symm

/-- Exhaustion of `Fin 4`: every rail is `0`, `1`, `2`, or `3`. -/
theorem fin4_cases (c : Fin 4) : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 := by
  have hv : c.val = 0 ∨ c.val = 1 ∨ c.val = 2 ∨ c.val = 3 := by
    have h := c.isLt; omega
  rcases hv with h | h | h | h
  · exact Or.inl (Fin.ext (h.trans (by decide)))
  · exact Or.inr (Or.inl (Fin.ext (h.trans (by decide))))
  · exact Or.inr (Or.inr (Or.inl (Fin.ext (h.trans (by decide)))))
  · exact Or.inr (Or.inr (Or.inr (Fin.ext (h.trans (by decide)))))

/-! ### Rail rotation -/

/-- Rotation of the four rails by `k` positions: `i ↦ i + k` modulo `4`,
realised through `Fin.val` arithmetic. -/
def quadRotF (k : ℕ) : Fin 4 → Fin 4 :=
  fun c => ⟨(c.val + k) % 4, Nat.mod_lt _ (by norm_num)⟩

theorem quadRotF_val (k : ℕ) (c : Fin 4) :
    (quadRotF k c).val = (c.val + k) % 4 := rfl

theorem quadRotF_add_two (k : ℕ) (c : Fin 4) :
    quadRotF k c + 2 = quadRotF k (c + 2) := by
  apply Fin.ext
  rw [val_add_two]
  show ((c.val + k) % 4 + 2) % 4 = ((c + 2).val + k) % 4
  rw [val_add_two]
  omega

/-- The point map rotating rails by `k`, fixing the column. -/
def quadRotN (k : ℕ) : Fin 4 × ℕ → Fin 4 × ℕ :=
  fun p => (quadRotF k p.1, p.2)

theorem quadRotN_comp (k k' : ℕ) (p : Fin 4 × ℕ) :
    quadRotN k (quadRotN k' p) = quadRotN (k' + k) p := by
  rcases p with ⟨c, j⟩
  refine Prod.ext_iff.mpr ⟨Fin.ext ?_, rfl⟩
  show ((c.val + k') % 4 + k) % 4 = (c.val + (k' + k)) % 4
  omega

theorem quadRotN_mod (k : ℕ) (p : Fin 4 × ℕ) :
    quadRotN k p = quadRotN (k % 4) p := by
  rcases p with ⟨c, j⟩
  refine Prod.ext_iff.mpr ⟨Fin.ext ?_, rfl⟩
  show (c.val + k) % 4 = (c.val + k % 4) % 4
  omega

theorem quadRotN_injective (k : ℕ) : Function.Injective (quadRotN k) := by
  rintro ⟨c, j⟩ ⟨c', j'⟩ h
  obtain ⟨h1, h2⟩ := Prod.ext_iff.mp h
  have hc : c = c' := by
    apply Fin.ext
    have h3 : (c.val + k) % 4 = (c'.val + k) % 4 := congrArg Fin.val h1
    omega
  exact Prod.ext_iff.mpr ⟨hc, h2⟩

theorem quadRotN_leftInv (k : ℕ) :
    Function.LeftInverse (quadRotN (4 - k % 4)) (quadRotN k) := by
  intro p
  rw [quadRotN_comp]
  rcases p with ⟨c, j⟩
  refine Prod.ext_iff.mpr ⟨Fin.ext ?_, rfl⟩
  show (c.val + (k + (4 - k % 4))) % 4 = c.val
  omega

theorem mem_image_quadRotN {k : ℕ} {p : Fin 4 × ℕ}
    {t : Finset (Fin 4 × ℕ)} :
    p ∈ t.image (quadRotN k) ↔ quadRotN (4 - k % 4) p ∈ t := by
  rw [Finset.mem_image]
  constructor
  · rintro ⟨q, hq, rfl⟩
    rwa [quadRotN_leftInv]
  · intro hp
    refine ⟨quadRotN (4 - k % 4) p, hp, ?_⟩
    rw [quadRotN_comp]
    rcases p with ⟨c, j⟩
    refine Prod.ext_iff.mpr ⟨Fin.ext ?_, rfl⟩
    show (c.val + ((4 - k % 4) + k)) % 4 = c.val
    omega

theorem image_quadRotN_image (k k' : ℕ) (t : Finset (Fin 4 × ℕ)) :
    (t.image (quadRotN k)).image (quadRotN k') =
      t.image (quadRotN (k + k')) := by
  rw [Finset.image_image]
  congr 1
  funext p
  exact quadRotN_comp k' k p

theorem quadRotN_zero : quadRotN 0 = id := by
  funext ⟨c, j⟩
  refine Prod.ext_iff.mpr ⟨Fin.ext ?_, rfl⟩
  show (c.val + 0) % 4 = c.val
  omega

theorem quadRotN_eq_fun (k : ℕ) : quadRotN k = quadRotN (k % 4) :=
  funext fun p => quadRotN_mod k p

/-- Rotating by `k` and then by `4 - k % 4` is the identity image. -/
theorem image_quadRotN_self (k : ℕ) (t : Finset (Fin 4 × ℕ)) :
    (t.image (quadRotN k)).image (quadRotN (4 - k % 4)) = t := by
  rw [image_quadRotN_image]
  have e : k + (4 - k % 4) = 4 * (k / 4 + 1) := by omega
  rw [e]
  have hid : quadRotN (4 * (k / 4 + 1)) = id := by
    rw [quadRotN_eq_fun, show (4 * (k / 4 + 1)) % 4 = 0 by omega,
      quadRotN_zero]
  rw [hid, Finset.image_id]

theorem image_quadRotN_self' (k : ℕ) (t : Finset (Fin 4 × ℕ)) :
    (t.image (quadRotN (4 - k % 4))).image (quadRotN k) = t := by
  rw [image_quadRotN_image]
  have e : (4 - k % 4) + k = 4 * (k / 4 + 1) := by omega
  rw [e]
  have hid : quadRotN (4 * (k / 4 + 1)) = id := by
    rw [quadRotN_eq_fun, show (4 * (k / 4 + 1)) % 4 = 0 by omega,
      quadRotN_zero]
  rw [hid, Finset.image_id]

theorem quadVert_image_quadRotN {k : ℕ} {L : ℕ} {t : Finset (Fin 4 × ℕ)}
    (ht : t ⊆ quadVert L) : t.image (quadRotN k) ⊆ quadVert L := by
  rintro ⟨c, j⟩ hp
  rw [mem_image_quadRotN] at hp
  have hv := ht hp
  rw [mem_quadVert] at hv ⊢
  exact hv

theorem quadFree_image_quadRotN {k : ℕ} {t : Finset (Fin 4 × ℕ)}
    (ht : quadFree t) : quadFree (t.image (quadRotN k)) := by
  constructor
  · rintro ⟨c, j⟩ hp hC
    rw [mem_image_quadRotN] at hp hC
    exact ht.1 (quadRotN (4 - k % 4) (c, j)) hp hC
  · rintro ⟨c, j⟩ hp ⟨c', j'⟩ hq hjj'
    rw [mem_image_quadRotN] at hp hq
    have h := ht.2 (quadRotN (4 - k % 4) (c, j)) hp
      (quadRotN (4 - k % 4) (c', j')) hq hjj'
    rcases h with h | h | h
    · refine Or.inl ?_
      have e : (c.val + (4 - k % 4)) % 4 = (c'.val + (4 - k % 4)) % 4 :=
        congrArg Fin.val h
      have hcc : c = c' := by
        apply Fin.ext
        omega
      exact hcc
    · refine Or.inr (Or.inl ?_)
      have e : ((c.val + (4 - k % 4)) % 4 + 2) % 4 =
          (c'.val + (4 - k % 4)) % 4 := congrArg Fin.val h
      have hcc : c + 2 = c' := by
        apply Fin.ext
        rw [val_add_two]
        omega
      exact hcc
    · refine Or.inr (Or.inr ?_)
      have e : ((c'.val + (4 - k % 4)) % 4 + 2) % 4 =
          (c.val + (4 - k % 4)) % 4 := congrArg Fin.val h
      have hcc : c' + 2 = c := by
        apply Fin.ext
        rw [val_add_two]
        omega
      exact hcc

theorem mem_quadSets_image_quadRotN {k : ℕ} {L : ℕ}
    {u : Finset (Fin 4 × ℕ)} (hu : u ∈ quadSets L) :
    u.image (quadRotN k) ∈ quadSets L := by
  rw [mem_quadSets] at hu ⊢
  exact ⟨quadVert_image_quadRotN hu.1, quadFree_image_quadRotN hu.2⟩

/-- **Rail symmetry.**  Rotating the rails identifies the avoiding
families of `r` and of `r + k` (mod `4`). -/
theorem quadAvoid_rotN_eq_image (r : Fin 4) (k : ℕ) (L : ℕ) :
    quadAvoid (quadRotF k r) L =
      (quadAvoid r L).image fun t => t.image (quadRotN k) := by
  ext u
  rw [mem_quadAvoid, Finset.mem_image]
  constructor
  · rintro ⟨hu, hb⟩
    refine ⟨u.image (quadRotN (4 - k % 4)), ?_, image_quadRotN_self' k u⟩
    rw [mem_quadAvoid]
    refine ⟨mem_quadSets_image_quadRotN hu, fun hC => hb ?_⟩
    have hm := mem_image_quadRotN.mp hC
    have e : quadRotN (4 - (4 - k % 4) % 4) (r, L - 1) =
        (quadRotF k r, L - 1) := by
      exact Prod.ext_iff.mpr ⟨Fin.ext (by
        show (r.val + (4 - (4 - k % 4) % 4)) % 4 = (r.val + k) % 4
        omega), rfl⟩
    exact e ▸ hm
  · rintro ⟨t, ht, rfl⟩
    rw [mem_quadAvoid] at ht
    obtain ⟨ht, hb⟩ := ht
    refine ⟨mem_quadSets_image_quadRotN ht, fun hC => hb ?_⟩
    have hm := mem_image_quadRotN.mp hC
    have e : quadRotN (4 - k % 4) (quadRotF k r, L - 1) = (r, L - 1) := by
      exact Prod.ext_iff.mpr ⟨Fin.ext (by
        show ((r.val + k) % 4 + (4 - k % 4)) % 4 = r.val; omega), rfl⟩
    rwa [e] at hm

/-- Rotating the rails also identifies the pair-avoiding families. -/
theorem quadAvoid2_rotN_eq_image (a : Fin 4) (k : ℕ) (L : ℕ) :
    quadAvoid2 (quadRotF k a) L =
      (quadAvoid2 a L).image fun t => t.image (quadRotN k) := by
  ext u
  rw [mem_quadAvoid2, Finset.mem_image, quadRotF_add_two]
  constructor
  · rintro ⟨hu, hb1, hb2⟩
    refine ⟨u.image (quadRotN (4 - k % 4)), ?_, image_quadRotN_self' k u⟩
    rw [mem_quadAvoid2]
    refine ⟨mem_quadSets_image_quadRotN hu, fun hC => hb1 ?_,
      fun hC => hb2 ?_⟩
    · have hm := mem_image_quadRotN.mp hC
      have e : quadRotN (4 - (4 - k % 4) % 4) (a, L - 1) =
          (quadRotF k a, L - 1) := by
        exact Prod.ext_iff.mpr ⟨Fin.ext (by
          show (a.val + (4 - (4 - k % 4) % 4)) % 4 = (a.val + k) % 4
          omega), rfl⟩
      exact e ▸ hm
    · have hm := mem_image_quadRotN.mp hC
      have e : quadRotN (4 - (4 - k % 4) % 4) (a + 2, L - 1) =
          (quadRotF k (a + 2), L - 1) := by
        exact Prod.ext_iff.mpr ⟨Fin.ext (by
          show ((a + 2).val + (4 - (4 - k % 4) % 4)) % 4 =
            ((a + 2).val + k) % 4
          omega), rfl⟩
      exact e ▸ hm
  · rintro ⟨t, ht, rfl⟩
    rw [mem_quadAvoid2] at ht
    obtain ⟨ht, hb1, hb2⟩ := ht
    refine ⟨mem_quadSets_image_quadRotN ht, fun hC => hb1 ?_,
      fun hC => hb2 ?_⟩
    · have hm := mem_image_quadRotN.mp hC
      have e : quadRotN (4 - k % 4) (quadRotF k a, L - 1) = (a, L - 1) := by
        exact Prod.ext_iff.mpr ⟨Fin.ext (by
          show ((a.val + k) % 4 + (4 - k % 4)) % 4 = a.val; omega), rfl⟩
      rwa [e] at hm
    · have hm := mem_image_quadRotN.mp hC
      have e : quadRotN (4 - k % 4) (quadRotF k (a + 2), L - 1) =
          (a + 2, L - 1) := by
        exact Prod.ext_iff.mpr ⟨Fin.ext (by
          show (((a + 2).val + k) % 4 + (4 - k % 4)) % 4 = (a + 2).val
          omega), rfl⟩
      rwa [e] at hm

/-- All four singleton-avoiding families have the same cardinality. -/
theorem quadAvoid_card_eq (r r' : Fin 4) (L : ℕ) :
    (quadAvoid r L).card = (quadAvoid r' L).card := by
  have h : quadRotF (r'.val + 4 - r.val) r = r' := by
    apply Fin.ext
    show (r.val + (r'.val + 4 - r.val)) % 4 = r'.val
    omega
  rw [← h, quadAvoid_rotN_eq_image]
  exact (Finset.card_image_of_injective _
    (Finset.image_injective (quadRotN_injective _))).symm

/-- Both antipodal-pair-avoiding families have the same cardinality. -/
theorem quadAvoid2_card_eq (a b : Fin 4) (L : ℕ) :
    (quadAvoid2 a L).card = (quadAvoid2 b L).card := by
  have h : quadRotF (b.val + 4 - a.val) a = b := by
    apply Fin.ext
    show (a.val + (b.val + 4 - a.val)) % 4 = b.val
    omega
  rw [← h, quadAvoid2_rotN_eq_image]
  exact (Finset.card_image_of_injective _
    (Finset.image_injective (quadRotN_injective _))).symm

/-- `quadAvoid2` only sees the pair `{a, a+2}`, which is unchanged by
`a ↦ a + 2`. -/
theorem quadAvoid2_add_two (a : Fin 4) (L : ℕ) :
    quadAvoid2 (a + 2) L = quadAvoid2 a L := by
  ext t
  rw [mem_quadAvoid2, mem_quadAvoid2, add_two_add_two]
  constructor
  · rintro ⟨hs, h1, h2⟩; exact ⟨hs, h2, h1⟩
  · rintro ⟨hs, h1, h2⟩; exact ⟨hs, h2, h1⟩

/-! ### Column decomposition -/

/-- Members of `quadSets (L+1)` with an empty last column are exactly
the independent sets of the `4 × L` strip. -/
theorem mem_quadSets_of_succ {L : ℕ} {t : Finset (Fin 4 × ℕ)}
    (ht : t ∈ quadSets (L + 1)) (hf : ∀ r : Fin 4, (r, L) ∉ t) :
    t ∈ quadSets L := by
  rw [mem_quadSets] at ht ⊢
  obtain ⟨hsub, hfree⟩ := ht
  refine ⟨?_, hfree⟩
  rintro ⟨c, j⟩ hp
  have hv := hsub hp
  rw [mem_quadVert] at hv ⊢
  rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hv) with h | h
  · exact h
  · rw [h] at hp
    exact absurd hp (hf c)

/-- Erasing `(r, L)` from an independent set containing it — and no
other column-`L` cell, i.e. `(r+2, L)` absent — leaves an element of
`quadAvoid r L`. -/
theorem erase_mem_quadAvoid {r : Fin 4} {L : ℕ} {t : Finset (Fin 4 × ℕ)}
    (ht : t ∈ quadSets (L + 1)) (hb : (r, L) ∈ t) (hn : (r + 2, L) ∉ t) :
    t.erase (r, L) ∈ quadAvoid r L := by
  rw [mem_quadSets] at ht
  obtain ⟨hsub, hfree⟩ := ht
  have hU : t.erase (r, L) ⊆ quadVert L := by
    rintro ⟨c, j⟩ hp
    rw [Finset.mem_erase] at hp
    obtain ⟨hne, hp⟩ := hp
    have hv := hsub hp
    rw [mem_quadVert] at hv ⊢
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
        exact hn (by rwa [hcc] at hp)
      · have hcc : c = r + 2 := (add_two_eq_iff.mp hrc).symm
        exfalso
        exact hn (by rwa [hcc] at hp)
  rw [mem_quadAvoid, mem_quadSets]
  refine ⟨⟨hU, hfree.mono (Finset.erase_subset _ _)⟩, ?_⟩
  intro hC
  have hmem := Finset.mem_of_mem_erase hC
  have hv := hU hC
  rw [mem_quadVert] at hv
  have hL : 1 ≤ L := by omega
  have h1 := hfree.1 (r, L - 1) hmem
  rw [Nat.sub_add_cancel hL] at h1
  exact h1 hb

/-- Erasing the antipodal pair `{(a, L), (a+2, L)}` from an independent
set containing it leaves an element of `quadAvoid2 a L` (the `C4`
condition kills every other cell of column `L`). -/
theorem erase2_mem_quadAvoid2 {a : Fin 4} {L : ℕ}
    {t : Finset (Fin 4 × ℕ)}
    (ht : t ∈ quadSets (L + 1)) (h1 : (a, L) ∈ t) (h2 : (a + 2, L) ∈ t) :
    (t.erase (a, L)).erase (a + 2, L) ∈ quadAvoid2 a L := by
  rw [mem_quadSets] at ht
  obtain ⟨hsub, hfree⟩ := ht
  have hU : (t.erase (a, L)).erase (a + 2, L) ⊆ quadVert L := by
    rintro ⟨c, j⟩ hp
    rw [Finset.mem_erase, Finset.mem_erase] at hp
    obtain ⟨hne2, hne1, hp⟩ := hp
    have hv := hsub hp
    rw [mem_quadVert] at hv ⊢
    rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hv) with h | h
    · exact h
    · rw [h] at hp hne1 hne2
      have hrc := hfree.2 (a, L) h1 (c, L) hp rfl
      rcases hrc with hrc | hrc | hrc
      · have hcc : c = a := hrc.symm
        exfalso
        exact hne1 (Prod.ext_iff.mpr ⟨hcc, rfl⟩)
      · have hcc : c = a + 2 := hrc.symm
        exfalso
        exact hne2 (Prod.ext_iff.mpr ⟨hcc, rfl⟩)
      · have hcc : c = a + 2 := (add_two_eq_iff.mp hrc).symm
        exfalso
        exact hne2 (Prod.ext_iff.mpr ⟨hcc, rfl⟩)
  rw [mem_quadAvoid2, mem_quadSets]
  refine ⟨⟨hU, hfree.mono
    ((Finset.erase_subset _ _).trans (Finset.erase_subset _ _))⟩, ?_, ?_⟩
  · intro hC
    have hmem := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hC)
    have hv := hU hC
    rw [mem_quadVert] at hv
    have hL : 1 ≤ L := by omega
    have h3 := hfree.1 (a, L - 1) hmem
    rw [Nat.sub_add_cancel hL] at h3
    exact h3 h1
  · intro hC
    have hmem := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hC)
    have hv := hU hC
    rw [mem_quadVert] at hv
    have hL : 1 ≤ L := by omega
    have h3 := hfree.1 (a + 2, L - 1) hmem
    rw [Nat.sub_add_cancel hL] at h3
    exact h3 h2

/-- Inserting `(r, L)` into an element of `quadAvoid r L` stays
independent: the other column-`L` cells and the rail predecessor
`(r, L-1)` are absent. -/
theorem mem_quadSets_succ_of_mem_quadAvoid {r : Fin 4} {L : ℕ}
    {u : Finset (Fin 4 × ℕ)} (hu : u ∈ quadAvoid r L) :
    insert (r, L) u ∈ quadSets (L + 1) := by
  rw [mem_quadAvoid, mem_quadSets] at hu
  obtain ⟨⟨hsub, hfree⟩, hb⟩ := hu
  rw [mem_quadSets]
  refine ⟨?_, ⟨?_, ?_⟩⟩
  · rintro ⟨c, j⟩ hp
    rw [Finset.mem_insert] at hp
    rw [mem_quadVert]
    rcases hp with hp | hp
    · have e2 : j = L := (Prod.ext_iff.mp hp).2
      rw [e2]
      exact Nat.lt_succ_self L
    · have hv := hsub hp
      rw [mem_quadVert] at hv
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
        rw [mem_quadVert] at hv
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
        rw [mem_quadVert] at hv
        omega
    · rcases hq with hq | hq
      · have ej' : j' = L := (Prod.ext_iff.mp hq).2
        rw [ej'] at hjj'
        have hv := hsub hp
        rw [mem_quadVert] at hv
        omega
      · exact hfree.2 (c, j) hp (c', j') hq hjj'

/-- Inserting the antipodal pair `{(a, L), (a+2, L)}` into an element of
`quadAvoid2 a L` stays independent. -/
theorem mem_quadSets_succ_of_mem_quadAvoid2 {a : Fin 4} {L : ℕ}
    {u : Finset (Fin 4 × ℕ)} (hu : u ∈ quadAvoid2 a L) :
    insert (a, L) (insert (a + 2, L) u) ∈ quadSets (L + 1) := by
  rw [mem_quadAvoid2, mem_quadSets] at hu
  obtain ⟨⟨hsub, hfree⟩, hb1, hb2⟩ := hu
  rw [mem_quadSets]
  refine ⟨?_, ⟨?_, ?_⟩⟩
  · rintro ⟨c, j⟩ hp
    rw [Finset.mem_insert, Finset.mem_insert] at hp
    rw [mem_quadVert]
    rcases hp with hp | hp | hp
    · have e : j = L := (Prod.ext_iff.mp hp).2
      rw [e]; exact Nat.lt_succ_self L
    · have e : j = L := (Prod.ext_iff.mp hp).2
      rw [e]; exact Nat.lt_succ_self L
    · have hv := hsub hp
      rw [mem_quadVert] at hv
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
        have hv : (a, L + 1) ∈ quadVert L := hsub hC
        rw [mem_quadVert] at hv
        omega
      · have e3 : c = a + 2 := (Prod.ext_iff.mp hp).1
        have e4 : j = L := (Prod.ext_iff.mp hp).2
        rw [e3, e4] at hC
        have hv : (a + 2, L + 1) ∈ quadVert L := hsub hC
        rw [mem_quadVert] at hv
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
        rw [mem_quadVert] at hv
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
        rw [mem_quadVert] at hv
        omega
    · rcases hq with hq | hq | hq
      · have e3 : c' = a := (Prod.ext_iff.mp hq).1
        have e4 : j' = L := (Prod.ext_iff.mp hq).2
        have hjj : j = j' := hjj'
        have hv := hsub hp
        rw [mem_quadVert] at hv
        omega
      · have e3 : c' = a + 2 := (Prod.ext_iff.mp hq).1
        have e4 : j' = L := (Prod.ext_iff.mp hq).2
        have hjj : j = j' := hjj'
        have hv := hsub hp
        rw [mem_quadVert] at hv
        omega
      · exact hfree.2 (c, j) hp (c', j') hq hjj'

/-- **Pair column lemma.**  If an independent set of the `4 × (L+1)`
strip contains the antipodal pair `{(c, L), (c+2, L)}` in its last
column, then it is the double-insert of an element of `quadAvoid2 a L`
over the canonical representative `a ∈ {0,1}` of that pair, and the
last column contains both cells of the pair. -/
theorem quad_pair_col {L : ℕ} {t : Finset (Fin 4 × ℕ)} {c : Fin 4}
    (ht : t ∈ quadSets (L + 1)) (h1 : (c, L) ∈ t) (h2 : (c + 2, L) ∈ t) :
    ∃ a ∈ ({0, 1} : Finset (Fin 4)), ∃ u ∈ quadAvoid2 a L,
      t = insert (a, L) (insert (a + 2, L) u) ∧
        (a, L) ∈ t ∧ (a + 2, L) ∈ t := by
  have key : ∀ a : Fin 4, (a, L) ∈ t → (a + 2, L) ∈ t →
      ∃ u ∈ quadAvoid2 a L,
        t = insert (a, L) (insert (a + 2, L) u) ∧
          (a, L) ∈ t ∧ (a + 2, L) ∈ t := by
    intro a ha1 ha2
    refine ⟨(t.erase (a, L)).erase (a + 2, L),
      erase2_mem_quadAvoid2 ht ha1 ha2, ?_, ha1, ha2⟩
    have hne : (a + 2, L) ≠ (a, L) := fun e =>
      add_two_ne_self a (Prod.ext_iff.mp e).1
    have step : insert (a + 2, L) ((t.erase (a, L)).erase (a + 2, L)) =
        t.erase (a, L) :=
      Finset.insert_erase (Finset.mem_erase.mpr ⟨hne, ha2⟩)
    rw [step, Finset.insert_erase ha1]
  rcases fin4_cases c with rfl | rfl | rfl | rfl
  · exact ⟨0, by decide, key 0 h1 h2⟩
  · exact ⟨1, by decide, key 1 h1 h2⟩
  · -- c = 2: pair `{2, 0}` with canonical representative `0`
    exact ⟨0, by decide, key 0 h2 h1⟩
  · -- c = 3: pair `{3, 1}` with canonical representative `1`
    exact ⟨1, by decide, key 1 h2 h1⟩

/-- **Column decomposition.**  `quadSets (L+1)` is the disjoint union of
the sets with empty last column (`quadSets L`), the sets ending in a
singleton `{(r, L)}` (four symmetric choices), and the sets ending in
an antipodal pair (two choices, indexed by `{0,1}`). -/
theorem quadSets_succ (L : ℕ) :
    quadSets (L + 1) =
      quadSets L ∪ (Finset.univ : Finset (Fin 4)).biUnion
          (fun r => (quadAvoid r L).image fun t => insert (r, L) t) ∪
        (({0, 1} : Finset (Fin 4)).biUnion fun a => (quadAvoid2 a L).image
          fun t => insert (a, L) (insert (a + 2, L) t)) := by
  ext t
  simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_image,
    Finset.mem_univ, true_and]
  constructor
  · intro ht
    by_cases h : ∃ c : Fin 4, (c, L) ∈ t
    · obtain ⟨c, hc⟩ := h
      by_cases h2 : (c + 2, L) ∈ t
      · obtain ⟨a, ha01, u, hu, ht_eq, hm1, hm2⟩ := quad_pair_col ht hc h2
        exact Or.inr ⟨a, ha01, u, hu, ht_eq.symm⟩
      · exact Or.inl (Or.inr ⟨c, t.erase (c, L),
          erase_mem_quadAvoid ht hc h2, Finset.insert_erase hc⟩)
    · exact Or.inl (Or.inl (mem_quadSets_of_succ ht fun c hc => h ⟨c, hc⟩))
  · rintro ((ht | ⟨c, u, hu, rfl⟩) | ⟨a, -, u, hu, rfl⟩)
    · exact quadSets_mono L ht
    · exact mem_quadSets_succ_of_mem_quadAvoid hu
    · exact mem_quadSets_succ_of_mem_quadAvoid2 hu

/-- The avoiding family at level `L+1`: sets with empty last column
(`quadSets L`), sets ending in `{(c, L)}` for `c ≠ r`, and sets ending
in the antipodal pair disjoint from `r` (exactly one of the two). -/
theorem quadAvoid_succ (L : ℕ) (r : Fin 4) :
    quadAvoid r (L + 1) =
      quadSets L ∪ (Finset.univ.filter fun c => c ≠ r).biUnion
          (fun c => (quadAvoid c L).image fun t => insert (c, L) t) ∪
        ((({0, 1} : Finset (Fin 4)).filter fun a => r ≠ a ∧ r ≠ a + 2).biUnion
          fun a => (quadAvoid2 a L).image
            fun t => insert (a, L) (insert (a + 2, L) t)) := by
  ext t
  simp only [mem_quadAvoid, Nat.add_sub_cancel, Finset.mem_union,
    Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
    true_and]
  constructor
  · rintro ⟨ht, hr⟩
    by_cases h : ∃ c : Fin 4, (c, L) ∈ t
    · obtain ⟨c, hc⟩ := h
      by_cases h2 : (c + 2, L) ∈ t
      · obtain ⟨a, ha01, u, hu, ht_eq, hm1, hm2⟩ := quad_pair_col ht hc h2
        exact Or.inr ⟨a, ⟨ha01,
            fun e => hr (by rwa [← e] at hm1),
            fun e => hr (by rwa [← e] at hm2)⟩,
          u, hu, ht_eq.symm⟩
      · exact Or.inl (Or.inr ⟨c, fun e => hr (by rwa [e] at hc),
          t.erase (c, L), mem_quadAvoid.mp (erase_mem_quadAvoid ht hc h2),
          Finset.insert_erase hc⟩)
    · exact Or.inl (Or.inl (mem_quadSets_of_succ ht fun c hc => h ⟨c, hc⟩))
  · rintro ((ht | ⟨c, hcr, u, hu, rfl⟩) |
      ⟨a, ⟨-, hra, hra2⟩, u, hu, rfl⟩)
    · refine ⟨quadSets_mono L ht, fun hC => ?_⟩
      have hv := (mem_quadSets.mp ht).1 hC
      rw [mem_quadVert] at hv
      exact absurd hv (lt_irrefl _)
    · refine ⟨mem_quadSets_succ_of_mem_quadAvoid (mem_quadAvoid.mpr hu),
        fun hC => ?_⟩
      rw [Finset.mem_insert] at hC
      rcases hC with hC | hC
      · exact hcr (Prod.ext_iff.mp hC).1.symm
      · have hv := (mem_quadSets.mp hu.1).1 hC
        rw [mem_quadVert] at hv
        exact absurd hv (lt_irrefl _)
    · refine ⟨mem_quadSets_succ_of_mem_quadAvoid2 hu, fun hC => ?_⟩
      rw [Finset.mem_insert, Finset.mem_insert] at hC
      rcases hC with hC | hC | hC
      · exact hra (Prod.ext_iff.mp hC).1
      · exact hra2 (Prod.ext_iff.mp hC).1
      · have hv := (mem_quadSets.mp (mem_quadAvoid2.mp hu).1).1 hC
        rw [mem_quadVert] at hv
        exact absurd hv (lt_irrefl _)

/-- The pair-avoiding family `quadAvoid2 0` at level `L+1`: sets with
empty last column, sets ending in `{(c, L)}` for `c ∈ {1,3}`, and sets
ending in the pair `{1,3}` (the unique antipodal pair disjoint from
`{0,2}`). -/
theorem quadAvoid2_zero_succ (L : ℕ) :
    quadAvoid2 0 (L + 1) =
      quadSets L ∪ (Finset.univ.filter fun c => c ≠ 0 ∧ c ≠ 0 + 2).biUnion
          (fun c => (quadAvoid c L).image fun t => insert (c, L) t) ∪
        ((({0, 1} : Finset (Fin 4)).filter fun a =>
            (0 : Fin 4) ≠ a ∧ 0 ≠ a + 2 ∧ (0 : Fin 4) + 2 ≠ a ∧
              (0 : Fin 4) + 2 ≠ a + 2).biUnion
          fun a => (quadAvoid2 a L).image
            fun t => insert (a, L) (insert (a + 2, L) t)) := by
  ext t
  simp only [mem_quadAvoid2, Nat.add_sub_cancel, Finset.mem_union,
    Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
    true_and]
  constructor
  · rintro ⟨ht, hb1, hb2⟩
    by_cases h : ∃ c : Fin 4, (c, L) ∈ t
    · obtain ⟨c, hc⟩ := h
      by_cases h2 : (c + 2, L) ∈ t
      · obtain ⟨a, ha01, u, hu, ht_eq, hm1, hm2⟩ := quad_pair_col ht hc h2
        exact Or.inr ⟨a, ⟨ha01,
            fun e => hb1 (by rwa [← e] at hm1),
            fun e => hb1 (by rwa [← e] at hm2),
            fun e => hb2 (by rwa [← e] at hm1),
            fun e => hb2 (by rwa [← e] at hm2)⟩,
          u, mem_quadAvoid2.mp hu, ht_eq.symm⟩
      · exact Or.inl (Or.inr ⟨c,
          ⟨fun e => hb1 (by rwa [e] at hc),
           fun e => hb2 (by rwa [e] at hc)⟩,
          t.erase (c, L), erase_mem_quadAvoid ht hc h2,
          Finset.insert_erase hc⟩)
    · exact Or.inl (Or.inl (mem_quadSets_of_succ ht fun c hc => h ⟨c, hc⟩))
  · rintro ((ht | ⟨c, ⟨hc1, hc2⟩, u, hu, rfl⟩) |
      ⟨a, ⟨-, h1, h2, h3, h4⟩, u, hu, rfl⟩)
    · refine ⟨quadSets_mono L ht, fun hC => ?_, fun hC => ?_⟩
      · have hv := (mem_quadSets.mp ht).1 hC
        rw [mem_quadVert] at hv
        exact absurd hv (lt_irrefl _)
      · have hv := (mem_quadSets.mp ht).1 hC
        rw [mem_quadVert] at hv
        exact absurd hv (lt_irrefl _)
    · refine ⟨mem_quadSets_succ_of_mem_quadAvoid hu, fun hC => ?_,
        fun hC => ?_⟩
      · rw [Finset.mem_insert] at hC
        rcases hC with hC | hC
        · exact hc1 (Prod.ext_iff.mp hC).1.symm
        · have hv := (mem_quadSets.mp (mem_quadAvoid.mp hu).1).1 hC
          rw [mem_quadVert] at hv
          exact absurd hv (lt_irrefl _)
      · rw [Finset.mem_insert] at hC
        rcases hC with hC | hC
        · exact hc2 (Prod.ext_iff.mp hC).1.symm
        · have hv := (mem_quadSets.mp (mem_quadAvoid.mp hu).1).1 hC
          rw [mem_quadVert] at hv
          exact absurd hv (lt_irrefl _)
    · refine ⟨mem_quadSets_succ_of_mem_quadAvoid2 (mem_quadAvoid2.mpr hu),
        fun hC => ?_, fun hC => ?_⟩
      · rw [Finset.mem_insert, Finset.mem_insert] at hC
        rcases hC with hC | hC | hC
        · exact h1 (Prod.ext_iff.mp hC).1
        · exact h2 (Prod.ext_iff.mp hC).1
        · have hv := (mem_quadSets.mp hu.1).1 hC
          rw [mem_quadVert] at hv
          exact absurd hv (lt_irrefl _)
      · rw [Finset.mem_insert, Finset.mem_insert] at hC
        rcases hC with hC | hC | hC
        · exact h3 (Prod.ext_iff.mp hC).1
        · exact h4 (Prod.ext_iff.mp hC).1
        · have hv := (mem_quadSets.mp hu.1).1 hC
          rw [mem_quadVert] at hv
          exact absurd hv (lt_irrefl _)

/-! ### Cardinality lemmas -/

/-- The `insert (r, L)` image of `quadAvoid r L` has the same
cardinality: `erase (r, L)` inverts it. -/
theorem quadCard_image_insert (r : Fin 4) (L : ℕ) :
    ((quadAvoid r L).image fun t => insert (r, L) t).card =
      (quadAvoid r L).card := by
  apply Finset.card_image_of_injOn
  intro t₁ ht₁ t₂ ht₂ h
  rw [Finset.mem_coe, mem_quadAvoid, mem_quadSets] at ht₁ ht₂
  have h1 : (r, L) ∉ t₁ := by
    intro hC
    have hv := ht₁.1.1 hC
    rw [mem_quadVert] at hv
    exact absurd hv (lt_irrefl _)
  have h2 : (r, L) ∉ t₂ := by
    intro hC
    have hv := ht₂.1.1 hC
    rw [mem_quadVert] at hv
    exact absurd hv (lt_irrefl _)
  have e := congrArg (Finset.erase · (r, L)) h
  rwa [Finset.erase_insert h1, Finset.erase_insert h2] at e

/-- The double-`insert` image of `quadAvoid2 a L` has the same
cardinality: the double `erase` inverts it. -/
theorem quadCard_image_insert2 (a : Fin 4) (L : ℕ) :
    ((quadAvoid2 a L).image fun t => insert (a, L)
        (insert (a + 2, L) t)).card =
      (quadAvoid2 a L).card := by
  apply Finset.card_image_of_injOn
  intro t₁ ht₁ t₂ ht₂ h
  rw [Finset.mem_coe, mem_quadAvoid2, mem_quadSets] at ht₁ ht₂
  have h1 : (a, L) ∉ t₁ := by
    intro hC
    have hv := ht₁.1.1 hC
    rw [mem_quadVert] at hv
    exact absurd hv (lt_irrefl _)
  have h1' : (a, L) ∉ t₂ := by
    intro hC
    have hv := ht₂.1.1 hC
    rw [mem_quadVert] at hv
    exact absurd hv (lt_irrefl _)
  have h2 : (a + 2, L) ∉ t₁ := by
    intro hC
    have hv := ht₁.1.1 hC
    rw [mem_quadVert] at hv
    exact absurd hv (lt_irrefl _)
  have h2' : (a + 2, L) ∉ t₂ := by
    intro hC
    have hv := ht₂.1.1 hC
    rw [mem_quadVert] at hv
    exact absurd hv (lt_irrefl _)
  have hn1 : (a, L) ∉ insert (a + 2, L) t₁ := fun hm =>
    (Finset.mem_insert.mp hm).elim
      (fun e => absurd (Prod.ext_iff.mp e).1.symm (add_two_ne_self a)) h1
  have hn2 : (a, L) ∉ insert (a + 2, L) t₂ := fun hm =>
    (Finset.mem_insert.mp hm).elim
      (fun e => absurd (Prod.ext_iff.mp e).1.symm (add_two_ne_self a)) h1'
  have e := congrArg (fun s => (s.erase (a, L)).erase (a + 2, L)) h
  rwa [Finset.erase_insert hn1, Finset.erase_insert h2,
    Finset.erase_insert hn2, Finset.erase_insert h2'] at e

/-- `quadSets L` is disjoint from any singleton-image biUnion: the
images contain a column-`L` cell, members of `quadSets L` do not. -/
theorem quad_disjoint_sets_single (L : ℕ) (s : Finset (Fin 4)) :
    Disjoint (quadSets L)
      (s.biUnion fun c => (quadAvoid c L).image
        fun t => insert (c, L) t) := by
  rw [Finset.disjoint_left]
  intro t ht hB
  rw [Finset.mem_biUnion] at hB
  obtain ⟨c, -, hr⟩ := hB
  obtain ⟨u, -, rfl⟩ := Finset.mem_image.mp hr
  have hv := (mem_quadSets.mp ht).1 (Finset.mem_insert_self (c, L) u)
  rw [mem_quadVert] at hv
  exact absurd hv (lt_irrefl _)

/-- `quadSets L` is disjoint from any pair-image biUnion. -/
theorem quad_disjoint_sets_pair (L : ℕ) (s : Finset (Fin 4)) :
    Disjoint (quadSets L)
      (s.biUnion fun a => (quadAvoid2 a L).image
        fun t => insert (a, L) (insert (a + 2, L) t)) := by
  rw [Finset.disjoint_left]
  intro t ht hB
  rw [Finset.mem_biUnion] at hB
  obtain ⟨a, -, hr⟩ := hB
  obtain ⟨u, -, rfl⟩ := Finset.mem_image.mp hr
  have hv := (mem_quadSets.mp ht).1 (Finset.mem_insert_self (a, L) _)
  rw [mem_quadVert] at hv
  exact absurd hv (lt_irrefl _)

/-- Singleton-image families over distinct rails are disjoint. -/
theorem quad_single_pw (L : ℕ) (s : Finset (Fin 4)) :
    ((s : Set (Fin 4)).PairwiseDisjoint
      fun c => (quadAvoid c L).image fun t => insert (c, L) t) := by
  rintro c - c' - hcc
  show Disjoint ((quadAvoid c L).image fun t => insert (c, L) t)
    ((quadAvoid c' L).image fun t => insert (c', L) t)
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
  · have hv' := (mem_quadSets.mp (mem_quadAvoid.mp hv).1).1 hmem
    rw [mem_quadVert] at hv'
    exact absurd hv' (lt_irrefl _)

/-- Pair-image families over distinct representatives in `{0,1}` are
disjoint (the pairs `{0,2}` and `{1,3}` are different). -/
theorem quad_pair_pw (L : ℕ) (s : Finset (Fin 4))
    (hs : s ⊆ ({0, 1} : Finset (Fin 4))) :
    ((s : Set (Fin 4)).PairwiseDisjoint
      fun a => (quadAvoid2 a L).image
        fun t => insert (a, L) (insert (a + 2, L) t)) := by
  rintro a ha a' ha' haa
  have ha01 : a = 0 ∨ a = 1 := by
    have h := hs (Finset.mem_coe.mp ha)
    rwa [Finset.mem_insert, Finset.mem_singleton] at h
  have ha'01 : a' = 0 ∨ a' = 1 := by
    have h := hs (Finset.mem_coe.mp ha')
    rwa [Finset.mem_insert, Finset.mem_singleton] at h
  show Disjoint ((quadAvoid2 a L).image
      fun t => insert (a, L) (insert (a + 2, L) t))
    ((quadAvoid2 a' L).image
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
    rcases ha01 with rfl | rfl <;> rcases ha'01 with rfl | rfl <;>
      exact absurd e (by decide)
  · have hv' := (mem_quadSets.mp (mem_quadAvoid2.mp hv).1).1 hmem
    rw [mem_quadVert] at hv'
    exact absurd hv' (lt_irrefl _)

/-- A singleton image and a pair image are disjoint: the former has
exactly one cell in column `L`, the latter has two. -/
theorem quad_disjoint_single_pair (L : ℕ) (s₁ s₂ : Finset (Fin 4)) :
    Disjoint (s₁.biUnion fun c => (quadAvoid c L).image
        fun t => insert (c, L) t)
      (s₂.biUnion fun a => (quadAvoid2 a L).image
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
      exact absurd (e2.trans e1.symm) (add_two_ne_self a)
    · have hv' := (mem_quadSets.mp (mem_quadAvoid.mp hv).1).1 hm2
      rw [mem_quadVert] at hv'
      exact absurd hv' (lt_irrefl _)
  · have hv' := (mem_quadSets.mp (mem_quadAvoid.mp hv).1).1 hm1
    rw [mem_quadVert] at hv'
    exact absurd hv' (lt_irrefl _)

/-- Union of the disjointness facts: `quadSets L ∪ singles` is disjoint
from the pair biUnion. -/
theorem quad_disjoint_union_pair (L : ℕ) (s₁ s₂ : Finset (Fin 4)) :
    Disjoint (quadSets L ∪ s₁.biUnion fun c => (quadAvoid c L).image
        fun t => insert (c, L) t)
      (s₂.biUnion fun a => (quadAvoid2 a L).image
        fun t => insert (a, L) (insert (a + 2, L) t)) := by
  rw [Finset.disjoint_left]
  intro t ht hB
  rcases Finset.mem_union.mp ht with ht | ht
  · exact Finset.disjoint_left.mp (quad_disjoint_sets_pair L s₂) ht hB
  · exact Finset.disjoint_left.mp (quad_disjoint_single_pair L s₁ s₂) ht hB

/-- `T(L+1) = T(L) + 4·A(L) + 2·B(L)`: one choice for the empty last
column, four symmetric singleton choices, and two antipodal-pair
choices. -/
theorem quadSets_card_succ (L : ℕ) :
    (quadSets (L + 1)).card =
      (quadSets L).card + 4 * (quadAvoid 0 L).card +
        2 * (quadAvoid2 0 L).card := by
  have d_top := quad_disjoint_union_pair L Finset.univ {0, 1}
  have d_AS := quad_disjoint_sets_single L Finset.univ
  have pw_S := quad_single_pw L Finset.univ
  have pw_P := quad_pair_pw L {0, 1} (Finset.Subset.refl _)
  rw [quadSets_succ, Finset.card_union_of_disjoint d_top,
    Finset.card_union_of_disjoint d_AS, Finset.card_biUnion pw_S,
    Finset.card_biUnion pw_P]
  have hsum : (∑ r ∈ Finset.univ,
        ((quadAvoid r L).image fun t => insert (r, L) t).card)
      = ∑ _r ∈ (Finset.univ : Finset (Fin 4)), (quadAvoid 0 L).card := by
    apply Finset.sum_congr rfl
    intro r _
    rw [quadCard_image_insert]
    exact quadAvoid_card_eq r 0 L
  rw [hsum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    Nat.nsmul_eq_mul]
  have hsum2 : (∑ a ∈ ({0, 1} : Finset (Fin 4)),
        ((quadAvoid2 a L).image fun t => insert (a, L)
          (insert (a + 2, L) t)).card)
      = ∑ _a ∈ ({0, 1} : Finset (Fin 4)), (quadAvoid2 0 L).card := by
    apply Finset.sum_congr rfl
    intro a _
    rw [quadCard_image_insert2]
    exact quadAvoid2_card_eq a 0 L
  rw [hsum2, Finset.sum_const, Nat.nsmul_eq_mul,
    Finset.card_pair (by decide : (0 : Fin 4) ≠ 1)]

/-- `A(L+1) = T(L) + 3·A(L) + B(L)`: an `r`-avoiding set of length
`L+1` has empty last column, ends in one of the three other rails, or
ends in the unique antipodal pair disjoint from `r`. -/
theorem quadAvoid_succ_card (L : ℕ) (r : Fin 4) :
    (quadAvoid r (L + 1)).card =
      (quadSets L).card + 3 * (quadAvoid r L).card +
        (quadAvoid2 0 L).card := by
  have d_top := quad_disjoint_union_pair L
    (Finset.univ.filter fun c => c ≠ r)
    (({0, 1} : Finset (Fin 4)).filter fun a : Fin 4 =>
      r ≠ a ∧ r ≠ a + 2)
  have d_AS := quad_disjoint_sets_single L
    (Finset.univ.filter fun c => c ≠ r)
  have pw_S := quad_single_pw L (Finset.univ.filter fun c => c ≠ r)
  have pw_P := quad_pair_pw L
    (({0, 1} : Finset (Fin 4)).filter fun a : Fin 4 =>
      r ≠ a ∧ r ≠ a + 2) (Finset.filter_subset _ _)
  rw [quadAvoid_succ, Finset.card_union_of_disjoint d_top,
    Finset.card_union_of_disjoint d_AS, Finset.card_biUnion pw_S,
    Finset.card_biUnion pw_P]
  have hcard : ((Finset.univ : Finset (Fin 4)).filter
      fun c => c ≠ r).card = 3 := by
    rw [Finset.filter_ne' _ r,
      Finset.card_erase_of_mem (Finset.mem_univ r), Finset.card_univ,
      Fintype.card_fin]
  have hsum : (∑ c ∈ Finset.univ.filter fun c => c ≠ r,
        ((quadAvoid c L).image fun t => insert (c, L) t).card)
      = ∑ _c ∈ Finset.univ.filter (fun c => c ≠ r),
        (quadAvoid r L).card := by
    apply Finset.sum_congr rfl
    intro c _
    rw [quadCard_image_insert]
    exact quadAvoid_card_eq c r L
  rw [hsum, Finset.sum_const, hcard, Nat.nsmul_eq_mul]
  have hcard2 : (({0, 1} : Finset (Fin 4)).filter
      fun a => r ≠ a ∧ r ≠ a + 2).card = 1 := by
    fin_cases r <;> decide
  have hsum2 : (∑ a ∈ ({0, 1} : Finset (Fin 4)).filter
        fun a => r ≠ a ∧ r ≠ a + 2,
        ((quadAvoid2 a L).image fun t => insert (a, L)
          (insert (a + 2, L) t)).card)
      = ∑ _a ∈ ({0, 1} : Finset (Fin 4)).filter
          (fun a => r ≠ a ∧ r ≠ a + 2), (quadAvoid2 0 L).card := by
    apply Finset.sum_congr rfl
    intro a _
    rw [quadCard_image_insert2]
    exact quadAvoid2_card_eq a 0 L
  rw [hsum2, Finset.sum_const, hcard2, Nat.nsmul_eq_mul, one_mul]

/-- `B(L+1) = T(L) + 2·A(L) + B(L)`: a `{0,2}`-avoiding set of length
`L+1` has empty last column, ends in rail `1` or `3`, or ends in the
pair `{1,3}`. -/
theorem quadAvoid2_succ_card (L : ℕ) :
    (quadAvoid2 0 (L + 1)).card =
      (quadSets L).card + 2 * (quadAvoid 0 L).card +
        (quadAvoid2 0 L).card := by
  have d_top := quad_disjoint_union_pair L
    ((Finset.univ : Finset (Fin 4)).filter
      fun c : Fin 4 => c ≠ 0 ∧ c ≠ 0 + 2)
    (({0, 1} : Finset (Fin 4)).filter fun a : Fin 4 =>
      (0 : Fin 4) ≠ a ∧ (0 : Fin 4) ≠ a + 2 ∧ (0 : Fin 4) + 2 ≠ a ∧
        (0 : Fin 4) + 2 ≠ a + 2)
  have d_AS := quad_disjoint_sets_single L
    ((Finset.univ : Finset (Fin 4)).filter
      fun c : Fin 4 => c ≠ 0 ∧ c ≠ 0 + 2)
  have pw_S := quad_single_pw L
    ((Finset.univ : Finset (Fin 4)).filter
      fun c : Fin 4 => c ≠ 0 ∧ c ≠ 0 + 2)
  have pw_P := quad_pair_pw L
    (({0, 1} : Finset (Fin 4)).filter fun a : Fin 4 =>
      (0 : Fin 4) ≠ a ∧ (0 : Fin 4) ≠ a + 2 ∧ (0 : Fin 4) + 2 ≠ a ∧
        (0 : Fin 4) + 2 ≠ a + 2) (Finset.filter_subset _ _)
  rw [quadAvoid2_zero_succ, Finset.card_union_of_disjoint d_top,
    Finset.card_union_of_disjoint d_AS, Finset.card_biUnion pw_S,
    Finset.card_biUnion pw_P]
  have hcard : ((Finset.univ : Finset (Fin 4)).filter
      fun c => c ≠ 0 ∧ c ≠ 0 + 2).card = 2 := by
    decide
  have hsum : (∑ c ∈ (Finset.univ : Finset (Fin 4)).filter
        fun c : Fin 4 => c ≠ 0 ∧ c ≠ 0 + 2,
        ((quadAvoid c L).image fun t => insert (c, L) t).card)
      = ∑ _c ∈ (Finset.univ : Finset (Fin 4)).filter
        (fun c : Fin 4 => c ≠ 0 ∧ c ≠ 0 + 2),
        (quadAvoid 0 L).card := by
    apply Finset.sum_congr rfl
    intro c _
    rw [quadCard_image_insert]
    exact quadAvoid_card_eq c 0 L
  rw [hsum, Finset.sum_const, hcard, Nat.nsmul_eq_mul]
  have hcard2 : (({0, 1} : Finset (Fin 4)).filter fun a =>
      (0 : Fin 4) ≠ a ∧ 0 ≠ a + 2 ∧ (0 : Fin 4) + 2 ≠ a ∧
        (0 : Fin 4) + 2 ≠ a + 2).card = 1 := by
    decide
  have hsum2 : (∑ a ∈ ({0, 1} : Finset (Fin 4)).filter fun a =>
        (0 : Fin 4) ≠ a ∧ 0 ≠ a + 2 ∧ (0 : Fin 4) + 2 ≠ a ∧
          (0 : Fin 4) + 2 ≠ a + 2,
        ((quadAvoid2 a L).image fun t => insert (a, L)
          (insert (a + 2, L) t)).card)
      = ∑ _a ∈ ({0, 1} : Finset (Fin 4)).filter (fun a =>
          (0 : Fin 4) ≠ a ∧ 0 ≠ a + 2 ∧ (0 : Fin 4) + 2 ≠ a ∧
            (0 : Fin 4) + 2 ≠ a + 2), (quadAvoid2 0 L).card := by
    apply Finset.sum_congr rfl
    intro a _
    rw [quadCard_image_insert2]
    exact quadAvoid2_card_eq a 0 L
  rw [hsum2, Finset.sum_const, hcard2, Nat.nsmul_eq_mul, one_mul]

theorem quadSets_zero : quadSets 0 = {∅} := by
  ext t
  rw [mem_quadSets, quadVert_zero, Finset.subset_empty,
    Finset.mem_singleton]
  refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
  subst h
  exact ⟨fun p hp => absurd hp (Finset.notMem_empty _),
    fun p hp => absurd hp (Finset.notMem_empty _)⟩

theorem quadAvoid_zero (r : Fin 4) : quadAvoid r 0 = {∅} := by
  ext t
  rw [mem_quadAvoid, quadSets_zero, Finset.mem_singleton]
  refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
  subst h
  exact Finset.notMem_empty _

theorem quadAvoid2_zero (a : Fin 4) : quadAvoid2 a 0 = {∅} := by
  ext t
  rw [mem_quadAvoid2, quadSets_zero, Finset.mem_singleton]
  refine ⟨fun h => h.1, fun h => ⟨h, ?_, ?_⟩⟩ <;>
    subst h <;> exact Finset.notMem_empty _

/-- Base count: `T(0) = 1`. -/
theorem quadSets_card_zero : (quadSets 0).card = 1 := by
  rw [quadSets_zero, Finset.card_singleton]

/-- Base count: `T(1) = 7` (the empty set, four singletons, and the two
antipodal pairs). -/
theorem quadSets_card_one : (quadSets 1).card = 7 := by
  have h : (quadSets (0 + 1)).card =
      (quadSets 0).card + 4 * (quadAvoid 0 0).card +
        2 * (quadAvoid2 0 0).card := quadSets_card_succ 0
  rw [quadSets_card_zero, quadAvoid_zero, quadAvoid2_zero,
    Finset.card_singleton] at h
  exact h

/-- Base count: `T(2) = 35`. -/
theorem quadSets_card_two : (quadSets 2).card = 35 := by
  have h2 : (quadSets (1 + 1)).card =
      (quadSets 1).card + 4 * (quadAvoid 0 1).card +
        2 * (quadAvoid2 0 1).card := quadSets_card_succ 1
  have hA : (quadAvoid 0 (0 + 1)).card =
      (quadSets 0).card + 3 * (quadAvoid 0 0).card +
        (quadAvoid2 0 0).card := quadAvoid_succ_card 0 (0 : Fin 4)
  have hB : (quadAvoid2 0 (0 + 1)).card =
      (quadSets 0).card + 2 * (quadAvoid 0 0).card +
        (quadAvoid2 0 0).card := quadAvoid2_succ_card 0
  rw [show (0 : ℕ) + 1 = 1 from rfl] at hA hB
  rw [show (1 : ℕ) + 1 = 2 from rfl] at h2
  simp only [quadSets_card_one, quadSets_card_zero, quadAvoid_zero,
    quadAvoid2_zero, Finset.card_singleton] at h2 hA hB
  omega

/-- **The two-step bound** `T(L+2) ≤ 5·T(L+1) + 2·T(L)`, obtained by
eliminating the avoiding counts (`16A + 6B ≤ 4·(4A + 2B)`). -/
theorem quadSets_card_add_two_le (L : ℕ) :
    (quadSets (L + 2)).card ≤
      5 * (quadSets (L + 1)).card + 2 * (quadSets L).card := by
  have hT1 := quadSets_card_succ L
  have hT2 := quadSets_card_succ (L + 1)
  have hA := quadAvoid_succ_card L (0 : Fin 4)
  have hB := quadAvoid2_succ_card L
  rw [show L + 1 + 1 = L + 2 from rfl] at hT2
  omega

/-- **The exact recurrence** `T(L+3) = 5·T(L+1)... `, i.e.
`T(L+3) + T(L) = 5·T(L+2) + T(L+1)`, the order-3 recurrence of the
`7`-state transfer matrix (characteristic polynomial
`λ³ = 5λ² + λ - 1`, Perron root `≈ 5.156`). -/
theorem quadSets_card_add_three (L : ℕ) :
    (quadSets (L + 3)).card + (quadSets L).card =
      5 * (quadSets (L + 2)).card + (quadSets (L + 1)).card := by
  have hT1 := quadSets_card_succ L
  have hT2 := quadSets_card_succ (L + 1)
  have hT3 := quadSets_card_succ (L + 2)
  have hA1 := quadAvoid_succ_card L (0 : Fin 4)
  have hA2 := quadAvoid_succ_card (L + 1) (0 : Fin 4)
  have hA3 := quadAvoid_succ_card (L + 2) (0 : Fin 4)
  have hB1 := quadAvoid2_succ_card L
  have hB2 := quadAvoid2_succ_card (L + 1)
  have hB3 := quadAvoid2_succ_card (L + 2)
  rw [show L + 1 + 1 = L + 2 from rfl] at hT2 hA2 hB2
  rw [show L + 2 + 1 = L + 3 from rfl] at hT3 hA3 hB3
  omega

/-- **Integer-normalised bound.**  `T(L)·2^L ≤ 2·11^L` for all `L`,
i.e. `T(L) ≤ 2·(11/2)^L`: the two-step induction gives
`T(k+2)·2^{k+2} ≤ 10·(T(k+1)·2^{k+1}) + 8·(T(k)·2^k) ≤ 20·11^{k+1} +
16·11^k = 236·11^k ≤ 242·11^k = 2·11^{k+2}`.  Per vertex this is the
rate `(11/2)^{1/4} ≈ 1.5317`, strictly below the ladder rate
`√(1 + √2) ≈ 1.5538`. -/
theorem quadSets_card_mul_two_pow_le (L : ℕ) :
    (quadSets L).card * 2 ^ L ≤ 2 * 11 ^ L := by
  induction L using Nat.twoStepInduction with
  | zero =>
      rw [quadSets_card_zero]
      norm_num
  | one =>
      rw [quadSets_card_one]
      norm_num
  | more k ih ih1 =>
      have hrec := quadSets_card_add_two_le k
      calc (quadSets (k + 2)).card * 2 ^ (k + 2)
          ≤ (5 * (quadSets (k + 1)).card + 2 * (quadSets k).card) *
              2 ^ (k + 2) := Nat.mul_le_mul hrec (le_refl _)
        _ = 10 * ((quadSets (k + 1)).card * 2 ^ (k + 1)) +
              8 * ((quadSets k).card * 2 ^ k) := by
            rw [Nat.add_mul]
            have e1 : (2 : ℕ) ^ (k + 2) = 4 * 2 ^ k := by
              rw [pow_add]; ring
            have e2 : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := pow_succ' _ _
            rw [e1, e2]
            ring
        _ ≤ 10 * (2 * 11 ^ (k + 1)) + 8 * (2 * 11 ^ k) :=
            add_le_add (Nat.mul_le_mul (le_refl 10) ih1)
              (Nat.mul_le_mul (le_refl 8) ih)
        _ = 236 * 11 ^ k := by
            rw [show (11 : ℕ) ^ (k + 1) = 11 * 11 ^ k from pow_succ' _ _]
            ring
        _ ≤ 2 * 11 ^ (k + 2) := by
            have e : (11 : ℕ) ^ (k + 2) = 121 * 11 ^ k := by
              rw [pow_add]; ring
            rw [e]
            calc 236 * 11 ^ k ≤ 242 * 11 ^ k :=
                  Nat.mul_le_mul (by norm_num) (le_refl _)
              _ = 2 * (121 * 11 ^ k) := by ring

/-- Loose corollary for later use: `T(L) ≤ 2·11^L`. -/
theorem quadSets_card_le (L : ℕ) : (quadSets L).card ≤ 2 * 11 ^ L := by
  calc (quadSets L).card
      ≤ (quadSets L).card * 2 ^ L := by
        apply Nat.le_mul_of_pos_right
        exact pow_pos (by norm_num) _
    _ ≤ 2 * 11 ^ L := quadSets_card_mul_two_pow_le L

end JSP000728
