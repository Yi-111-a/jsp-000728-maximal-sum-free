import JSPProblem.RemovalAttack
import JSPProblem.Supersat3
import Mathlib.Data.ZMod.Basic

/-!
# JSP-000728 — cover bounds and reductions for the Schur removal lemma

The Schur removal lemma (`SchurRemoval` in `Removal.lean`) is equivalent
to the Ruzsa–Szemerédi triangle removal lemma and does not yield to the
elementary hitting-set/matching proofs collected in `Supersat3.lean`.
This file proves *why* the naive approaches fail and packages the
statement in two strictly useful equivalent/sufficient forms:

* **Tops deletion** (`isSumFree_filter_no_sum`): deleting `s ∩ (s + s)`
  — every element that is the sum of two elements of `s` — always leaves
  a sum-free set.  This only gives `schurTripleCount`-many deletions in
  the worst case and is *not* strong enough: there are `s ⊆ {1,…,n}`
  with `Θ(n)` tops but deletion number `1`.

* **Matching cover** (`exists_isSumFree_sdiff_card_le_two_mul`):
  in the auxiliary bipartite graph on two copies of `s` with edges
  `x ~ z ⇔ z − x ∈ s`, the endpoints of a maximal matching cover every
  edge, hence every Schur triple, so the deletion number is at most
  `2·(matching number)`.  The corresponding hypothesis
  `SchurMatchingBound` implies `SchurRemoval`
  (`schurRemoval_of_matchingBound`) — but it is expected to be *false*:
  `s = {1} ∪ (n/2, n]` has `O(n)` triples and matching number `≈ n/4`.
  So the removal lemma genuinely requires more than matching/cover
  bounds.

* **Large-minimum reduction** (`schurRemoval_iff_minElem`):
  `SchurRemoval` is equivalent to its restriction to sets all of whose
  elements exceed `ε·n/4`: the `≤ ⌊εn/4⌋` small elements are simply
  deleted.  This is the standard "cleaning" step and reduces the problem
  to sets of *large* elements.

* **Cyclic-group reduction** (`schurRemoval_of_zmod`): if removal holds
  for `x + y = z` in `ZMod N` for all large `N`, then `SchurRemoval`
  holds — embed `s ⊆ {1,…,n}` in `ZMod (2n+1)`, where integer and
  modular triples coincide because `x + y ≤ 2n < 2n+1`.  This moves the
  problem to the setting where the Fourier-analytic / arithmetic
  regularity proofs (Green; Král–Serra–Vena) operate.

All proofs are complete; no placeholders.
-/

namespace JSP000728

/-! ## Tops deletion -/

/-- **Tops deletion.**  The elements of `s` that are *not* the top of a
Schur triple form a sum-free set: if `x, y` survive and `x + y ∈ s` then
`x + y` is a top (via `x`), contradiction.

So `s` can always be made sum-free by deleting `|s ∩ (s + s)|` elements.
This is the greedy `exists_isSumFree_sub_card_le` bound in disguise and
is *not* sufficient for the removal lemma: `s = {1} ∪ (n/2, n]` has
`≈ n/2` tops (each `z` is `1 + (z − 1)`) but deletion number `1`. -/
theorem isSumFree_filter_no_sum (s : Finset ℤ) :
    IsSumFree (s.filter fun z => ∀ x ∈ s, z - x ∉ s) := by
  intro x hx y hy hxy
  obtain ⟨hxs, -⟩ := Finset.mem_filter.mp hx
  obtain ⟨hys, -⟩ := Finset.mem_filter.mp hy
  obtain ⟨-, hbad⟩ := Finset.mem_filter.mp hxy
  exact hbad x hxs (by rwa [show x + y - x = y by ring])

/-! ## The bipartite-matching cover -/

/-- **Schur matching** of `s`: a family `M` of ordered pairs `(x, z)`
with `x, z ∈ s` and `z − x ∈ s` — each pair is the `(summand, top)`
skeleton of the Schur triple `(x, z − x, z)` — with pairwise disjoint
endpoint sets. -/
def IsSchurMatching (s : Finset ℤ) (M : Finset (ℤ × ℤ)) : Prop :=
  (∀ p ∈ M, p.1 ∈ s ∧ p.2 ∈ s ∧ p.2 - p.1 ∈ s) ∧
    ∀ p ∈ M, ∀ q ∈ M, p ≠ q →
      Disjoint ({p.1, p.2} : Finset ℤ) ({q.1, q.2} : Finset ℤ)

/-- **Deletion number ≤ `2 · matching number`.**  A maximal Schur
matching `M` of `s` has its `≤ 2|M|` endpoints covering every edge
`(x, z)` with `z − x ∈ s` — in particular the edge `(x, x + y)` of any
Schur triple — so deleting them makes `s` sum-free. -/
theorem exists_isSumFree_sdiff_card_le_two_mul (s : Finset ℤ) :
    ∃ t : Finset ℤ, t ⊆ s ∧ IsSumFree t ∧
      ∃ M : Finset (ℤ × ℤ), IsSchurMatching s M ∧
        (s \ t).card ≤ 2 * M.card := by
  classical
  set E := (s ×ˢ s).filter fun p : ℤ × ℤ => p.2 - p.1 ∈ s with hE
  set fam := E.powerset.filter fun M =>
    ∀ p ∈ M, ∀ q ∈ M, p ≠ q →
      Disjoint ({p.1, p.2} : Finset ℤ) ({q.1, q.2} : Finset ℤ) with hfam
  have hne : fam.Nonempty := by
    refine ⟨∅, ?_⟩
    rw [hfam, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.empty_subset _,
      fun p hp => (Finset.notMem_empty _ hp).elim⟩
  obtain ⟨M, hMfam, hMmax⟩ := Finset.exists_max_image fam Finset.card hne
  rw [hfam, Finset.mem_filter, Finset.mem_powerset] at hMfam
  obtain ⟨hMsub, hMdisj⟩ := hMfam
  have hMem : ∀ p ∈ M, p.1 ∈ s ∧ p.2 ∈ s ∧ p.2 - p.1 ∈ s := by
    intro p hp
    have h := Finset.mem_filter.mp (hMsub hp)
    obtain ⟨hp2, hd⟩ := h
    rw [Finset.mem_product] at hp2
    exact ⟨hp2.1, hp2.2, hd⟩
  set D := M.biUnion fun p : ℤ × ℤ => ({p.1, p.2} : Finset ℤ) with hD
  have hDsub : D ⊆ s := by
    intro a ha
    rw [hD, Finset.mem_biUnion] at ha
    obtain ⟨p, hp, hap⟩ := ha
    obtain ⟨hp1, hp2, -⟩ := hMem p hp
    rw [Finset.mem_insert, Finset.mem_singleton] at hap
    rcases hap with rfl | rfl <;> assumption
  -- Every edge meets `D`: otherwise `insert e M` is a larger disjoint
  -- family.
  have hcover : ∀ e ∈ E, e.1 ∈ D ∨ e.2 ∈ D := by
    intro e he
    by_contra hcon
    rw [not_or] at hcon
    have heM : e ∉ M := fun h =>
      hcon.1 (Finset.mem_biUnion.mpr
        ⟨e, h, Finset.mem_insert_self _ _⟩)
    have hinsert : insert e M ∈ fam := by
      rw [hfam, Finset.mem_filter, Finset.mem_powerset]
      refine ⟨Finset.insert_subset he hMsub, ?_⟩
      intro p hp q hq hne'
      rw [Finset.mem_insert] at hp hq
      rcases hp with rfl | hp <;> rcases hq with rfl | hq
      · exact absurd rfl hne'
      · -- endpoints of `e` are not in `D`, but endpoints of `q ∈ M` are.
        rw [Finset.disjoint_left]
        intro a ha hb
        have haD : a ∈ D := Finset.mem_biUnion.mpr ⟨q, hq, hb⟩
        rw [Finset.mem_insert, Finset.mem_singleton] at ha
        rcases ha with rfl | rfl
        · exact hcon.1 haD
        · exact hcon.2 haD
      · rw [Finset.disjoint_left]
        intro a ha hb
        have haD : a ∈ D := Finset.mem_biUnion.mpr ⟨p, hp, ha⟩
        rw [Finset.mem_insert, Finset.mem_singleton] at hb
        rcases hb with rfl | rfl
        · exact hcon.1 haD
        · exact hcon.2 haD
      · exact hMdisj p hp q hq hne'
    have hcard := hMmax (insert e M) hinsert
    rw [Finset.card_insert_of_notMem heM] at hcard
    omega
  refine ⟨s \ D, Finset.sdiff_subset, ?_, M, ⟨hMem, hMdisj⟩, ?_⟩
  · -- `s ∖ D` is sum-free.
    intro x hx y hy hxy
    obtain ⟨hxs, hxD⟩ := Finset.mem_sdiff.mp hx
    obtain ⟨hys, hyD⟩ := Finset.mem_sdiff.mp hy
    obtain ⟨hxys, hxyD⟩ := Finset.mem_sdiff.mp hxy
    have hedge : (x, x + y) ∈ E := by
      rw [hE, Finset.mem_filter, Finset.mem_product]
      refine ⟨⟨hxs, hxys⟩, ?_⟩
      show x + y - x ∈ s
      rw [show x + y - x = y by ring]
      exact hys
    obtain h | h := hcover _ hedge
    · exact hxD h
    · exact hxyD h
  · have hsplit : s \ (s \ D) = D := Finset.sdiff_sdiff_eq_self hDsub
    rw [hsplit]
    calc D.card ≤ ∑ p ∈ M, ({p.1, p.2} : Finset ℤ).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _p ∈ M, 2 := by
          apply Finset.sum_le_sum
          intro p _
          calc ({p.1, p.2} : Finset ℤ).card
              ≤ ({p.2} : Finset ℤ).card + 1 := Finset.card_insert_le _ _
            _ = 1 + 1 := by rw [Finset.card_singleton]
            _ = 2 := rfl
      _ = 2 * M.card := by
          rw [Finset.sum_const, smul_eq_mul, mul_comm]

/-- **Matching-number hypothesis.**  If a sparse `s ⊆ {1,…,n}` never
contains a Schur matching of size `ε·n`, removal follows — a maximal
matching's `2|M|` endpoints cover all triples.  Note this hypothesis is
genuinely stronger than needed: it is expected to fail for
`s = {1} ∪ (n/2, n]` (matching `≈ n/4`, `O(n)` triples), so the vertex
cover of a sparse Schur hypergraph is *not* controlled by its matching
number. -/
def SchurMatchingBound : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n : ℕ in Filter.atTop,
    ∀ s : Finset ℤ, s ⊆ interval n →
      (schurTripleCount s : ℝ) ≤ δ * (n : ℝ) ^ 2 →
      ∀ M : Finset (ℤ × ℤ), IsSchurMatching s M →
        (M.card : ℝ) ≤ ε * (n : ℝ)

/-- **Matching bound ⇒ removal.** -/
theorem schurRemoval_of_matchingBound (h : SchurMatchingBound) :
    SchurRemoval := by
  intro ε hε
  obtain ⟨δ, hδ, hrem⟩ := h (ε / 2) (by linarith)
  refine ⟨δ, hδ, ?_⟩
  filter_upwards [hrem] with n hremn s hs htri
  obtain ⟨t, hts, htf, M, hM, hdel⟩ := exists_isSumFree_sdiff_card_le_two_mul s
  refine ⟨t, hts, htf, ?_⟩
  have hMbound := hremn s hs htri M hM
  calc ((s \ t).card : ℝ)
      ≤ 2 * (M.card : ℝ) := by exact_mod_cast hdel
    _ ≤ 2 * (ε / 2 * (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hMbound (by norm_num)
    _ = ε * (n : ℝ) := by ring

/-! ## Reduction to sets of large elements -/

/-- **Large-minimum form of removal**: same conclusion as `SchurRemoval`
but only for sets all of whose elements exceed `ε/2 · n`.  It is
equivalent to `SchurRemoval` (`schurRemoval_iff_minElem`): the `≤ εn/4`
small elements are deleted outright, so WLOG every element of `s` is
large.  This is the standard "cleaning" step; it reduces the problem to
the genuinely hard regime `s ⊆ (εn, n]`. -/
def SchurRemovalMinElem : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n : ℕ in Filter.atTop,
    ∀ s : Finset ℤ, s ⊆ interval n →
      (∀ x ∈ s, ε / 2 * (n : ℝ) < (x : ℝ)) →
      (schurTripleCount s : ℝ) ≤ δ * (n : ℝ) ^ 2 →
      ∃ t : Finset ℤ, t ⊆ s ∧ IsSumFree t ∧ ((s \ t).card : ℝ) ≤ ε * (n : ℝ)

/-- The large-minimum form implies full removal: delete the at most
`⌊εn/4⌋` elements below `εn/4`, then apply the hypothesis at parameter
`ε/2` to the rest. -/
theorem schurRemoval_of_minElem (h : SchurRemovalMinElem) : SchurRemoval := by
  classical
  intro ε hε
  obtain ⟨δ, hδ, hrem⟩ := h (ε / 2) (by linarith)
  refine ⟨δ, hδ, ?_⟩
  filter_upwards [hrem, Filter.eventually_ge_atTop 1] with n hremn hn
  intro s hs htri
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  set s' := s.filter fun (x : ℤ) => ε / 4 * (n : ℝ) < (x : ℝ) with hs'
  set slow := s.filter fun (x : ℤ) => (x : ℝ) ≤ ε / 4 * (n : ℝ) with hlow
  -- `slow ⊆ Icc 1 ⌊εn/4⌋`, hence `|slow| ≤ εn/4`.
  have hlowcard : (slow.card : ℝ) ≤ ε / 4 * (n : ℝ) := by
    have hsub : slow ⊆ Finset.Icc (1 : ℤ) ⌊ε / 4 * (n : ℝ)⌋ := by
      intro x hx
      rw [hlow, Finset.mem_filter] at hx
      obtain ⟨hxs, hxle⟩ := hx
      have hx1 := (Finset.mem_Icc.mp (hs hxs)).1
      rw [Finset.mem_Icc]
      exact ⟨hx1, Int.le_floor.mpr hxle⟩
    have h1 := Finset.card_le_card hsub
    rw [Int.card_Icc] at h1
    have hfloor : (0 : ℤ) ≤ ⌊ε / 4 * (n : ℝ)⌋ :=
      Int.floor_nonneg.mpr (mul_nonneg (by linarith) hnR.le)
    have hsimp : (⌊ε / 4 * (n : ℝ)⌋ + 1 - 1).toNat
        = (⌊ε / 4 * (n : ℝ)⌋).toNat := by
      congr 1; omega
    have h2 : ((⌊ε / 4 * (n : ℝ)⌋).toNat : ℝ) ≤ ε / 4 * (n : ℝ) := by
      have e : ((⌊ε / 4 * (n : ℝ)⌋).toNat : ℝ)
          = (⌊ε / 4 * (n : ℝ)⌋ : ℤ) := by
        exact_mod_cast Int.toNat_of_nonneg hfloor
      rw [e]
      exact Int.floor_le _
    rw [hsimp] at h1
    have h3 : (slow.card : ℝ) ≤ ((⌊ε / 4 * (n : ℝ)⌋).toNat : ℝ) := by
      exact_mod_cast h1
    exact h3.trans h2
  -- The large part `s'` satisfies the hypotheses at parameter `ε/2`.
  have hs'sub : s' ⊆ interval n := (Finset.filter_subset _ _).trans hs
  have hs'min : ∀ x ∈ s', ε / 2 / 2 * (n : ℝ) < (x : ℝ) := by
    intro x hx
    rw [hs', Finset.mem_filter] at hx
    have : ε / 2 / 2 = ε / 4 := by ring
    rw [this]
    exact hx.2
  have hs'tri : (schurTripleCount s' : ℝ) ≤ δ * (n : ℝ) ^ 2 :=
    (Nat.cast_le.mpr (schurTripleCount_mono (Finset.filter_subset _ _))).trans
      htri
  obtain ⟨t, hts', htf, htdel⟩ := hremn s' hs'sub hs'min hs'tri
  refine ⟨t, hts'.trans (Finset.filter_subset _ _), htf, ?_⟩
  -- `s ∖ t ⊆ slow ∪ (s' ∖ t)`.
  have hsplit : s \ t ⊆ slow ∪ (s' \ t) := by
    intro x hx
    obtain ⟨hxs, hxt⟩ := Finset.mem_sdiff.mp hx
    rw [Finset.mem_union]
    by_cases hxl : (x : ℝ) ≤ ε / 4 * (n : ℝ)
    · exact Or.inl (Finset.mem_filter.mpr ⟨hxs, hxl⟩)
    · exact Or.inr (Finset.mem_sdiff.mpr
        ⟨Finset.mem_filter.mpr ⟨hxs, by linarith⟩, hxt⟩)
  have hcard : ((s \ t).card : ℝ)
      ≤ (slow.card : ℝ) + ((s' \ t).card : ℝ) := by
    have h := (Finset.card_le_card hsplit).trans (Finset.card_union_le _ _)
    exact_mod_cast h
  linarith [hcard, hlowcard, htdel]

/-- The trivial direction: full removal implies its large-minimum
restriction. -/
theorem schurRemovalMinElem_of_schurRemoval (h : SchurRemoval) :
    SchurRemovalMinElem := by
  intro ε hε
  obtain ⟨δ, hδ, hrem⟩ := h ε hε
  refine ⟨δ, hδ, ?_⟩
  filter_upwards [hrem] with n hremn s hs _ htri
  exact hremn s hs htri

/-- `SchurRemoval` is equivalent to its restriction to sets of large
elements. -/
theorem schurRemoval_iff_minElem : SchurRemoval ↔ SchurRemovalMinElem :=
  ⟨schurRemovalMinElem_of_schurRemoval, schurRemoval_of_minElem⟩

/-! ## Reduction to `ZMod N` -/

/-- Sum-freeness inside `ZMod N`. -/
def zmodIsSumFree {N : ℕ} (s : Finset (ZMod N)) : Prop :=
  ∀ x ∈ s, ∀ y ∈ s, x + y ∉ s

/-- The Schur triples of a subset of `ZMod N`. -/
def zmodSchurTriples {N : ℕ} (s : Finset (ZMod N)) :
    Finset (ZMod N × ZMod N × ZMod N) :=
  (s ×ˢ (s ×ˢ s)).filter fun t => t.1 + t.2.1 = t.2.2

/-- The number of Schur triples of a subset of `ZMod N`. -/
def zmodSchurTripleCount {N : ℕ} (s : Finset (ZMod N)) : ℕ :=
  (zmodSchurTriples s).card

/-- The removal lemma inside `ZMod N`, required to hold for all
sufficiently large `N`.  This is the finite-group formulation used by the
Fourier-analytic proofs of the removal lemma (Green; Král'–Serra–Vena). -/
def SchurRemovalZMod : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ N : ℕ in Filter.atTop,
    ∀ s : Finset (ZMod N),
      (zmodSchurTripleCount s : ℝ) ≤ δ * (N : ℝ) ^ 2 →
      ∃ t : Finset (ZMod N), t ⊆ s ∧ zmodIsSumFree t ∧
        ((s \ t).card : ℝ) ≤ ε * (N : ℝ)

/-- The cast `ℤ → ZMod N` is injective on any finset of integers lying
in `[0, N)`. -/
theorem injOn_intCast_zmod {N : ℕ} {s : Finset ℤ}
    (h : ∀ x ∈ s, 0 ≤ x ∧ x < (N : ℤ)) :
    Set.InjOn (fun x : ℤ => (x : ZMod N)) s := by
  intro a ha b hb hab
  obtain ⟨ha0, haN⟩ := h a ha
  obtain ⟨hb0, hbN⟩ := h b hb
  have he : a % (N : ℤ) = b % (N : ℤ) :=
    (ZMod.intCast_eq_intCast_iff' a b N).mp hab
  rwa [Int.emod_eq_of_lt ha0 haN, Int.emod_eq_of_lt hb0 hbN] at he

/-- For `s ⊆ [0, n]` and `2n < N`, every Schur triple of the image of `s`
in `ZMod N` is the image of an integer Schur triple of `s`.  Hence the
modular triple count is at most the integer one. -/
theorem zmodSchurTripleCount_image_le {N n : ℕ} {s : Finset ℤ}
    (hs : ∀ x ∈ s, 0 ≤ x ∧ x ≤ (n : ℤ)) (hN : 2 * n < N) :
    zmodSchurTripleCount (s.image fun x : ℤ => (x : ZMod N)) ≤
      schurTripleCount s := by
  classical
  have hsub :
      zmodSchurTriples (s.image fun x : ℤ => (x : ZMod N)) ⊆
        (schurTriples s).image fun p : ℤ × ℤ × ℤ =>
          ((p.1 : ZMod N), (p.2.1 : ZMod N), (p.2.2 : ZMod N)) := by
    intro q hq
    obtain ⟨q1, q2, q3⟩ := q
    rw [zmodSchurTriples, Finset.mem_filter] at hq
    obtain ⟨hmem, hqeq⟩ := hq
    rw [Finset.mem_product, Finset.mem_product] at hmem
    obtain ⟨hq1, hq2, hq3⟩ := hmem
    obtain ⟨x, hxs, hqx⟩ := Finset.mem_image.mp hq1
    obtain ⟨y, hys, hqy⟩ := Finset.mem_image.mp hq2
    obtain ⟨z, hzs, hqz⟩ := Finset.mem_image.mp hq3
    -- The modular equation `x + y ≡ z (mod N)` is in fact an integer
    -- equality because both sides lie in `[0, N)`.
    have hxyz : x + y = z := by
      have hcast : ((x + y : ℤ) : ZMod N) = (z : ZMod N) := by
        rw [Int.cast_add, hqx, hqy, hqz]
        exact hqeq
      have he : (x + y) % (N : ℤ) = z % (N : ℤ) :=
        (ZMod.intCast_eq_intCast_iff' _ _ _).mp hcast
      obtain ⟨hx0, hxn⟩ := hs x hxs
      obtain ⟨hy0, hyn⟩ := hs y hys
      obtain ⟨hz0, hzn⟩ := hs z hzs
      have he2 : (x + y) % (N : ℤ) = x + y :=
        Int.emod_eq_of_lt (by omega) (by omega)
      have he3 : z % (N : ℤ) = z := Int.emod_eq_of_lt hz0 (by omega)
      omega
    refine Finset.mem_image.mpr ⟨(x, (y, z)), ?_, ?_⟩
    · rw [schurTriples, Finset.mem_filter, Finset.mem_product,
        Finset.mem_product]
      exact ⟨⟨hxs, hys, hzs⟩, hxyz⟩
    · show ((x : ZMod N), (y : ZMod N), (z : ZMod N)) = (q1, q2, q3)
      exact Prod.ext_iff.mpr ⟨hqx, Prod.ext_iff.mpr ⟨hqy, hqz⟩⟩
  calc zmodSchurTripleCount (s.image fun x : ℤ => (x : ZMod N))
      = (zmodSchurTriples
          (s.image fun x : ℤ => (x : ZMod N))).card := rfl
    _ ≤ ((schurTriples s).image fun p : ℤ × ℤ × ℤ =>
          ((p.1 : ZMod N), (p.2.1 : ZMod N), (p.2.2 : ZMod N))).card :=
        Finset.card_le_card hsub
    _ ≤ (schurTriples s).card := Finset.card_image_le
    _ = schurTripleCount s := rfl

/-- **Reduction to the cyclic group.**  If the removal lemma holds in
`ZMod N` for all large `N`, then it holds in `{1,…,n}`: embed
`s ⊆ {1,…,n}` in `ZMod (2n+1)`, where integer and modular Schur triples
coincide because `x + y ≤ 2n < 2n+1`. -/
theorem schurRemoval_of_zmod (h : SchurRemovalZMod) : SchurRemoval := by
  classical
  intro ε hε
  obtain ⟨δ, hδ, hrem⟩ := h (ε / 4) (by linarith)
  refine ⟨4 * δ, by linarith, ?_⟩
  have htend : Filter.Tendsto (fun n : ℕ => 2 * n + 1) Filter.atTop
      Filter.atTop :=
    Filter.tendsto_atTop_atTop.mpr fun b => ⟨b, fun a ha => by omega⟩
  filter_upwards [htend.eventually hrem, Filter.eventually_ge_atTop 1]
    with n hremn hn
  intro s hs htri
  set N := 2 * n + 1 with hN
  have hrange : ∀ x ∈ s, 0 ≤ x ∧ x ≤ (n : ℤ) := by
    intro x hx
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp (hs hx)
    exact ⟨by omega, h2⟩
  have hinj : Set.InjOn (fun x : ℤ => (x : ZMod N)) s := by
    apply injOn_intCast_zmod
    intro x hx
    obtain ⟨hx0, hxn⟩ := hrange x hx
    refine ⟨hx0, ?_⟩
    have hN' : ((N : ℕ) : ℤ) = 2 * (n : ℤ) + 1 := by
      rw [hN]; push_cast; ring
    omega
  have hcount : zmodSchurTripleCount
      (s.image fun x : ℤ => (x : ZMod N)) ≤ schurTripleCount s :=
    zmodSchurTripleCount_image_le hrange (by omega)
  have hNR : ((N : ℕ) : ℝ) = 2 * (n : ℝ) + 1 := by
    rw [hN]; push_cast; ring
  obtain ⟨t', _hts', ht'f, ht'del⟩ :=
    hremn (s.image fun x : ℤ => (x : ZMod N)) (by
      calc (zmodSchurTripleCount
              (s.image fun x : ℤ => (x : ZMod N)) : ℝ)
          ≤ (schurTripleCount s : ℝ) := by exact_mod_cast hcount
        _ ≤ 4 * δ * (n : ℝ) ^ 2 := htri
        _ ≤ δ * ((N : ℕ) : ℝ) ^ 2 := by
            rw [hNR]
            nlinarith [mul_nonneg hδ.le
              (show (0 : ℝ) ≤ 4 * (n : ℝ) + 1 by positivity)])
  set t := s.filter fun x : ℤ => (x : ZMod N) ∈ t' with ht
  refine ⟨t, Finset.filter_subset _ _, ?_, ?_⟩
  · -- `t` is sum-free: a Schur triple in `t` would give one in `t'`.
    intro x hx y hy hxy
    obtain ⟨-, hxt'⟩ := Finset.mem_filter.mp hx
    obtain ⟨-, hyt'⟩ := Finset.mem_filter.mp hy
    obtain ⟨-, hxyt'⟩ := Finset.mem_filter.mp hxy
    have hcast : ((x + y : ℤ) : ZMod N) = (x : ZMod N) + (y : ZMod N) :=
      Int.cast_add _ _
    exact ht'f _ hxt' _ hyt' (hcast ▸ hxyt')
  · -- `s \ t` and `s' \ t'` are in bijection via the injective cast.
    have hinj' : Set.InjOn (fun x : ℤ => (x : ZMod N)) ↑(s \ t) :=
      hinj.mono fun x hx => Finset.sdiff_subset (Finset.mem_coe.mp hx)
    have him : s.image (fun x : ℤ => (x : ZMod N)) \ t' =
        (s \ t).image fun x : ℤ => (x : ZMod N) := by
      ext a
      simp only [Finset.mem_sdiff, Finset.mem_image]
      constructor
      · rintro ⟨ha', hat'⟩
        obtain ⟨x, hxs, rfl⟩ := ha'
        exact ⟨x, ⟨hxs, fun hxt =>
          hat' (Finset.mem_filter.mp hxt).2⟩, rfl⟩
      · rintro ⟨x, ⟨hxs, hxt⟩, rfl⟩
        exact ⟨⟨x, hxs, rfl⟩,
          fun ha => hxt (Finset.mem_filter.mpr ⟨hxs, ha⟩)⟩
    have hcard : (s \ t).card =
        (s.image (fun x : ℤ => (x : ZMod N)) \ t').card := by
      rw [him, Finset.card_image_of_injOn hinj']
    calc ((s \ t).card : ℝ)
        = ((s.image (fun x : ℤ => (x : ZMod N)) \ t').card : ℝ) := by
          exact_mod_cast hcard
      _ ≤ ε / 4 * ((N : ℕ) : ℝ) := ht'del
      _ ≤ ε * (n : ℝ) := by
          rw [hNR]
          have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
          have h2 := mul_le_mul_of_nonneg_left h1 hε.le
          linarith

end JSP000728
