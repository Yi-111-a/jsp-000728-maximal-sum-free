import JSPProblem.RemovalFull
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Tactic

/-!
# JSP-000728 — the Schur removal lemma in `ZMod N`

Proof of `SchurRemovalZMod` via Mathlib's triangle removal lemma
(`SimpleGraph.triangle_removal`), applied to the standard tripartite
"difference graph" on `ZMod N × Fin 3`: parts `0, 1, 2`, with `u ~ v`
iff they lie in different parts and the oriented difference `v.1 - u.1`
(for `u.2 < v.2`) belongs to `s`.  Triangles of this graph are in
bijection with `ZMod N × zmodSchurTriples s`, and the `N` triangles
over one Schur triple are pairwise edge-disjoint, so the triangle
removal lemma yields a small set of "marked" elements of `s` whose
deletion makes `s` sum-free.
-/

namespace JSP000728

open Finset SimpleGraph

/-- Vertex type of the tripartite difference graph: three copies of
`ZMod N`, indexed by `Fin 3`. -/
abbrev TripVert (N : ℕ) := ZMod N × Fin 3

/-- Adjacency in the tripartite difference graph of `s`: `u ~ v` iff
`u, v` lie in different parts and the oriented difference (from the
lower part to the higher part) belongs to `s`. -/
def tripAdj (s : Finset (ZMod N)) (u v : TripVert N) : Prop :=
  (u.2 < v.2 ∧ v.1 - u.1 ∈ s) ∨ (v.2 < u.2 ∧ u.1 - v.1 ∈ s)

theorem tripAdj_symm (s : Finset (ZMod N)) : Std.Symm (tripAdj s) :=
  ⟨fun {_ _} h => h.symm⟩

theorem tripAdj_irrefl (s : Finset (ZMod N)) : Std.Irrefl (tripAdj s) := by
  refine ⟨fun u h => ?_⟩
  rcases h with ⟨h1, _⟩ | ⟨h1, _⟩ <;> exact lt_irrefl _ h1

/-- The tripartite difference graph on `ZMod N × Fin 3` attached to
`s ⊆ ZMod N`. -/
def tripGraph (s : Finset (ZMod N)) : SimpleGraph (TripVert N) where
  Adj := tripAdj s
  symm := tripAdj_symm s
  loopless := tripAdj_irrefl s

instance (s : Finset (ZMod N)) : DecidableRel (tripGraph s).Adj :=
  fun u v => inferInstanceAs
    (Decidable ((u.2 < v.2 ∧ v.1 - u.1 ∈ s) ∨ (v.2 < u.2 ∧ u.1 - v.1 ∈ s)))

theorem tripGraph_adj {N : ℕ} {s : Finset (ZMod N)} {u v : TripVert N} :
    (tripGraph s).Adj u v ↔
      (u.2 < v.2 ∧ v.1 - u.1 ∈ s) ∨ (v.2 < u.2 ∧ u.1 - v.1 ∈ s) :=
  Iff.rfl

/-- Adjacent vertices lie in different parts. -/
theorem tripGraph_adj_snd_ne {N : ℕ} {s : Finset (ZMod N)} {u v : TripVert N}
    (h : (tripGraph s).Adj u v) : u.2 ≠ v.2 := by
  intro he
  rcases h with ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega

/-- The forward adjacency: if `u.2 < v.2`, then `u ~ v` iff
`v.1 - u.1 ∈ s`. -/
theorem tripGraph_adj_of_lt {N : ℕ} {s : Finset (ZMod N)} {u v : TripVert N}
    (h : u.2 < v.2) : (tripGraph s).Adj u v ↔ v.1 - u.1 ∈ s := by
  constructor
  · rintro (⟨_, hx⟩ | ⟨hv, -⟩)
    · exact hx
    · exact absurd h (not_lt.mpr hv.le)
  · exact fun hx => Or.inl ⟨h, hx⟩

/-- Forward edges exist whenever the difference is in `s`. -/
theorem tripGraph_adj_mk {N : ℕ} {s : Finset (ZMod N)} {a d : ZMod N}
    {i j : Fin 3} (hij : i < j) (hd : d ∈ s) :
    (tripGraph s).Adj (a, i) (a + d, j) := by
  rw [tripGraph_adj_of_lt hij]
  simpa using hd

/-! ## The triangle count -/

/-- The triangle in `TripVert N` built from basepoint `a` and
differences `x` (between parts `0` and `1`) and `z` (between parts `0`
and `2`). -/
def zmodTriVerts (a x z : ZMod N) : Finset (TripVert N) :=
  {(a, 0), (a + x, 1), (a + z, 2)}

theorem mem_zmodTriVerts {N : ℕ} {a x z : ZMod N} {u : TripVert N} :
    u ∈ zmodTriVerts a x z ↔ u = (a, 0) ∨ u = (a + x, 1) ∨ u = (a + z, 2) := by
  simp [zmodTriVerts]

/-- Every triangle of the difference graph has one vertex in each part
and is of the form `zmodTriVerts a x z` with `x, z - x, z ∈ s`. -/
theorem zmodTriVerts_mem_cliqueFinset {N : ℕ} [NeZero N] {s : Finset (ZMod N)}
    {a x y z : ZMod N} (hx : x ∈ s) (hy : y ∈ s) (hz : z ∈ s)
    (hxyz : x + y = z) :
    zmodTriVerts a x z ∈ (tripGraph s).cliqueFinset 3 := by
  rw [mem_cliqueFinset_iff]
  unfold zmodTriVerts
  rw [is3Clique_triple_iff]
  refine ⟨tripGraph_adj_mk (by decide) hx,
          tripGraph_adj_mk (by decide) hz, ?_⟩
  have h : (tripGraph s).Adj (a + x, 1) (a + x + y, 2) :=
    tripGraph_adj_mk (by decide) hy
  rwa [show a + x + y = a + z by rw [add_assoc, hxyz]] at h

/-- On `ZMod N × zmodSchurTriples s` the triangle map is injective:
the triangle determines `a, x, z`, and `y = z - x`. -/
theorem zmodTriVerts_injOn {N : ℕ} [NeZero N] (s : Finset (ZMod N)) :
    Set.InjOn
      (fun p : ZMod N × (ZMod N × ZMod N × ZMod N) =>
        zmodTriVerts p.1 p.2.1 p.2.2.2)
      ↑((univ : Finset (ZMod N)) ×ˢ zmodSchurTriples s) := by
  rintro ⟨a, x, y, z⟩ hp ⟨a', x', y', z'⟩ hp' h
  rw [mem_coe, mem_product] at hp hp'
  simp only [zmodSchurTriples, mem_filter, mem_product] at hp hp'
  obtain ⟨_, ⟨⟨-, -, -⟩, hxyz⟩⟩ := hp
  obtain ⟨_, ⟨⟨-, -, -⟩, hxyz'⟩⟩ := hp'
  have h' : zmodTriVerts a x z = zmodTriVerts a' x' z' := h
  have h0 : ((a, 0) : TripVert N) ∈ zmodTriVerts a' x' z' := by
    rw [← h']; simp [zmodTriVerts]
  have h1 : ((a + x, 1) : TripVert N) ∈ zmodTriVerts a' x' z' := by
    rw [← h']; simp [zmodTriVerts]
  have h2 : ((a + z, 2) : TripVert N) ∈ zmodTriVerts a' x' z' := by
    rw [← h']; simp [zmodTriVerts]
  simp only [mem_zmodTriVerts] at h0 h1 h2
  have ha : a = a' := by
    rcases h0 with h | h | h
    · exact congrArg Prod.fst h
    · simp at h
    · simp at h
  have hx : x = x' := by
    rcases h1 with h | h | h
    · simp at h
    · have e := congrArg Prod.fst h
      rw [ha] at e
      exact add_left_cancel e
    · simp at h
  have hz : z = z' := by
    rcases h2 with h | h | h
    · simp at h
    · simp at h
    · have e := congrArg Prod.fst h
      rw [ha] at e
      exact add_left_cancel e
  have hy : y = y' := by
    have e1 : y = z - x := by rw [← hxyz]; abel
    rw [e1, hz, hx, ← hxyz', add_sub_cancel_left]
  simp [ha, hx, hy, hz]

/-- The triangles of the difference graph are exactly the images of
`ZMod N × zmodSchurTriples s`. -/
theorem tripGraph_cliqueFinset_eq {N : ℕ} [NeZero N] (s : Finset (ZMod N)) :
    (tripGraph s).cliqueFinset 3 =
      ((univ : Finset (ZMod N)) ×ˢ zmodSchurTriples s).image
        (fun p : ZMod N × (ZMod N × ZMod N × ZMod N) =>
          zmodTriVerts p.1 p.2.1 p.2.2.2) := by
  classical
  ext c
  simp only [mem_cliqueFinset_iff, mem_image, mem_product]
  constructor
  · intro hc
    obtain ⟨hcl, hcard⟩ := hc
    -- The second coordinate is injective on the clique.
    have hsnd : ∀ p ∈ c, ∀ q ∈ c, p.2 = q.2 → p = q := by
      intro p hp q hq he
      by_contra hne
      exact tripGraph_adj_snd_ne (hcl (mem_coe.mpr hp) (mem_coe.mpr hq) hne) he
    have hinj2 : Set.InjOn Prod.snd ↑c :=
      fun p hp q hq he => hsnd p (mem_coe.mp hp) q (mem_coe.mp hq) he
    -- Hence every part `i` is represented.
    have hex : ∀ i : Fin 3, ∃ p, p ∈ c ∧ p.2 = i := by
      intro i
      have himg : c.image Prod.snd = univ := by
        apply Finset.eq_univ_of_card
        rw [card_image_of_injOn hinj2, hcard, Fintype.card_fin]
      have : i ∈ c.image Prod.snd := by rw [himg]; exact mem_univ i
      obtain ⟨p, hp, hpe⟩ := mem_image.mp this
      exact ⟨p, hp, hpe⟩
    obtain ⟨v0, hv0c, hv0⟩ := hex 0
    obtain ⟨v1, hv1c, hv1⟩ := hex 1
    obtain ⟨v2, hv2c, hv2⟩ := hex 2
    have h01 : v0 ≠ v1 := fun h => by
      have := congrArg Prod.snd h; rw [hv0, hv1] at this; exact absurd this (by decide)
    have h02 : v0 ≠ v2 := fun h => by
      have := congrArg Prod.snd h; rw [hv0, hv2] at this; exact absurd this (by decide)
    have h12 : v1 ≠ v2 := fun h => by
      have := congrArg Prod.snd h; rw [hv1, hv2] at this; exact absurd this (by decide)
    -- `c = {v0, v1, v2}` by cardinality.
    have hsub : ({v0, v1, v2} : Finset (TripVert N)) ⊆ c := by
      intro u hu
      simp only [mem_insert, mem_singleton] at hu
      rcases hu with rfl | rfl | rfl <;> assumption
    have hc3 : ({v0, v1, v2} : Finset (TripVert N)).card = 3 := by
      rw [card_insert_of_notMem (by simp [h01, h02]), card_insert_of_notMem (by simp [h12]),
        card_singleton]
    have hceq : c = {v0, v1, v2} :=
      (Finset.eq_of_subset_of_card_le hsub (le_of_eq (by rw [hcard, hc3]))).symm
    -- The three relevant adjacencies.
    have hadj01 : (tripGraph s).Adj v0 v1 := hcl (mem_coe.mpr hv0c) (mem_coe.mpr hv1c) h01
    have hadj02 : (tripGraph s).Adj v0 v2 := hcl (mem_coe.mpr hv0c) (mem_coe.mpr hv2c) h02
    have hadj12 : (tripGraph s).Adj v1 v2 := hcl (mem_coe.mpr hv1c) (mem_coe.mpr hv2c) h12
    have hx : v1.1 - v0.1 ∈ s :=
      (tripGraph_adj_of_lt (by rw [hv0, hv1]; decide : v0.2 < v1.2)).mp hadj01
    have hy : v2.1 - v1.1 ∈ s :=
      (tripGraph_adj_of_lt (by rw [hv1, hv2]; decide : v1.2 < v2.2)).mp hadj12
    have hz : v2.1 - v0.1 ∈ s :=
      (tripGraph_adj_of_lt (by rw [hv0, hv2]; decide : v0.2 < v2.2)).mp hadj02
    have hxyz : v1.1 - v0.1 + (v2.1 - v1.1) = v2.1 - v0.1 := by abel
    refine ⟨(v0.1, (v1.1 - v0.1, v2.1 - v1.1, v2.1 - v0.1)), ?_, ?_⟩
    · refine ⟨mem_univ _, ?_⟩
      simp only [zmodSchurTriples, mem_filter, mem_product]
      exact ⟨⟨hx, hy, hz⟩, hxyz⟩
    · -- `c = zmodTriVerts v0.1 (v1.1 - v0.1) (v2.1 - v0.1)`.
      have e0 : (v0.1, (0 : Fin 3)) = v0 := by rw [← hv0]
      have e1 : (v0.1 + (v1.1 - v0.1), (1 : Fin 3)) = v1 := by
        rw [show v0.1 + (v1.1 - v0.1) = v1.1 by abel, ← hv1]
      have e2 : (v0.1 + (v2.1 - v0.1), (2 : Fin 3)) = v2 := by
        rw [show v0.1 + (v2.1 - v0.1) = v2.1 by abel, ← hv2]
      rw [hceq]
      unfold zmodTriVerts
      rw [e0, e1, e2]
  · rintro ⟨⟨a, x, y, z⟩, ⟨-, ht⟩, rfl⟩
    simp only [zmodSchurTriples, mem_filter, mem_product] at ht
    obtain ⟨⟨hx, hy, hz⟩, hxyz⟩ := ht
    exact mem_cliqueFinset_iff.1 (zmodTriVerts_mem_cliqueFinset hx hy hz hxyz)

/-- There are exactly `N * zmodSchurTripleCount s` triangles. -/
theorem tripGraph_cliqueFinset_card {N : ℕ} [NeZero N] (s : Finset (ZMod N)) :
    ((tripGraph s).cliqueFinset 3).card = N * zmodSchurTripleCount s := by
  classical
  rw [tripGraph_cliqueFinset_eq, card_image_of_injOn (zmodTriVerts_injOn s),
    card_product, card_univ, ZMod.card]
  rfl

/-! ## Edge labels -/

/-- The `N` edges between parts `i` and `j` labelled by difference `d`:
for each `a`, the edge `{(a,i), (a+d,j)}`. -/
def lblEdges (N : ℕ) [NeZero N] (i j : Fin 3) (d : ZMod N) :
    Finset (Sym2 (TripVert N)) :=
  (univ : Finset (ZMod N)).image fun a => s((a, i), (a + d, j))

theorem mem_lblEdges {N : ℕ} [NeZero N] {i j : Fin 3} {d : ZMod N}
    {e : Sym2 (TripVert N)} :
    e ∈ lblEdges N i j d ↔ ∃ a : ZMod N, s((a, i), (a + d, j)) = e := by
  simp [lblEdges]

/-- Equality of two labelled edges (with both part-indices increasing)
forces equality of all data. -/
theorem lblEdges_mk_eq {N : ℕ} [NeZero N] {i j i' j' : Fin 3} {a d a' d' : ZMod N}
    (hij : i < j) (hi'j' : i' < j')
    (h : (s((a, i), (a + d, j)) : Sym2 (TripVert N)) =
      s((a', i'), (a' + d', j'))) :
    a = a' ∧ i = i' ∧ j = j' ∧ d = d' := by
  rw [Sym2.eq_iff] at h
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hi : i = i' := congrArg Prod.snd h1
    have hj : j = j' := congrArg Prod.snd h2
    have ha : a = a' := congrArg Prod.fst h1
    have hd : d = d' := by
      have e := congrArg Prod.fst h2
      rw [ha] at e
      exact add_left_cancel e
    exact ⟨ha, hi, hj, hd⟩
  · have hi : i = j' := congrArg Prod.snd h1
    have hj : j = i' := congrArg Prod.snd h2
    omega

theorem lblEdges_card {N : ℕ} [NeZero N] {i j : Fin 3} (hij : i < j)
    (d : ZMod N) :
    (lblEdges N i j d).card = N := by
  unfold lblEdges
  rw [card_image_of_injective _ (fun a a' h => (lblEdges_mk_eq hij hij h).1),
    card_univ, ZMod.card]

theorem lblEdges_subset_edgeFinset {N : ℕ} [NeZero N] {s : Finset (ZMod N)}
    {i j : Fin 3} (hij : i < j) {d : ZMod N} (hd : d ∈ s) :
    lblEdges N i j d ⊆ (tripGraph s).edgeFinset := by
  intro e he
  rw [mem_lblEdges] at he
  obtain ⟨a, rfl⟩ := he
  rw [mem_edgeFinset, mem_edgeSet]
  exact tripGraph_adj_mk hij hd

/-- Labelled edge sets for distinct part-pairs are disjoint. -/
theorem disjoint_lblEdges {N : ℕ} [NeZero N] {i j i' j' : Fin 3} {d d' : ZMod N}
    (hij : i < j) (hi'j' : i' < j') (hne : (i, j) ≠ (i', j')) :
    Disjoint (lblEdges N i j d) (lblEdges N i' j' d') := by
  rw [Finset.disjoint_left]
  intro e he he'
  rw [mem_lblEdges] at he he'
  obtain ⟨a, rfl⟩ := he
  obtain ⟨a', h⟩ := he'
  obtain ⟨-, hi, hj, -⟩ := lblEdges_mk_eq hi'j' hij h
  exact hne (Prod.ext_iff.mpr ⟨hi.symm, hj.symm⟩)

/-- Labelled edge sets for the same part-pair but distinct labels are
disjoint. -/
theorem disjoint_lblEdges_label {N : ℕ} [NeZero N] {i j : Fin 3} {d d' : ZMod N}
    (hij : i < j) (hne : d ≠ d') :
    Disjoint (lblEdges N i j d) (lblEdges N i j d') := by
  rw [Finset.disjoint_left]
  intro e he he'
  rw [mem_lblEdges] at he he'
  obtain ⟨a, rfl⟩ := he
  obtain ⟨a', h⟩ := he'
  obtain ⟨-, -, -, hd⟩ := lblEdges_mk_eq hij hij h
  exact hne hd.symm

/-- All edges labelled by `x`: the three part-pairs `0–1`, `1–2`,
`0–2`. -/
def lblSet (N : ℕ) [NeZero N] (x : ZMod N) : Finset (Sym2 (TripVert N)) :=
  lblEdges N 0 1 x ∪ (lblEdges N 1 2 x ∪ lblEdges N 0 2 x)

theorem mem_lblSet {N : ℕ} [NeZero N] {x : ZMod N} {e : Sym2 (TripVert N)} :
    e ∈ lblSet N x ↔
      e ∈ lblEdges N 0 1 x ∨ e ∈ lblEdges N 1 2 x ∨ e ∈ lblEdges N 0 2 x := by
  simp [lblSet]

/-- The label sets of distinct `x ≠ x'` are disjoint. -/
theorem disjoint_lblSet {N : ℕ} [NeZero N] {x x' : ZMod N} (hne : x ≠ x') :
    Disjoint (lblSet N x) (lblSet N x') := by
  rw [Finset.disjoint_left]
  intro e he he'
  rw [mem_lblSet] at he he'
  rcases he with h | h | h <;> rcases he' with h' | h' | h' <;>
    · obtain ⟨a, rfl⟩ := mem_lblEdges.mp h
      obtain ⟨a', h2⟩ := mem_lblEdges.mp h'
      exact absurd (lblEdges_mk_eq (by decide) (by decide) h2).2.2.2 hne.symm

/-- The three edges of the triangle over `a` in the Schur triple
`(x, y, x + y)`. -/
def triEdges (a x y : ZMod N) : Finset (Sym2 (TripVert N)) :=
  {s((a, 0), (a + x, 1)), s((a + x, 1), (a + x + y, 2)),
    s((a, 0), (a + (x + y), 2))}

theorem mem_triEdges {N : ℕ} {a x y : ZMod N} {e : Sym2 (TripVert N)} :
    e ∈ triEdges a x y ↔
      e = s((a, 0), (a + x, 1)) ∨ e = s((a + x, 1), (a + x + y, 2)) ∨
        e = s((a, 0), (a + (x + y), 2)) := by
  simp [triEdges]

/-- The triangles for distinct basepoints are edge-disjoint. -/
theorem disjoint_triEdges {N : ℕ} [NeZero N] {x y a a' : ZMod N}
    (hne : a ≠ a') :
    Disjoint (triEdges a x y) (triEdges a' x y) := by
  rw [Finset.disjoint_left]
  intro e he he'
  rw [mem_triEdges] at he he'
  rcases he with rfl | rfl | rfl <;> rcases he' with h | h | h
  · exact absurd (lblEdges_mk_eq (show (0 : Fin 3) < 1 by decide)
      (show (0 : Fin 3) < 1 by decide) h).1 hne
  · exact absurd (lblEdges_mk_eq (show (0 : Fin 3) < 1 by decide)
      (show (1 : Fin 3) < 2 by decide) h).2.1 (by decide)
  · exact absurd (lblEdges_mk_eq (show (0 : Fin 3) < 1 by decide)
      (show (0 : Fin 3) < 2 by decide) h).2.2.1 (by decide)
  · exact absurd (lblEdges_mk_eq (show (1 : Fin 3) < 2 by decide)
      (show (0 : Fin 3) < 1 by decide) h).2.1 (by decide)
  · exact absurd (add_right_cancel
      (lblEdges_mk_eq (show (1 : Fin 3) < 2 by decide)
        (show (1 : Fin 3) < 2 by decide) h).1) hne
  · exact absurd (lblEdges_mk_eq (show (1 : Fin 3) < 2 by decide)
      (show (0 : Fin 3) < 2 by decide) h).2.1 (by decide)
  · exact absurd (lblEdges_mk_eq (show (0 : Fin 3) < 2 by decide)
      (show (0 : Fin 3) < 1 by decide) h).2.2.1 (by decide)
  · exact absurd (lblEdges_mk_eq (show (0 : Fin 3) < 2 by decide)
      (show (1 : Fin 3) < 2 by decide) h).2.1 (by decide)
  · exact absurd (lblEdges_mk_eq (show (0 : Fin 3) < 2 by decide)
      (show (0 : Fin 3) < 2 by decide) h).1 hne

theorem mem_lblSet_01 {N : ℕ} [NeZero N] {a x : ZMod N} :
    s((a, 0), (a + x, 1)) ∈ lblSet N x :=
  Finset.mem_union.mpr (Or.inl (mem_lblEdges.mpr ⟨a, rfl⟩))

theorem mem_lblSet_12 {N : ℕ} [NeZero N] {a x : ZMod N} :
    s((a, 1), (a + x, 2)) ∈ lblSet N x :=
  Finset.mem_union.mpr
    (Or.inr (Finset.mem_union.mpr (Or.inl (mem_lblEdges.mpr ⟨a, rfl⟩))))

theorem mem_lblSet_02 {N : ℕ} [NeZero N] {a x : ZMod N} :
    s((a, 0), (a + x, 2)) ∈ lblSet N x :=
  Finset.mem_union.mpr
    (Or.inr (Finset.mem_union.mpr (Or.inr (mem_lblEdges.mpr ⟨a, rfl⟩))))

/-- The triangle edges lie in the label sets of the three triple
entries. -/
theorem triEdges_subset_lbl_union {N : ℕ} [NeZero N] {a x y : ZMod N} :
    triEdges a x y ⊆ lblSet N x ∪ (lblSet N y ∪ lblSet N (x + y)) := by
  intro e he
  rcases mem_triEdges.mp he with rfl | rfl | rfl
  · exact Finset.mem_union.mpr (Or.inl mem_lblSet_01)
  · exact Finset.mem_union.mpr
      (Or.inr (Finset.mem_union.mpr (Or.inl mem_lblSet_12)))
  · exact Finset.mem_union.mpr
      (Or.inr (Finset.mem_union.mpr (Or.inr mem_lblSet_02)))

/-- The triangle edges are edges of the difference graph. -/
theorem triEdges_subset_edgeFinset {N : ℕ} [NeZero N] {s : Finset (ZMod N)}
    {a x y : ZMod N} (hx : x ∈ s) (hy : y ∈ s) (hz : x + y ∈ s) :
    triEdges a x y ⊆ (tripGraph s).edgeFinset := by
  intro e he
  rcases mem_triEdges.mp he with rfl | rfl | rfl
  · exact lblEdges_subset_edgeFinset (by decide) hx (mem_lblEdges.mpr ⟨a, rfl⟩)
  · exact lblEdges_subset_edgeFinset (by decide) hy
      (mem_lblEdges.mpr ⟨a + x, rfl⟩)
  · exact lblEdges_subset_edgeFinset (by decide) hz (mem_lblEdges.mpr ⟨a, rfl⟩)

/-! ## The marking argument -/

/-- If `x, y, x + y ∈ s`, every triangle `triEdges a x y` contains a
deleted edge: otherwise it would be a triangle of `G'`. -/
theorem triEdges_inter_del_nonempty {N : ℕ} [NeZero N] {s : Finset (ZMod N)}
    {G' : SimpleGraph (TripVert N)} [DecidableRel G'.Adj]
    (_hle : G' ≤ tripGraph s) (hfree : G'.CliqueFree 3)
    {a x y : ZMod N} (hx : x ∈ s) (hy : y ∈ s) (hz : x + y ∈ s) :
    (triEdges a x y ∩ ((tripGraph s).edgeFinset \ G'.edgeFinset)).Nonempty := by
  classical
  by_contra h
  have hT := triEdges_subset_edgeFinset hx hy hz (a := a) (s := s)
  have hempty := Finset.not_nonempty_iff_eq_empty.mp h
  have hnd : ∀ e ∈ triEdges a x y,
      e ∉ (tripGraph s).edgeFinset \ G'.edgeFinset :=
    fun e he hd => Finset.eq_empty_iff_forall_notMem.mp hempty e
      (mem_inter.mpr ⟨he, hd⟩)
  have hinG' : ∀ e ∈ triEdges a x y, e ∈ G'.edgeFinset := by
    intro e he
    by_contra h'
    exact hnd e he (mem_sdiff.mpr ⟨hT he, h'⟩)
  have adj' : ∀ {u v : TripVert N},
      (s(u, v) : Sym2 (TripVert N)) ∈ triEdges a x y → G'.Adj u v :=
    fun {u v} he => (mem_edgeFinset.mp (hinG' _ he) : G'.Adj u v)
  exact hfree _ (is3Clique_triple_iff.mpr
    ⟨adj' (mem_triEdges.mpr (Or.inl rfl)),
     adj' (mem_triEdges.mpr (Or.inr (Or.inr rfl))),
     adj' (mem_triEdges.mpr (Or.inr (Or.inl (by rw [← add_assoc]))))⟩)

/-- Counting: a Schur triple `(x, y, x + y)` of `s` forces at least `N`
deleted edges in the union of the three label sets, since the `N`
triangles are edge-disjoint and each contains a deleted edge. -/
theorem deleted_count_ge {N : ℕ} [NeZero N] (s : Finset (ZMod N))
    {G' : SimpleGraph (TripVert N)} [DecidableRel G'.Adj]
    (hle : G' ≤ tripGraph s) (hfree : G'.CliqueFree 3)
    {x y : ZMod N} (hx : x ∈ s) (hy : y ∈ s) (hz : x + y ∈ s) :
    (N : ℝ) ≤
      (#((lblSet N x ∪ (lblSet N y ∪ lblSet N (x + y))) ∩
        ((tripGraph s).edgeFinset \ G'.edgeFinset)) : ℝ) := by
  classical
  set D := (tripGraph s).edgeFinset \ G'.edgeFinset with hD
  have hne : ∀ a : ZMod N, (triEdges a x y ∩ D).Nonempty :=
    fun a => triEdges_inter_del_nonempty hle hfree hx hy hz
  have hdisj : (↑(univ : Finset (ZMod N)) : Set (ZMod N)).PairwiseDisjoint
      (fun a => triEdges a x y ∩ D) :=
    fun a _ b _ hne' => Disjoint.mono inter_subset_left inter_subset_left
      (disjoint_triEdges hne')
  have hcard :
      #((univ : Finset (ZMod N)).biUnion (fun a => triEdges a x y ∩ D)) =
        ∑ a ∈ univ, #(triEdges a x y ∩ D) :=
    card_biUnion hdisj
  have hsub : (univ : Finset (ZMod N)).biUnion (fun a => triEdges a x y ∩ D) ⊆
      (lblSet N x ∪ (lblSet N y ∪ lblSet N (x + y))) ∩ D := by
    intro e he
    rw [mem_biUnion] at he
    obtain ⟨a, -, he⟩ := he
    obtain ⟨he1, he2⟩ := mem_inter.mp he
    exact mem_inter.mpr ⟨triEdges_subset_lbl_union he1, he2⟩
  have h1 : (N : ℝ) ≤ ∑ a ∈ univ, (#(triEdges a x y ∩ D) : ℝ) := by
    have h3 : ∑ _a ∈ univ, (1 : ℕ) ≤ ∑ a ∈ univ, #(triEdges a x y ∩ D) :=
      Finset.sum_le_sum fun a _ => Finset.card_pos.mpr (hne a)
    rw [Finset.sum_const, smul_eq_mul, mul_one, card_univ, ZMod.card] at h3
    exact_mod_cast h3
  calc (N : ℝ)
      ≤ ∑ a ∈ univ, (#(triEdges a x y ∩ D) : ℝ) := h1
    _ = (#((univ : Finset (ZMod N)).biUnion (fun a => triEdges a x y ∩ D)) : ℝ) := by
        exact_mod_cast hcard.symm
    _ ≤ (#((lblSet N x ∪ (lblSet N y ∪ lblSet N (x + y))) ∩ D) : ℝ) := by
        exact_mod_cast card_le_card hsub

/-- The union over the three labels: the count splits into the three
label classes. -/
theorem deleted_count_le {N : ℕ} [NeZero N]
    {D : Finset (Sym2 (TripVert N))} {x y : ZMod N} :
    (#((lblSet N x ∪ (lblSet N y ∪ lblSet N (x + y))) ∩ D) : ℝ) ≤
      (#(lblSet N x ∩ D) : ℝ) +
        ((#(lblSet N y ∩ D) : ℝ) + (#(lblSet N (x + y) ∩ D) : ℝ)) := by
  have hsub : (lblSet N x ∪ (lblSet N y ∪ lblSet N (x + y))) ∩ D ⊆
      (lblSet N x ∩ D) ∪ ((lblSet N y ∩ D) ∪ (lblSet N (x + y) ∩ D)) := by
    intro e he
    simp only [mem_inter, mem_union] at he ⊢
    tauto
  have h1 : #(lblSet N x ∩ D ∪ (lblSet N y ∩ D ∪ lblSet N (x + y) ∩ D)) ≤
      #(lblSet N x ∩ D) + (#(lblSet N y ∩ D) + #(lblSet N (x + y) ∩ D)) := by
    have h2 := card_union_le (lblSet N x ∩ D)
      (lblSet N y ∩ D ∪ lblSet N (x + y) ∩ D)
    have h3 := card_union_le (lblSet N y ∩ D) (lblSet N (x + y) ∩ D)
    omega
  have h := (card_le_card hsub).trans h1
  exact_mod_cast h

/-! ## The removal lemma -/

/-- **Schur removal lemma in `ZMod N`.** -/
theorem schurRemovalZMod : SchurRemovalZMod := by
  classical
  intro ε hε
  set ε' := ε / 100 with hε'
  have hε'0 : (0 : ℝ) < ε' := by positivity
  refine ⟨SimpleGraph.triangleRemovalBound ε',
    SimpleGraph.triangleRemovalBound_pos hε'0, ?_⟩
  rw [Filter.eventually_atTop]
  refine ⟨1, fun N hN => ?_⟩
  intro s hcount
  haveI : NeZero N := ⟨by omega⟩
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  set δ := SimpleGraph.triangleRemovalBound ε' with hδ
  have hδ0 : (0 : ℝ) < δ := SimpleGraph.triangleRemovalBound_pos hε'0
  have hcardV : Fintype.card (TripVert N) = 3 * N := by
    rw [Fintype.card_prod, ZMod.card, Fintype.card_fin, mul_comm]
  -- The triangle hypothesis for `triangle_removal`.
  have hcl : ((tripGraph s).cliqueFinset 3).card <
      δ * Fintype.card (TripVert N) ^ 3 := by
    have hc : (((tripGraph s).cliqueFinset 3).card : ℝ) =
        (N : ℝ) * zmodSchurTripleCount s := by
      exact_mod_cast tripGraph_cliqueFinset_card s
    rw [hc, hcardV]
    push_cast
    have hle : (N : ℝ) * zmodSchurTripleCount s ≤ δ * (N : ℝ) ^ 3 := by
      have hmul := mul_le_mul_of_nonneg_left hcount hN0.le
      calc (N : ℝ) * zmodSchurTripleCount s
          ≤ (N : ℝ) * (δ * (N : ℝ) ^ 2) := hmul
        _ = δ * (N : ℝ) ^ 3 := by ring
    have hpos : (0 : ℝ) < δ * (N : ℝ) ^ 3 := mul_pos hδ0 (pow_pos hN0 3)
    nlinarith [hle, hpos]
  obtain ⟨G', hle, hdec, hdel, hfree⟩ := SimpleGraph.triangle_removal hcl
  letI := hdec
  set D := (tripGraph s).edgeFinset \ G'.edgeFinset with hD
  have hsub' : G'.edgeFinset ⊆ (tripGraph s).edgeFinset :=
    SimpleGraph.edgeFinset_mono hle
  have hDcard : (#D : ℝ) < ε' * (3 * (N : ℝ)) ^ 2 := by
    have hsd : #D =
        (tripGraph s).edgeFinset.card - G'.edgeFinset.card :=
      Finset.card_sdiff_of_subset hsub'
    rw [hsd, Nat.cast_sub (card_le_card hsub')]
    push_cast at hdel
    rw [hcardV] at hdel
    push_cast at hdel
    exact hdel
  -- The marked elements and the surviving set `t`.
  set t := s.filter
    (fun x => ¬ (N : ℝ) / 3 ≤ (#(lblSet N x ∩ D) : ℝ)) with ht
  refine ⟨t, Finset.filter_subset _ _, ?_, ?_⟩
  · -- `t` is sum-free.
    intro x hx y hy hxy
    rw [ht, mem_filter] at hx hy hxy
    obtain ⟨hxs, hux⟩ := hx
    obtain ⟨hys, huy⟩ := hy
    obtain ⟨hzs, huz⟩ := hxy
    have hlx : (#(lblSet N x ∩ D) : ℝ) < (N : ℝ) / 3 := not_le.mp hux
    have hly : (#(lblSet N y ∩ D) : ℝ) < (N : ℝ) / 3 := not_le.mp huy
    have hlz : (#(lblSet N (x + y) ∩ D) : ℝ) < (N : ℝ) / 3 :=
      not_le.mp huz
    have hge := deleted_count_ge s hle hfree hxs hys hzs
    have hle3 := deleted_count_le (D := D) (N := N) (x := x) (y := y)
    linarith [hge, hle3, hlx, hly, hlz]
  · -- The deletion count.
    have hst : s \ t =
        s.filter (fun x => (N : ℝ) / 3 ≤ (#(lblSet N x ∩ D) : ℝ)) := by
      ext x
      rw [ht]
      simp only [mem_sdiff, mem_filter, not_and, not_not]
      constructor
      · rintro ⟨hx, h⟩
        exact ⟨hx, h hx⟩
      · rintro ⟨hx, h⟩
        exact ⟨hx, fun _ => h⟩
    rw [hst]
    -- Bound the number of marked elements.
    set M := s.filter
      (fun x => (N : ℝ) / 3 ≤ (#(lblSet N x ∩ D) : ℝ)) with hM
    have h2 : (M.card : ℝ) * ((N : ℝ) / 3) ≤
        ∑ x ∈ M, (#(lblSet N x ∩ D) : ℝ) := by
      have h2' : (∑ _x ∈ M, ((N : ℝ) / 3)) ≤
          ∑ x ∈ M, (#(lblSet N x ∩ D) : ℝ) :=
        Finset.sum_le_sum fun x hx => (mem_filter.mp hx).2
      rwa [Finset.sum_const, nsmul_eq_mul] at h2'
    have hdisj : (↑s : Set (ZMod N)).PairwiseDisjoint
        (fun x => lblSet N x ∩ D) :=
      fun a _ b _ hne => Disjoint.mono inter_subset_left inter_subset_left
        (disjoint_lblSet hne)
    have h5 : (s.biUnion fun x => lblSet N x ∩ D) ⊆ D := by
      intro e he
      rw [mem_biUnion] at he
      obtain ⟨x, -, he⟩ := he
      exact inter_subset_right he
    have h6 : (∑ x ∈ s, (#(lblSet N x ∩ D) : ℝ)) ≤ (#D : ℝ) := by
      have h7 : (∑ x ∈ s, #(lblSet N x ∩ D)) =
          #(s.biUnion fun x => lblSet N x ∩ D) :=
        (card_biUnion hdisj).symm
      have h8 : (∑ x ∈ s, #(lblSet N x ∩ D)) ≤ #D := by
        rw [h7]
        exact card_le_card h5
      exact_mod_cast h8
    have hMsub : M ⊆ s := Finset.filter_subset _ _
    have h9 : (∑ x ∈ M, (#(lblSet N x ∩ D) : ℝ)) ≤
        ∑ x ∈ s, (#(lblSet N x ∩ D) : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hMsub
        fun x _ _ => Nat.cast_nonneg _
    have h10 : (M.card : ℝ) * ((N : ℝ) / 3) < ε' * (3 * (N : ℝ)) ^ 2 :=
      lt_of_le_of_lt (h2.trans (h9.trans h6)) hDcard
    have hN30 : (0 : ℝ) < (N : ℝ) / 3 := by positivity
    have h11 : (M.card : ℝ) < ε' * (3 * (N : ℝ)) ^ 2 / ((N : ℝ) / 3) :=
      (lt_div_iff₀ hN30).mpr h10
    have h12 : ε' * (3 * (N : ℝ)) ^ 2 / ((N : ℝ) / 3) = 27 * ε' * (N : ℝ) := by
      rw [div_eq_iff (ne_of_gt hN30)]
      ring
    rw [h12] at h11
    rw [hε'] at h11
    have hNε : (0 : ℝ) < ε * (N : ℝ) := mul_pos hε hN0
    linarith [h11, hNε]

end JSP000728
