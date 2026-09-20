import JSPProblem.HujterTuza
import JSPProblem.Odds

/-!
# JSP-000728 — BLST Lemma 3.4: the odd-type container count

For a sum-free fingerprint `S` consisting of even numbers, the link graph
`L_S[O]` on the odd numbers `O = odds n` has both *sum edges*
(`x + y ∈ S`, "red") and *difference edges* (`|x - y| ∈ S`, "blue").
This file proves the counting ingredients of BLST15 Lemma 3.4 / Claim 3.5:

* `linkLoop_iff_two_mul_mem_of_odd` — on odd vertices with `S` all-even,
  the loop predicate collapses to `2 * x ∈ S` (`x ± z` is odd for even `z`,
  hence never in `S`).
* `claim_3_5` — every triangle of `L_S` on a positive sum-free `S` has
  **0 or 2 blue edges**, stated as the four-type disjunction used by the
  count (all-red, or exactly one edge red).  Each excluded pattern
  produces a Schur triple in `S`, e.g. `(y - x) + (z - y) = z - x`.
* `triangles_le_mul_card_pow` — `L_S[O]` has at most `24 · |S|³` ordered
  triangles `x < y < z`: each of the four surviving types injects into
  `S³` via its `3 × 3` linear system `M·(x,y,z)ᵀ = (s₁,s₂,s₃)`,
  `|det M| = 2` (the solution is unique over `ℤ`, so the witness map
  `triangle ↦ (s₁,s₂,s₃)` is injective — no `3!` factor needed).
* `exists_triangleFree_sdiff_of_small_fingerprint` — for `|S| ≤ m`,
  deleting the union `T` of all triangle vertices (`|T| ≤ 72·m³`) leaves
  `L_S[O] ∖ T` triangle-free, ready for the Hujter–Tuza `2^{|B|/2}` bound.
* `deg_lo_le`, `deg_le_two_mul_add` — the dense-case degree estimates
  `|S| ≤ 2·deg(x)` and `deg(x) ≤ 2|S| + 2` for `x ∈ odds n`, feeding the
  Sapozhenko almost-regular MIS bound (applied in a separate file).
-/

namespace JSP000728

/-! ## Loops on odd vertices -/

/-- For odd `x` and `S` consisting of even numbers, the link-graph loop at
`x` is exactly `2x ∈ S`: the other two loop types would place the odd
integer `x - z` or `x + z` (with `z ∈ S` even) inside `S`. -/
theorem linkLoop_iff_two_mul_mem_of_odd {S : Finset ℤ} {x : ℤ}
    (hx : Odd x) (hS : ∀ s ∈ S, Even s) :
    linkLoop S x ↔ 2 * x ∈ S := by
  obtain ⟨a, ha⟩ := hx
  constructor
  · rintro (⟨z, hz, hxz⟩ | ⟨z, hz, hxz⟩ | hxx)
    · obtain ⟨b, hb⟩ := hS z hz
      obtain ⟨c, hc⟩ := hS _ hxz
      omega
    · obtain ⟨b, hb⟩ := hS z hz
      obtain ⟨c, hc⟩ := hS _ hxz
      omega
    · exact (two_mul x).symm ▸ hxx
  · intro h
    exact Or.inr (Or.inr (two_mul x ▸ h))

/-! ## Claim 3.5: triangles have 0 or 2 blue edges -/

/-- **BLST Claim 3.5.**  For positive sum-free `S` and `x < y < z`
pairwise link-adjacent, the triangle `xyz` has 0 or 2 *blue* (difference)
edges — equivalently it is of one of the four types:

* all edges red: `x + y, y + z, x + z ∈ S`;
* only `xy` red: `x + y, z - y, z - x ∈ S`;
* only `yz` red: `y - x, y + z, z - x ∈ S`;
* only `xz` red: `y - x, z - y, x + z ∈ S`.

Exactly-one-blue and all-blue triangles are impossible: each would give a
Schur triple in `S` — e.g. only `xz` blue gives `(z - x) + (x + y) = y + z`,
and all-blue gives `(y - x) + (z - y) = z - x`. -/
theorem claim_3_5 {S : Finset ℤ} (hSf : IsSumFree S)
    (hpos : ∀ s ∈ S, 0 < s) {x y z : ℤ} (hxy : x < y) (hyz : y < z)
    (e1 : linkAdj S x y) (e2 : linkAdj S y z) (e3 : linkAdj S x z) :
    (x + y ∈ S ∧ y + z ∈ S ∧ x + z ∈ S) ∨
    (x + y ∈ S ∧ z - y ∈ S ∧ z - x ∈ S) ∨
    (y - x ∈ S ∧ y + z ∈ S ∧ z - x ∈ S) ∨
    (y - x ∈ S ∧ z - y ∈ S ∧ x + z ∈ S) := by
  -- For positive `S`, the negative differences `x - y`, `y - z`, `x - z`
  -- can never be witnesses, so each edge is red or (forward-difference)
  -- blue.
  have e1' : x + y ∈ S ∨ y - x ∈ S := by
    rcases e1 with h | h | h
    · exact Or.inl h
    · exact absurd (hpos _ h) (by omega)
    · exact Or.inr h
  have e2' : y + z ∈ S ∨ z - y ∈ S := by
    rcases e2 with h | h | h
    · exact Or.inl h
    · exact absurd (hpos _ h) (by omega)
    · exact Or.inr h
  have e3' : x + z ∈ S ∨ z - x ∈ S := by
    rcases e3 with h | h | h
    · exact Or.inl h
    · exact absurd (hpos _ h) (by omega)
    · exact Or.inr h
  rcases e1' with r1 | b1 <;> rcases e2' with r2 | b2 <;>
    rcases e3' with r3 | b3
  · -- 0 blue: all red.
    exact Or.inl ⟨r1, r2, r3⟩
  · -- only `xz` blue: `(z - x) + (x + y) = y + z` is a Schur triple in `S`.
    have h := hSf (z - x) b3 (x + y) r1
    rw [show z - x + (x + y) = y + z by ring] at h
    exact absurd r2 h
  · -- only `yz` blue: `(x + y) + (z - y) = x + z`.
    have h := hSf (x + y) r1 (z - y) b2
    rw [show x + y + (z - y) = x + z by ring] at h
    exact absurd r3 h
  · -- 2 blue (`yz`, `xz`): only `xy` red.
    exact Or.inr (Or.inl ⟨r1, b2, b3⟩)
  · -- only `xy` blue: `(y - x) + (x + z) = y + z`.
    have h := hSf (y - x) b1 (x + z) r3
    rw [show y - x + (x + z) = y + z by ring] at h
    exact absurd r2 h
  · -- 2 blue (`xy`, `xz`): only `yz` red.
    exact Or.inr (Or.inr (Or.inl ⟨b1, r2, b3⟩))
  · -- 2 blue (`xy`, `yz`): only `xz` red.
    exact Or.inr (Or.inr (Or.inr ⟨b1, b2, r3⟩))
  · -- 3 blue: `(y - x) + (z - y) = z - x`.
    have h := hSf (y - x) b1 (z - y) b2
    rw [show y - x + (z - y) = z - x by ring] at h
    exact absurd b3 h

/-! ## Triangles and the `24 · |S|³` bound -/

/-- Ordered link-graph triangles on a vertex set `O`: triples `x < y < z`
of vertices of `O` that are pairwise `linkAdj S`-adjacent. -/
def linkTri (S O : Finset ℤ) : Finset ((ℤ × ℤ) × ℤ) :=
  ((O ×ˢ O) ×ˢ O).filter fun p =>
    p.1.1 < p.1.2 ∧ p.1.2 < p.2 ∧ linkAdj S p.1.1 p.1.2 ∧
      linkAdj S p.1.2 p.2 ∧ linkAdj S p.1.1 p.2

theorem mem_linkTri {S O : Finset ℤ} {p : (ℤ × ℤ) × ℤ} :
    p ∈ linkTri S O ↔
      p.1.1 ∈ O ∧ p.1.2 ∈ O ∧ p.2 ∈ O ∧
        p.1.1 < p.1.2 ∧ p.1.2 < p.2 ∧ linkAdj S p.1.1 p.1.2 ∧
          linkAdj S p.1.2 p.2 ∧ linkAdj S p.1.1 p.2 := by
  unfold linkTri
  rw [Finset.mem_filter, Finset.mem_product, Finset.mem_product]
  tauto

/-- Triangles with all three edges red. -/
private def triA (S O : Finset ℤ) : Finset ((ℤ × ℤ) × ℤ) :=
  (linkTri S O).filter fun p =>
    p.1.1 + p.1.2 ∈ S ∧ p.1.2 + p.2 ∈ S ∧ p.1.1 + p.2 ∈ S

/-- Triangles with only `xy` red (`yz`, `xz` blue). -/
private def triB (S O : Finset ℤ) : Finset ((ℤ × ℤ) × ℤ) :=
  (linkTri S O).filter fun p =>
    p.1.1 + p.1.2 ∈ S ∧ p.2 - p.1.2 ∈ S ∧ p.2 - p.1.1 ∈ S

/-- Triangles with only `yz` red (`xy`, `xz` blue). -/
private def triC (S O : Finset ℤ) : Finset ((ℤ × ℤ) × ℤ) :=
  (linkTri S O).filter fun p =>
    p.1.2 - p.1.1 ∈ S ∧ p.1.2 + p.2 ∈ S ∧ p.2 - p.1.1 ∈ S

/-- Triangles with only `xz` red (`xy`, `yz` blue). -/
private def triD (S O : Finset ℤ) : Finset ((ℤ × ℤ) × ℤ) :=
  (linkTri S O).filter fun p =>
    p.1.2 - p.1.1 ∈ S ∧ p.2 - p.1.2 ∈ S ∧ p.1.1 + p.2 ∈ S

/-- By Claim 3.5 every triangle is of one of the four types. -/
private theorem linkTri_subset_union {S O : Finset ℤ}
    (hSf : IsSumFree S) (hpos : ∀ s ∈ S, 0 < s) :
    linkTri S O ⊆ triA S O ∪ triB S O ∪ triC S O ∪ triD S O := by
  intro p hp
  have hp' := mem_linkTri.mp hp
  obtain ⟨-, -, -, hxy, hyz, e1, e2, e3⟩ := hp'
  have hc := claim_3_5 hSf hpos hxy hyz e1 e2 e3
  simp only [triA, triB, triC, triD, Finset.mem_filter, Finset.mem_union]
  rcases hc with h | h | h | h
  · exact Or.inl (Or.inl (Or.inl ⟨hp, h⟩))
  · exact Or.inl (Or.inl (Or.inr ⟨hp, h⟩))
  · exact Or.inl (Or.inr ⟨hp, h⟩)
  · exact Or.inr ⟨hp, h⟩

/-- A map `f` sending each triangle of a type set `T` into `S³`
injectively bounds `|T| ≤ |S|³`. -/
private theorem card_le_cube_of_injOn {S : Finset ℤ}
    {T : Finset ((ℤ × ℤ) × ℤ)} (f : (ℤ × ℤ) × ℤ → (ℤ × ℤ) × ℤ)
    (hf : ∀ p ∈ T, f p ∈ (S ×ˢ S) ×ˢ S)
    (hinj : Set.InjOn f T) : T.card ≤ S.card ^ 3 := by
  refine (Finset.card_le_card_of_injOn f hf hinj).trans_eq ?_
  rw [Finset.card_product, Finset.card_product]
  ring

private theorem card_triA_le (S O : Finset ℤ) :
    (triA S O).card ≤ S.card ^ 3 := by
  apply card_le_cube_of_injOn
    (fun p : (ℤ × ℤ) × ℤ => ((p.1.1 + p.1.2, p.1.2 + p.2), p.1.1 + p.2))
  · intro p hp
    obtain ⟨⟨x, y⟩, z⟩ := p
    simp only [triA, Finset.mem_filter] at hp
    simp only [Finset.mem_product]
    exact ⟨⟨hp.2.1, hp.2.2.1⟩, hp.2.2.2⟩
  · intro p hp q hq h
    obtain ⟨⟨x1, y1⟩, z1⟩ := p
    obtain ⟨⟨x2, y2⟩, z2⟩ := q
    simp only [Prod.mk.injEq] at h ⊢
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    refine ⟨⟨?_, ?_⟩, ?_⟩ <;> omega

private theorem card_triB_le (S O : Finset ℤ) :
    (triB S O).card ≤ S.card ^ 3 := by
  apply card_le_cube_of_injOn
    (fun p : (ℤ × ℤ) × ℤ => ((p.1.1 + p.1.2, p.2 - p.1.2), p.2 - p.1.1))
  · intro p hp
    obtain ⟨⟨x, y⟩, z⟩ := p
    simp only [triB, Finset.mem_filter] at hp
    simp only [Finset.mem_product]
    exact ⟨⟨hp.2.1, hp.2.2.1⟩, hp.2.2.2⟩
  · intro p hp q hq h
    obtain ⟨⟨x1, y1⟩, z1⟩ := p
    obtain ⟨⟨x2, y2⟩, z2⟩ := q
    simp only [Prod.mk.injEq] at h ⊢
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    refine ⟨⟨?_, ?_⟩, ?_⟩ <;> omega

private theorem card_triC_le (S O : Finset ℤ) :
    (triC S O).card ≤ S.card ^ 3 := by
  apply card_le_cube_of_injOn
    (fun p : (ℤ × ℤ) × ℤ => ((p.1.2 - p.1.1, p.1.2 + p.2), p.2 - p.1.1))
  · intro p hp
    obtain ⟨⟨x, y⟩, z⟩ := p
    simp only [triC, Finset.mem_filter] at hp
    simp only [Finset.mem_product]
    exact ⟨⟨hp.2.1, hp.2.2.1⟩, hp.2.2.2⟩
  · intro p hp q hq h
    obtain ⟨⟨x1, y1⟩, z1⟩ := p
    obtain ⟨⟨x2, y2⟩, z2⟩ := q
    simp only [Prod.mk.injEq] at h ⊢
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    refine ⟨⟨?_, ?_⟩, ?_⟩ <;> omega

private theorem card_triD_le (S O : Finset ℤ) :
    (triD S O).card ≤ S.card ^ 3 := by
  apply card_le_cube_of_injOn
    (fun p : (ℤ × ℤ) × ℤ => ((p.1.2 - p.1.1, p.2 - p.1.2), p.1.1 + p.2))
  · intro p hp
    obtain ⟨⟨x, y⟩, z⟩ := p
    simp only [triD, Finset.mem_filter] at hp
    simp only [Finset.mem_product]
    exact ⟨⟨hp.2.1, hp.2.2.1⟩, hp.2.2.2⟩
  · intro p hp q hq h
    obtain ⟨⟨x1, y1⟩, z1⟩ := p
    obtain ⟨⟨x2, y2⟩, z2⟩ := q
    simp only [Prod.mk.injEq] at h ⊢
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    refine ⟨⟨?_, ?_⟩, ?_⟩ <;> omega

/-- **The triangle count.**  For positive sum-free `S`, the link graph on
any vertex set `O` has at most `24 · |S|³` ordered triangles `x < y < z`:
four types, each injective into `S³` (in fact the count is `≤ 4·|S|³`). -/
theorem triangles_le_mul_card_pow {S O : Finset ℤ}
    (hSf : IsSumFree S) (hpos : ∀ s ∈ S, 0 < s) :
    (linkTri S O).card ≤ 24 * S.card ^ 3 := by
  have hA := card_triA_le S O
  have hB := card_triB_le S O
  have hC := card_triC_le S O
  have hD := card_triD_le S O
  have hsub := Finset.card_le_card (linkTri_subset_union (O := O) hSf hpos)
  have hu1 := Finset.card_union_le
    (triA S O ∪ triB S O ∪ triC S O) (triD S O)
  have hu2 := Finset.card_union_le (triA S O ∪ triB S O) (triC S O)
  have hu3 := Finset.card_union_le (triA S O) (triB S O)
  omega

/-! ## Deleting all triangle vertices -/

/-- The union of all triangle vertices. -/
def triVerts (S O : Finset ℤ) : Finset ℤ :=
  (linkTri S O).biUnion fun p => {p.1.1, p.1.2, p.2}

theorem triVerts_subset (S O : Finset ℤ) : triVerts S O ⊆ O := by
  intro v hv
  rw [triVerts, Finset.mem_biUnion] at hv
  obtain ⟨p, hp, hv⟩ := hv
  obtain ⟨hxO, hyO, hzO, -, -, -, -, -⟩ := mem_linkTri.mp hp
  rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl
  · exact hxO
  · exact hyO
  · exact hzO

private theorem card_triple_le (a b c : ℤ) :
    ({a, b, c} : Finset ℤ).card ≤ 3 := by
  calc ({a, b, c} : Finset ℤ).card
      = (insert a ({b, c} : Finset ℤ)).card := rfl
    _ ≤ ({b, c} : Finset ℤ).card + 1 := Finset.card_insert_le _ _
    _ ≤ (({c} : Finset ℤ).card + 1) + 1 := by
        have h := Finset.card_insert_le b ({c} : Finset ℤ)
        omega
    _ = 3 := by rw [Finset.card_singleton]

private theorem card_triVerts_le (S O : Finset ℤ) :
    (triVerts S O).card ≤ 3 * (linkTri S O).card := by
  calc (triVerts S O).card
      ≤ ∑ p ∈ linkTri S O, ({p.1.1, p.1.2, p.2} : Finset ℤ).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ linkTri S O, 3 :=
        Finset.sum_le_sum fun p _ => card_triple_le _ _ _
    _ = 3 * (linkTri S O).card := by
        rw [Finset.sum_const_nat (fun _ _ => rfl), mul_comm]

/-- Any three pairwise distinct integers have a sorted order. -/
private theorem sorted_three {x y z : ℤ} (hxy : x ≠ y) (hyz : y ≠ z)
    (hxz : x ≠ z) :
    ∃ a b c : ℤ, a < b ∧ b < c ∧ ({a, b, c} : Finset ℤ) = {x, y, z} := by
  rcases lt_or_gt_of_ne hxy with h1 | h1 <;>
    rcases lt_or_gt_of_ne hyz with h2 | h2 <;>
    rcases lt_or_gt_of_ne hxz with h3 | h3
  · exact ⟨x, y, z, h1, h2, rfl⟩
  · omega
  · refine ⟨x, z, y, h3, h2, ?_⟩
    ext w
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  · refine ⟨z, x, y, h3, h1, ?_⟩
    ext w
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  · refine ⟨y, x, z, h1, h3, ?_⟩
    ext w
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  · refine ⟨y, z, x, h2, h3, ?_⟩
    ext w
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  · omega
  · refine ⟨z, y, x, h2, h1, ?_⟩
    ext w
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto

/-- Deleting `triVerts` from `O` leaves a triangle-free link graph:
a surviving triangle `x, y, z` would sort to a triple `a < b < c` in
`linkTri S O`, putting `a` inside `triVerts`. -/
theorem triangleFree_sdiff_triVerts (S O : Finset ℤ) :
    triangleFree (linkAdj S) (O \ triVerts S O) := by
  intro x hx y hy z hz hxy hyz hxz hcon
  obtain ⟨e1, e2, e3⟩ := hcon
  obtain ⟨a, b, c, hab, hbc, hset⟩ := sorted_three hxy hyz hxz
  have hmem : ∀ u ∈ ({a, b, c} : Finset ℤ), u ∈ ({x, y, z} : Finset ℤ) :=
    fun u hu => hset ▸ hu
  have haS : a ∈ ({x, y, z} : Finset ℤ) :=
    hmem a (Finset.mem_insert_self a _)
  have hbS : b ∈ ({x, y, z} : Finset ℤ) :=
    hmem b (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert_self b _)))
  have hcS : c ∈ ({x, y, z} : Finset ℤ) :=
    hmem c (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr
      (Or.inr (Finset.mem_singleton_self c)))))
  have hOT : ∀ u ∈ ({x, y, z} : Finset ℤ), u ∈ O \ triVerts S O := by
    intro u hu
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl | rfl
    · exact hx
    · exact hy
    · exact hz
  have hadj : ∀ u ∈ ({x, y, z} : Finset ℤ), ∀ v ∈ ({x, y, z} : Finset ℤ),
      u ≠ v → linkAdj S u v := by
    intro u hu v hv huv
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hu hv
    rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
    · exact absurd rfl huv
    · exact e1
    · exact e3
    · exact linkAdj_comm.mp e1
    · exact absurd rfl huv
    · exact e2
    · exact linkAdj_comm.mp e3
    · exact linkAdj_comm.mp e2
    · exact absurd rfl huv
  have haO : a ∈ O := (Finset.mem_sdiff.mp (hOT a haS)).1
  have hbO : b ∈ O := (Finset.mem_sdiff.mp (hOT b hbS)).1
  have hcO : c ∈ O := (Finset.mem_sdiff.mp (hOT c hcS)).1
  have habc : ((a, b), c) ∈ linkTri S O := by
    rw [mem_linkTri]
    exact ⟨haO, hbO, hcO, hab, hbc, hadj a haS b hbS (ne_of_lt hab),
      hadj b hbS c hcS (ne_of_lt hbc),
      hadj a haS c hcS (ne_of_lt (hab.trans hbc))⟩
  have haT : a ∈ triVerts S O :=
    Finset.mem_biUnion.mpr ⟨(⟨a, b⟩, c), habc, Finset.mem_insert_self a _⟩
  exact (Finset.mem_sdiff.mp (hOT a haS)).2 haT

/-- **Small-fingerprint removal of triangles.**  If `S` is a positive
sum-free set with `|S| ≤ m`, then deleting the `≤ 72·m³` triangle
vertices leaves the link graph `L_S[O]` triangle-free. -/
theorem exists_triangleFree_sdiff_of_small_fingerprint {S O : Finset ℤ}
    {m : ℕ} (hSf : IsSumFree S) (hpos : ∀ s ∈ S, 0 < s) (hm : S.card ≤ m) :
    ∃ T ⊆ O, T.card ≤ 72 * m ^ 3 ∧
      triangleFree (linkAdj S) (O \ T) := by
  refine ⟨triVerts S O, triVerts_subset S O, ?_,
    triangleFree_sdiff_triVerts S O⟩
  calc (triVerts S O).card
      ≤ 3 * (linkTri S O).card := card_triVerts_le S O
    _ ≤ 3 * (24 * S.card ^ 3) :=
        Nat.mul_le_mul (le_refl 3) (triangles_le_mul_card_pow hSf hpos)
    _ = 72 * S.card ^ 3 := by ring
    _ ≤ 72 * m ^ 3 :=
        Nat.mul_le_mul (le_refl 72) (Nat.pow_le_pow_left hm 3)

/-- Specialisation to `O = odds n`. -/
theorem exists_triangleFree_sdiff_odds {n : ℕ} {S : Finset ℤ} {m : ℕ}
    (hSf : IsSumFree S) (hpos : ∀ s ∈ S, 0 < s) (hm : S.card ≤ m) :
    ∃ T ⊆ odds n, T.card ≤ 72 * m ^ 3 ∧
      triangleFree (linkAdj S) (odds n \ T) :=
  exists_triangleFree_sdiff_of_small_fingerprint hSf hpos hm

/-! ## Degree bounds for the dense case (`|S| ≥ n^{1/4}`) -/

/-- The link-graph neighbourhood of `x` inside `O`. -/
def linkNbrs (S O : Finset ℤ) (x : ℤ) : Finset ℤ :=
  O.filter (linkAdj S x)

/-- **Upper degree bound.**  A neighbour `y ∈ odds n` of `x` satisfies
`y = x + s` or `y = |x - s|` for some `s ∈ S`, so the neighbourhood is
covered by two images of `S`; in particular `deg(x) ≤ 2·|S|` (stated with
the `+ 2` slack that accounts for a possible loop in the Sapozhenko
convention). -/
theorem linkNbrs_card_le_two_mul {n : ℕ} {S : Finset ℤ} {x : ℤ}
    (_hx : x ∈ odds n) :
    (linkNbrs S (odds n) x).card ≤ 2 * S.card := by
  have hsub : linkNbrs S (odds n) x ⊆
      S.image (fun s => x + s) ∪ S.image (fun s => |x - s|) := by
    intro y hy
    rw [linkNbrs, Finset.mem_filter] at hy
    obtain ⟨hyO, hadj⟩ := hy
    have hy1 : 1 ≤ y := (Finset.mem_Icc.mp (mem_odds.mp hyO).1).1
    rcases hadj with h | h | h
    · -- `x + y ∈ S`: `y = |x - (x + y)|`.
      rw [Finset.mem_union]
      refine Or.inr (Finset.mem_image.mpr ⟨x + y, h, ?_⟩)
      show |x - (x + y)| = y
      rw [show x - (x + y) = -y by ring, abs_neg]
      exact abs_of_nonneg (by omega)
    · -- `x - y ∈ S`: `y = |x - (x - y)|`.
      rw [Finset.mem_union]
      refine Or.inr (Finset.mem_image.mpr ⟨x - y, h, ?_⟩)
      show |x - (x - y)| = y
      rw [show x - (x - y) = y by ring]
      exact abs_of_nonneg (by omega)
    · -- `y - x ∈ S`: `y = x + (y - x)`.
      rw [Finset.mem_union]
      exact Or.inl (Finset.mem_image.mpr ⟨y - x, h, by
        show x + (y - x) = y; ring⟩)
  calc (linkNbrs S (odds n) x).card
      ≤ (S.image (fun s => x + s) ∪ S.image (fun s => |x - s|)).card :=
        Finset.card_le_card hsub
    _ ≤ (S.image (fun s => x + s)).card +
          (S.image (fun s => |x - s|)).card :=
        Finset.card_union_le _ _
    _ ≤ S.card + S.card :=
        add_le_add Finset.card_image_le Finset.card_image_le
    _ = 2 * S.card := by ring

/-- `deg(x) ≤ 2|S| + 2` for `x ∈ O`. -/
theorem deg_le_two_mul_add {n : ℕ} {S : Finset ℤ} {x : ℤ}
    (hx : x ∈ odds n) :
    (linkNbrs S (odds n) x).card ≤ 2 * S.card + 2 :=
  (linkNbrs_card_le_two_mul hx).trans (by omega)

/-- **Lower degree bound.**  For `x ∈ odds n` and `S ⊆ {1,…,n}` all-even,
every `s ∈ S` produces the neighbour `|x - s| ∈ O` (it is odd, and lies in
`[1, n]` since `s ≠ x` by parity and both are in `[1, n]`): if `s < x` then
`x - s` is a difference-neighbour, and if `s > x` then `s - x` is a
sum-neighbour.  Each neighbour `y` arises from at most two values of `s`
(namely `x + y` and `x - y`), so `|S| ≤ 2·deg(x)`. -/
theorem deg_lo_le {n : ℕ} {S : Finset ℤ} {x : ℤ}
    (hx : x ∈ odds n) (hS : S ⊆ interval n) (hEven : ∀ s ∈ S, Even s) :
    S.card ≤ 2 * (linkNbrs S (odds n) x).card := by
  have hxI := Finset.mem_Icc.mp (mem_odds.mp hx).1
  have hxpar := (mem_odds.mp hx).2
  -- Every `s ∈ S` maps to a genuine neighbour `|x - s| ∈ O`.
  have him : S.image (fun s => |x - s|) ⊆ linkNbrs S (odds n) x := by
    intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨s, hs, rfl⟩ := hy
    have hsI := Finset.mem_Icc.mp (hS hs)
    have hspar : s % 2 = 0 := Int.even_iff.mp (hEven s hs)
    have hne : s ≠ x := by omega
    show |x - s| ∈ linkNbrs S (odds n) x
    rw [linkNbrs, Finset.mem_filter]
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · -- `s < x`: neighbour `x - s` via the difference `x - (x - s) = s`.
      have habs : |x - s| = x - s := abs_of_pos (by omega)
      rw [habs]
      refine ⟨mem_odds.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩,
          by omega⟩, ?_⟩
      exact Or.inr (Or.inl (by rwa [show x - (x - s) = s by ring]))
    · -- `s > x`: neighbour `s - x` via the sum `x + (s - x) = s`.
      have habs : |x - s| = s - x := by
        rw [abs_of_neg (by omega : x - s < 0)]; ring
      rw [habs]
      refine ⟨mem_odds.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩,
          by omega⟩, ?_⟩
      exact Or.inl (by rwa [show x + (s - x) = s by ring])
  -- Each neighbour `y` has at most two preimages: `s = x + y` or `x - y`.
  have hfib : ∀ y ∈ S.image (fun s => |x - s|),
      (S.filter fun s => |x - s| = y).card ≤ 2 := by
    intro y hy
    have hsub : S.filter (fun s => |x - s| = y) ⊆ {x - y, x + y} := by
      intro s hs
      rw [Finset.mem_filter] at hs
      obtain ⟨-, habs⟩ := hs
      rcases eq_or_eq_neg_of_abs_eq habs with h | h
      · rw [Finset.mem_insert, Finset.mem_singleton]
        exact Or.inl (by omega)
      · rw [Finset.mem_insert, Finset.mem_singleton]
        exact Or.inr (by omega)
    calc (S.filter fun s => |x - s| = y).card
        ≤ ({x - y, x + y} : Finset ℤ).card := Finset.card_le_card hsub
      _ ≤ 2 := by
          have h := Finset.card_insert_le (x - y) ({x + y} : Finset ℤ)
          rw [Finset.card_singleton] at h
          exact h
  calc S.card
      ≤ 2 * (S.image fun s => |x - s|).card :=
        Finset.card_le_mul_card_image (f := fun s => |x - s|) S 2 hfib
    _ ≤ 2 * (linkNbrs S (odds n) x).card :=
        Nat.mul_le_mul (le_refl 2) (Finset.card_le_card him)

end JSP000728
