import JSPProblem.LinkGraph

/-!
# JSP-000728 — the link graph on the upper half is triangle-free

For a sum-free fingerprint `S ⊆ [1, n]`, the link graph `L_S` restricted to
the *upper half* `(n/2, ∞)` is triangle-free.  The reason is structural:

* on the upper half a sum `x + y` exceeds `n`, hence lies outside `S`, so
  every link edge is a *difference* edge;
* a negative-oriented difference `x − y` with `x < y` is `< 0`, hence
  outside `S` too, so the edge `x ~ y` is witnessed by the positive
  difference `|x − y| ∈ S`;
* for `x < y < z` the three differences `y − x`, `z − y`, `z − x` would all
  lie in `S`, and `(y − x) + (z − y) = z − x` is a Schur triple inside
  `S` — contradicting `IsSumFree S`.

Main statements:

* `linkAdj_not_triangle_ordered` — the ordered case `x < y < z`.
* `linkAdj_not_triangle_of_isSumFree` — three pairwise distinct integers
  in the upper half never form a link triangle (the six orderings reduce
  to the ordered case by symmetry of `linkAdj`).
* `linkTriangleFree` — the same statement packaged over a ground set `B`
  all of whose elements exceed `n/2`.
* `linkTriangleFree_Icc` — the concrete ground set `B = {⌊n/2⌋+1, …, n}`.
* `linkAdj_not_adj_of_common_neighbour` — in the upper half the
  link-neighbourhood of a vertex is link-independent.

This triangle-freeness is the hypothesis of the Hujter–Tuza bound
`mi(G) ≤ 2^{|G|/2}` for the number of maximal independent sets of a
triangle-free graph — the mechanism behind the `2^{n/4 + o(n)}` upper
bound on maximal sum-free sets.
-/

namespace JSP000728

/-- **Ordered case.**  For `S ⊆ [1, n]` (pointwise) sum-free and
`x < y < z` in the upper half (`n < 2·`), the three vertices do not form
a link triangle: each edge is forced to be a positive-difference edge,
and the differences `y − x`, `z − y`, `z − x ∈ S` satisfy
`(y − x) + (z − y) = z − x`, a Schur triple inside `S`. -/
theorem linkAdj_not_triangle_ordered {S : Finset ℤ} {n x y z : ℤ}
    (hS : ∀ a ∈ S, 1 ≤ a ∧ a ≤ n) (hSf : IsSumFree S)
    (hx : n < 2 * x) (hy : n < 2 * y) (hz : n < 2 * z)
    (hxy : x < y) (hyz : y < z) :
    ¬ (linkAdj S x y ∧ linkAdj S y z ∧ linkAdj S x z) := by
  -- Sums lie above `S`: `x + y > n ≥ a` for every `a ∈ S`.
  have hxyS : x + y ∉ S := fun h => by
    obtain ⟨-, hle⟩ := hS _ h; omega
  have hyzS : y + z ∉ S := fun h => by
    obtain ⟨-, hle⟩ := hS _ h; omega
  have hxzS : x + z ∉ S := fun h => by
    obtain ⟨-, hle⟩ := hS _ h; omega
  -- Negative-oriented differences lie below `S`: `x − y < 0 < 1 ≤ a`.
  have hxyS' : x - y ∉ S := fun h => by
    obtain ⟨hge, -⟩ := hS _ h; omega
  have hyzS' : y - z ∉ S := fun h => by
    obtain ⟨hge, -⟩ := hS _ h; omega
  have hxzS' : x - z ∉ S := fun h => by
    obtain ⟨hge, -⟩ := hS _ h; omega
  rintro ⟨hxyL, hyzL, hxzL⟩
  -- Each adjacency collapses to the positive difference.
  have dxy : y - x ∈ S := by
    rcases hxyL with h | h | h
    · exact absurd h hxyS
    · exact absurd h hxyS'
    · exact h
  have dyz : z - y ∈ S := by
    rcases hyzL with h | h | h
    · exact absurd h hyzS
    · exact absurd h hyzS'
    · exact h
  have dxz : z - x ∈ S := by
    rcases hxzL with h | h | h
    · exact absurd h hxzS
    · exact absurd h hxzS'
    · exact h
  -- `(y − x) + (z − y) = z − x` is a Schur triple inside `S`.
  have hno := hSf (y - x) dxy (z - y) dyz
  have e : y - x + (z - y) = z - x := by ring
  rw [e] at hno
  exact hno dxz

/-- **The link graph on the upper half is triangle-free.**  For
`S ⊆ [1, n]` sum-free, three pairwise distinct integers `x, y, z` with
`n < 2x`, `n < 2y`, `n < 2z` never form a triangle in `L_S`: sorting them
reduces to `linkAdj_not_triangle_ordered`, the triangle edge set being
invariant under relabelling up to `linkAdj_comm`. -/
theorem linkAdj_not_triangle_of_isSumFree {S : Finset ℤ} {n x y z : ℤ}
    (hS : ∀ a ∈ S, 1 ≤ a ∧ a ≤ n) (hSf : IsSumFree S)
    (hx : n < 2 * x) (hy : n < 2 * y) (hz : n < 2 * z)
    (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) :
    ¬ (linkAdj S x y ∧ linkAdj S y z ∧ linkAdj S x z) := by
  rcases lt_or_gt_of_ne hxy with hxy' | hxy'
  · rcases lt_or_gt_of_ne hyz with hyz' | hyz'
    · -- x < y < z
      exact linkAdj_not_triangle_ordered hS hSf hx hy hz hxy' hyz'
    · rcases lt_or_gt_of_ne hxz with hxz' | hxz'
      · -- x < z < y
        exact fun h =>
          linkAdj_not_triangle_ordered hS hSf hx hz hy hxz' hyz'
            ⟨h.2.2, linkAdj_comm.mp h.2.1, h.1⟩
      · -- z < x < y
        exact fun h =>
          linkAdj_not_triangle_ordered hS hSf hz hx hy hxz' hxy'
            ⟨linkAdj_comm.mp h.2.2, h.1, linkAdj_comm.mp h.2.1⟩
  · rcases lt_or_gt_of_ne hyz with hyz' | hyz'
    · rcases lt_or_gt_of_ne hxz with hxz' | hxz'
      · -- y < x < z
        exact fun h =>
          linkAdj_not_triangle_ordered hS hSf hy hx hz hxy' hxz'
            ⟨linkAdj_comm.mp h.1, h.2.2, h.2.1⟩
      · -- y < z < x
        exact fun h =>
          linkAdj_not_triangle_ordered hS hSf hy hz hx hyz' hxz'
            ⟨h.2.1, linkAdj_comm.mp h.2.2, linkAdj_comm.mp h.1⟩
    · -- z < y < x
      exact fun h =>
        linkAdj_not_triangle_ordered hS hSf hz hy hx hyz' hxy'
          ⟨linkAdj_comm.mp h.2.1, linkAdj_comm.mp h.1,
            linkAdj_comm.mp h.2.2⟩

/-- **Packaged form.**  Inside a ground set `B` all of whose elements lie
in the upper half `(n/2, ∞)`, no three distinct vertices form a triangle
of the link graph `L_S` when `S ⊆ [1, n]` is sum-free. -/
theorem linkTriangleFree {S B : Finset ℤ} {n : ℤ}
    (hS : S ⊆ Finset.Icc 1 n) (hSf : IsSumFree S)
    (hB : ∀ x ∈ B, n < 2 * x) :
    ∀ x ∈ B, ∀ y ∈ B, ∀ z ∈ B, x ≠ y → y ≠ z → x ≠ z →
      ¬ (linkAdj S x y ∧ linkAdj S y z ∧ linkAdj S x z) :=
  fun x hx y hy z hz hxy hyz hxz =>
    linkAdj_not_triangle_of_isSumFree
      (fun _a ha => Finset.mem_Icc.mp (hS ha)) hSf
      (hB x hx) (hB y hy) (hB z hz) hxy hyz hxz

/-- The same packaged statement with pointwise bounds on `S`. -/
theorem linkTriangleFree' {S B : Finset ℤ} {n : ℤ}
    (hS : ∀ a ∈ S, 1 ≤ a ∧ a ≤ n) (hSf : IsSumFree S)
    (hB : ∀ x ∈ B, n < 2 * x) :
    ∀ x ∈ B, ∀ y ∈ B, ∀ z ∈ B, x ≠ y → y ≠ z → x ≠ z →
      ¬ (linkAdj S x y ∧ linkAdj S y z ∧ linkAdj S x z) :=
  fun x hx y hy z hz hxy hyz hxz =>
    linkAdj_not_triangle_of_isSumFree hS hSf
      (hB x hx) (hB y hy) (hB z hz) hxy hyz hxz

/-- **Concrete ground set.**  On `B = {⌊n/2⌋ + 1, …, n}` the link graph
of a sum-free `S ⊆ [1, n]` has no triangle. -/
theorem linkTriangleFree_Icc {S : Finset ℤ} {n : ℤ}
    (hS : S ⊆ Finset.Icc 1 n) (hSf : IsSumFree S) :
    ∀ x ∈ Finset.Icc (n / 2 + 1) n, ∀ y ∈ Finset.Icc (n / 2 + 1) n,
      ∀ z ∈ Finset.Icc (n / 2 + 1) n, x ≠ y → y ≠ z → x ≠ z →
        ¬ (linkAdj S x y ∧ linkAdj S y z ∧ linkAdj S x z) := by
  intro x hx y hy z hz hxy hyz hxz
  obtain ⟨hx1, -⟩ := Finset.mem_Icc.mp hx
  obtain ⟨hy1, -⟩ := Finset.mem_Icc.mp hy
  obtain ⟨hz1, -⟩ := Finset.mem_Icc.mp hz
  exact linkAdj_not_triangle_of_isSumFree
    (fun _a ha => Finset.mem_Icc.mp (hS ha)) hSf
    (by omega) (by omega) (by omega) hxy hyz hxz

/-- **Neighbourhoods are independent.**  In the upper half, two distinct
link-neighbours `v, w` of a common vertex `u` are never adjacent — the
link-neighbourhood `N(u)` is a link-independent set. -/
theorem linkAdj_not_adj_of_common_neighbour {S : Finset ℤ} {n u v w : ℤ}
    (hS : ∀ a ∈ S, 1 ≤ a ∧ a ≤ n) (hSf : IsSumFree S)
    (hu : n < 2 * u) (hv : n < 2 * v) (hw : n < 2 * w)
    (huv : u ≠ v) (hvw : v ≠ w) (huw : u ≠ w)
    (h1 : linkAdj S u v) (h2 : linkAdj S u w) : ¬ linkAdj S v w :=
  fun h3 =>
    linkAdj_not_triangle_of_isSumFree hS hSf hu hv hw huv hvw huw
      ⟨h1, h3, h2⟩

end JSP000728
