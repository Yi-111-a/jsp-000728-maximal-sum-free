import JSPProblem.Basic
import JSPProblem.Obstruction
import JSPProblem.MinDecomp
import JSPProblem.DeterminedMinClass
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Int.Interval
import Mathlib.Data.Nat.Fib.Basic

/-!
# JSP-000728 — the Wolfovitz link graph

For a fixed sum-free *fingerprint* `S` the link graph `L_S` has edges
`x ~ y` iff some `z ∈ S` completes `{x, y, z}` to a Schur triple —
concretely `x + y ∈ S` or `x − y ∈ S` or `y − x ∈ S` (`linkAdj`) — and a
loop at `x` when `x` alone already clashes with `S`: `x` is a sum of two
elements of `S` (`∃ z ∈ S, x − z ∈ S`), `x` translates an element of `S`
into `S` (`∃ z ∈ S, x + z ∈ S`), or `x + x ∈ S` (`linkLoop`).  These are
exactly the four obstruction types of `IsSumFree.insert_iff`
(`linkLoop_iff_not_isSumFree_insert`).

Correctness layer:

* `linkIndepSet_of_isSumFree` — inside a sum-free `M`, every `t ⊆ M` is
  link-independent w.r.t. every `S ⊆ M`.
* `isSumFree_union_iff_linkIndepSet` — under the separation `S ⊆ [1, K]`,
  `t ⊆ (K, ∞)`, `S ∪ t` is sum-free iff `S` is sum-free, `t` is sum-free,
  and `t` is link-independent.  (Link-independence alone does not suffice:
  a Schur triple lying entirely inside `t` is not a link edge, and a sum
  `u + v` of two `S`-elements landing in `t` is a *loop*, not an edge.)
* `linkMax_indep_of_isMaxSumFree` — for `M` maximal sum-free, `B = {K+1,…,n}`
  and `S = M ∩ [1,K]`, the trace `M ∩ B` is a *maximal* link-independent
  subset of `B`, provided `B` is itself sum-free (automatic when
  `n < 2(K+1)`, see `linkMax_indep_of_isMaxSumFree_of_lt`).  The hypothesis
  is necessary: an obstruction `x = a + b` or `a + x = w` with `a, b, w ∈ t`
  is a Schur triple on the `t`-side, not a link edge or loop.

Counting layer:

* `minClass_card_le_sum_linkSets` — `M ↦ (M ∩ [1,K], M ∩ {K+1,…,n})`
  injects `minClass n m` into fingerprint/link-independent pairs, giving
  `|minClass n m| ≤ Σ_{S ⊆ [1,K]} |linkSets S {K+1,…,n}|`.
* `minClass_card_le_two_pow_mul_linkSets` — the `2^K · (max |linkSets|)`
  form.
* `minClass_card_le_sum_linkMaxSets` — the same bound through *maximal*
  link-independent sets, valid when `n < 2(K+1)`.
* Stretch sanity check: `linkIndepSet {m}` implies `shiftFree m`, so
  `card_linkSets_singleton_Icc_le_prod_fib` recovers the determined
  Fibonacci-product bound of `minClass_card_le_prod_fib` for the singleton
  fingerprint `S = {m}`.
-/

namespace JSP000728

/-! ## The link relation -/

/-- **Link-graph adjacency.**  `x ~ y` in `L_S` iff some `z ∈ S` completes
`{x, y, z}` to a Schur triple: `x + y ∈ S`, `x − y ∈ S`, or `y − x ∈ S`. -/
def linkAdj (S : Finset ℤ) (x y : ℤ) : Prop :=
  x + y ∈ S ∨ x - y ∈ S ∨ y - x ∈ S

instance decidableLinkAdj (S : Finset ℤ) (x y : ℤ) :
    Decidable (linkAdj S x y) := by
  unfold linkAdj; infer_instance

/-- Adjacency is symmetric. -/
theorem linkAdj_comm {S : Finset ℤ} {x y : ℤ} :
    linkAdj S x y ↔ linkAdj S y x := by
  constructor
  · rintro (h | h | h)
    · exact Or.inl (add_comm x y ▸ h)
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)
  · rintro (h | h | h)
    · exact Or.inl (add_comm y x ▸ h)
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)

/-- **Link-graph loop.**  `x` carries a loop when `x` alone already clashes
with `S`: `x` is a sum of two elements of `S` (`∃ z ∈ S, x − z ∈ S`), `x`
translates an element of `S` into `S` (`∃ z ∈ S, x + z ∈ S`), or
`x + x ∈ S`.  For positive `x` and positive `S` this is exactly
`¬ IsSumFree (insert x S)`, see `linkLoop_iff_not_isSumFree_insert`. -/
def linkLoop (S : Finset ℤ) (x : ℤ) : Prop :=
  (∃ z ∈ S, x - z ∈ S) ∨ (∃ z ∈ S, x + z ∈ S) ∨ x + x ∈ S

instance decidableLinkLoop (S : Finset ℤ) (x : ℤ) :
    Decidable (linkLoop S x) := by
  unfold linkLoop; infer_instance

/-- The loop predicate is exactly the obstruction to adjoining `x` to `S`:
the four cases of `IsSumFree.insert_iff` reorganised — `a + b = x` is
`x − a = b`, and `a + x`/`x + a` coalesce by commutativity. -/
theorem linkLoop_iff_not_isSumFree_insert {S : Finset ℤ} {x : ℤ}
    (hSf : IsSumFree S) (hx : 0 < x) (hpos : ∀ a ∈ S, 0 < a) :
    linkLoop S x ↔ ¬ IsSumFree (insert x S) := by
  rw [hSf.insert_iff hx hpos]
  constructor
  · rintro (⟨z, hz, hxz⟩ | ⟨z, hz, hxz⟩ | hxx) ⟨-, h2, -, h4, h5⟩
    · exact h2 z hz (x - z) hxz (by ring)
    · exact h4 z hz hxz
    · exact h5 hxx
  · intro hnot
    have hnot' : ¬ ((∀ a ∈ S, ∀ b ∈ S, a + b ≠ x) ∧ (∀ a ∈ S, a + x ∉ S) ∧
        (∀ a ∈ S, x + a ∉ S) ∧ (x + x ∉ S)) :=
      fun hb => hnot ⟨hSf, hb⟩
    by_cases h2 : ∃ z ∈ S, x - z ∈ S
    · exact Or.inl h2
    by_cases h3 : ∃ z ∈ S, x + z ∈ S
    · exact Or.inr (Or.inl h3)
    refine Or.inr (Or.inr ?_)
    by_contra hxx
    refine hnot' ⟨?_, ?_, ?_, hxx⟩
    · intro a ha b hb hab
      refine h2 ⟨a, ha, ?_⟩
      have e : x - a = b := by omega
      rwa [e]
    · intro a ha hax
      exact h3 ⟨a, ha, by rwa [add_comm x a]⟩
    · intro a ha hxa
      exact h3 ⟨a, ha, hxa⟩

/-- `t` is *link-independent* w.r.t. `S`: no vertex of `t` carries a loop
and no two (not necessarily distinct) vertices of `t` are adjacent. -/
def linkIndepSet (S t : Finset ℤ) : Prop :=
  (∀ x ∈ t, ¬ linkLoop S x) ∧ ∀ x ∈ t, ∀ y ∈ t, ¬ linkAdj S x y

instance decidableLinkIndepSet (S t : Finset ℤ) :
    Decidable (linkIndepSet S t) := by
  unfold linkIndepSet; infer_instance

/-- `t` is a *maximal link-independent* subset of `B`: it is independent,
contained in `B`, and every `x ∈ B ∖ t` carries a loop or has an edge
into `t`. -/
def linkMaxIndepSet (S B t : Finset ℤ) : Prop :=
  t ⊆ B ∧ linkIndepSet S t ∧
    ∀ x ∈ B, x ∉ t → linkLoop S x ∨ ∃ y ∈ t, linkAdj S x y

instance decidableLinkMaxIndepSet (S B t : Finset ℤ) :
    Decidable (linkMaxIndepSet S B t) := by
  unfold linkMaxIndepSet; infer_instance

/-- The family of link-independent subsets of `B`. -/
def linkSets (S B : Finset ℤ) : Finset (Finset ℤ) :=
  B.powerset.filter (linkIndepSet S)

/-- The family of maximal link-independent subsets of `B`. -/
def linkMaxSets (S B : Finset ℤ) : Finset (Finset ℤ) :=
  B.powerset.filter (linkMaxIndepSet S B)

/-- Membership in `linkSets`: a subset of `B` with no link edge or loop. -/
theorem mem_linkSets {S B t : Finset ℤ} :
    t ∈ linkSets S B ↔ t ⊆ B ∧ linkIndepSet S t := by
  rw [linkSets, Finset.mem_filter, Finset.mem_powerset]

/-- Membership in `linkMaxSets`. -/
theorem mem_linkMaxSets {S B t : Finset ℤ} :
    t ∈ linkMaxSets S B ↔ t ⊆ B ∧ linkMaxIndepSet S B t := by
  rw [linkMaxSets, Finset.mem_filter, Finset.mem_powerset]

/-- `linkSets S B` is a subfamily of the powerset. -/
theorem linkSets_subset_powerset (S B : Finset ℤ) :
    linkSets S B ⊆ B.powerset :=
  Finset.filter_subset _ _

/-- Coarse bound `|linkSets S B| ≤ 2^{|B|}`. -/
theorem card_linkSets_le (S B : Finset ℤ) :
    (linkSets S B).card ≤ 2 ^ B.card := by
  calc (linkSets S B).card
      ≤ B.powerset.card := Finset.card_le_card (linkSets_subset_powerset S B)
    _ = 2 ^ B.card := Finset.card_powerset _

/-! ## Correctness -/

/-- **Sum-free ⇒ link-independent.**  Inside a sum-free `M`, every `t ⊆ M`
is link-independent w.r.t. every `S ⊆ M`: a loop or an edge inside `t`
would exhibit a Schur triple inside `M`. -/
theorem linkIndepSet_of_isSumFree {M S t : Finset ℤ} (hM : IsSumFree M)
    (hS : S ⊆ M) (ht : t ⊆ M) : linkIndepSet S t := by
  refine ⟨fun x hx => ?_, fun x hx y hy => ?_⟩
  · rintro (⟨z, hz, hxz⟩ | ⟨z, hz, hxz⟩ | hxx)
    · -- `z + (x − z) = x` is a Schur triple in `M`.
      have hno := hM z (hS hz) (x - z) (hS hxz)
      have e : z + (x - z) = x := by ring
      rw [e] at hno
      exact hno (ht hx)
    · exact hM x (ht hx) z (hS hz) (hS hxz)
    · exact hM x (ht hx) x (ht hx) (hS hxx)
  · rintro (h | h | h)
    · exact hM x (ht hx) y (ht hy) (hS h)
    · -- `(x − y) + y = x` is a Schur triple in `M`.
      have hno := hM (x - y) (hS h) y (ht hy)
      have e : x - y + y = x := by ring
      rw [e] at hno
      exact hno (ht hx)
    · have hno := hM (y - x) (hS h) x (ht hx)
      have e : y - x + x = y := by ring
      rw [e] at hno
      exact hno (ht hy)

/-- **Union correctness.**  With `S ⊆ [1, K]` sum-free and `t ⊆ (K, ∞)`
sum-free and link-independent, `S ∪ t` is sum-free.  Of the four
obstruction shapes for `S ∪ t`: sums inside `S` or `t` are handled by
sum-freeness; a sum of two `S`-elements landing in `t` is a loop at the
sum; a mixed sum `s + x` landing in `t` is a difference edge
`x ~ s + x`; and every sum involving an element of `t` is `> K`, hence
outside `S`. -/
theorem isSumFree_union_of_linkIndepSet {S t : Finset ℤ} {K : ℤ}
    (hK : 0 ≤ K) (hS : S ⊆ Finset.Icc 1 K) (hSf : IsSumFree S)
    (ht : IsSumFree t) (htK : ∀ x ∈ t, K < x)
    (hli : linkIndepSet S t) :
    IsSumFree (S ∪ t) := by
  intro u hu v hv huv
  rw [Finset.mem_union] at hu hv huv
  rcases hu with hu | hu <;> rcases hv with hv | hv <;>
    rcases huv with huv | huv
  · -- `u, v ∈ S`, `u + v ∈ S`: sum-freeness of `S`.
    exact hSf u hu v hv huv
  · -- `u, v ∈ S`, `u + v ∈ t`: loop at `u + v` via `z = u`.
    have hmem : u + v - u ∈ S := by
      have e : u + v - u = v := by ring
      rwa [e]
    exact hli.1 (u + v) huv (Or.inl ⟨u, hu, hmem⟩)
  · -- `u ∈ S`, `v ∈ t`, `u + v ∈ S`: impossible, `u + v > K`.
    obtain ⟨hu1, -⟩ := Finset.mem_Icc.mp (hS hu)
    obtain ⟨-, huv2⟩ := Finset.mem_Icc.mp (hS huv)
    have hvK := htK v hv
    omega
  · -- `u ∈ S`, `v ∈ t`, `u + v ∈ t`: difference edge `v ~ u + v`.
    have hmem : u + v - v ∈ S := by
      have e : u + v - v = u := by ring
      rwa [e]
    exact hli.2 v hv (u + v) huv (Or.inr (Or.inr hmem))
  · -- `u ∈ t`, `v ∈ S`, `u + v ∈ S`: impossible, `u + v > K`.
    obtain ⟨hv1, -⟩ := Finset.mem_Icc.mp (hS hv)
    obtain ⟨-, huv2⟩ := Finset.mem_Icc.mp (hS huv)
    have huK := htK u hu
    omega
  · -- `u ∈ t`, `v ∈ S`, `u + v ∈ t`: difference edge `u ~ u + v`.
    have hmem : u + v - u ∈ S := by
      have e : u + v - u = v := by ring
      rwa [e]
    exact hli.2 u hu (u + v) huv (Or.inr (Or.inr hmem))
  · -- `u, v ∈ t`, `u + v ∈ S`: impossible, `u + v > 2K ≥ K`.
    obtain ⟨-, huv2⟩ := Finset.mem_Icc.mp (hS huv)
    have huK := htK u hu
    have hvK := htK v hv
    omega
  · -- `u, v ∈ t`, `u + v ∈ t`: sum-freeness of `t`.
    exact ht u hu v hv huv

/-- **Exact characterisation.**  Under the separation `S ⊆ [1, K]` and
`t ⊆ (K, ∞)`, sum-freeness of `S ∪ t` is equivalent to `S` sum-free,
`t` sum-free, and `t` link-independent. -/
theorem isSumFree_union_iff_linkIndepSet {S t : Finset ℤ} {K : ℤ}
    (hK : 0 ≤ K) (hS : S ⊆ Finset.Icc 1 K) (htK : ∀ x ∈ t, K < x) :
    IsSumFree (S ∪ t) ↔
      IsSumFree S ∧ IsSumFree t ∧ linkIndepSet S t := by
  constructor
  · intro h
    exact ⟨h.mono Finset.subset_union_left, h.mono Finset.subset_union_right,
      linkIndepSet_of_isSumFree h Finset.subset_union_left
        Finset.subset_union_right⟩
  · rintro ⟨hSf, ht, hli⟩
    exact isSumFree_union_of_linkIndepSet hK hS hSf ht htK hli

/-- **Maximality transfers to the link graph** — under the side conditions
`0 ≤ K` and that `B = {K+1,…,n}` is itself sum-free.  For `M` maximal
sum-free in `{1,…,n}` with fingerprint `S = M ∩ [1,K]`, every `x ∈ B ∖ M`
is obstructed; the obstruction `a + b = x` or `a + x`/`x + a ∈ M` lands in
`S` (loop), across `S` and `t = M ∩ B` (edge), or has both entries in
`t ⊆ B`, which `IsSumFree B` rules out — as does `x + x ∈ B`. -/
theorem linkMax_indep_of_isMaxSumFree {n : ℕ} {M : Finset ℤ} {K : ℤ}
    (hM : IsMaxSumFree n M) (hK : 0 ≤ K)
    (hBB : IsSumFree (Finset.Icc (K + 1) (n : ℤ))) :
    linkMaxIndepSet (M ∩ Finset.Icc 1 K) (Finset.Icc (K + 1) (n : ℤ))
      (M ∩ Finset.Icc (K + 1) (n : ℤ)) := by
  refine ⟨Finset.inter_subset_right,
    linkIndepSet_of_isSumFree hM.2.1 Finset.inter_subset_left
      Finset.inter_subset_left, ?_⟩
  intro x hxB hxt
  have hxn : x ∈ interval n := by
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hxB
    exact Finset.mem_Icc.mpr ⟨by omega, h2⟩
  have hxM : x ∉ M := fun h => hxt (Finset.mem_inter.mpr ⟨h, hxB⟩)
  -- Every element of `M` is in the fingerprint `M ∩ [1,K]` or the trace
  -- `M ∩ {K+1,…,n}`.
  have hd : ∀ a ∈ M, a ∈ M ∩ Finset.Icc 1 K ∨
      a ∈ M ∩ Finset.Icc (K + 1) (n : ℤ) := by
    intro a ha
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp (hM.1 ha)
    by_cases haK : a ≤ K
    · exact Or.inl (Finset.mem_inter.mpr ⟨ha, Finset.mem_Icc.mpr ⟨h1, haK⟩⟩)
    · refine Or.inr (Finset.mem_inter.mpr ⟨ha, Finset.mem_Icc.mpr ⟨?_, h2⟩⟩)
      omega
  rcases hM.exists_obstruction hxn hxM with hsum | hax | hxa | hxx
  · obtain ⟨a, ha, b, hb, hab⟩ := hsum
    rcases hd a ha with haS | hat <;> rcases hd b hb with hbS | hbt
    · -- `a, b` in the fingerprint: `x = a + b` is a loop at `x`.
      refine Or.inl (Or.inl ⟨a, haS, ?_⟩)
      have e : x - a = b := by omega
      rwa [e]
    · -- `a ∈` fingerprint, `b ∈` trace: difference edge `x ~ b`.
      refine Or.inr ⟨b, hbt, Or.inr (Or.inl ?_)⟩
      have e : x - b = a := by omega
      rwa [e]
    · -- `a ∈` trace, `b ∈` fingerprint: difference edge `x ~ a`.
      refine Or.inr ⟨a, hat, Or.inr (Or.inl ?_)⟩
      have e : x - a = b := by omega
      rwa [e]
    · -- `a, b ∈` trace `⊆ B`: `a + b = x ∈ B` contradicts `IsSumFree B`.
      have hmem : a + b ∈ Finset.Icc (K + 1) (n : ℤ) := hab ▸ hxB
      exact absurd hmem (hBB a (Finset.mem_inter.mp hat).2
        b (Finset.mem_inter.mp hbt).2)
  · obtain ⟨a, ha, hax⟩ := hax
    have haxB : a + x ∈ Finset.Icc (K + 1) (n : ℤ) := by
      obtain ⟨hax1, hax2⟩ := Finset.mem_Icc.mp (hM.1 hax)
      obtain ⟨ha1, -⟩ := Finset.mem_Icc.mp (hM.1 ha)
      obtain ⟨hx1, -⟩ := Finset.mem_Icc.mp hxB
      exact Finset.mem_Icc.mpr ⟨by omega, hax2⟩
    have haxt : a + x ∈ M ∩ Finset.Icc (K + 1) (n : ℤ) :=
      Finset.mem_inter.mpr ⟨hax, haxB⟩
    rcases hd a ha with haS | hat
    · -- `a ∈` fingerprint: difference edge `x ~ a + x`.
      refine Or.inr ⟨a + x, haxt, Or.inr (Or.inr ?_)⟩
      have e : a + x - x = a := by ring
      rwa [e]
    · -- `a ∈` trace: `a + x ∈ t ⊆ B` contradicts `IsSumFree B`.
      exact absurd haxB (hBB a (Finset.mem_inter.mp hat).2 x hxB)
  · obtain ⟨a, ha, hxa⟩ := hxa
    have hxaB : x + a ∈ Finset.Icc (K + 1) (n : ℤ) := by
      obtain ⟨hxa1, hxa2⟩ := Finset.mem_Icc.mp (hM.1 hxa)
      obtain ⟨ha1, -⟩ := Finset.mem_Icc.mp (hM.1 ha)
      obtain ⟨hx1, -⟩ := Finset.mem_Icc.mp hxB
      exact Finset.mem_Icc.mpr ⟨by omega, hxa2⟩
    have hxat : x + a ∈ M ∩ Finset.Icc (K + 1) (n : ℤ) :=
      Finset.mem_inter.mpr ⟨hxa, hxaB⟩
    rcases hd a ha with haS | hat
    · refine Or.inr ⟨x + a, hxat, Or.inr (Or.inr ?_)⟩
      have e : x + a - x = a := by ring
      rwa [e]
    · exact absurd hxaB (hBB x hxB a (Finset.mem_inter.mp hat).2)
  · -- `x + x ∈ M ⊆ B` contradicts `IsSumFree B`.
    have hxxB : x + x ∈ Finset.Icc (K + 1) (n : ℤ) := by
      obtain ⟨hxx1, hxx2⟩ := Finset.mem_Icc.mp (hM.1 hxx)
      obtain ⟨hx1, -⟩ := Finset.mem_Icc.mp hxB
      exact Finset.mem_Icc.mpr ⟨by omega, hxx2⟩
    exact absurd hxxB (hBB x hxB x hxB)

/-- **Maximality transfers unconditionally when `n < 2(K+1)`:** then
`B = {K+1,…,n}` is automatically sum-free, so the trace `M ∩ B` is a
maximal link-independent set of the link graph `L_{M ∩ [1,K]}[B]`. -/
theorem linkMax_indep_of_isMaxSumFree_of_lt {n : ℕ} {M : Finset ℤ} {K : ℤ}
    (hM : IsMaxSumFree n M) (hK : (n : ℤ) < 2 * (K + 1)) :
    linkMaxIndepSet (M ∩ Finset.Icc 1 K) (Finset.Icc (K + 1) (n : ℤ))
      (M ∩ Finset.Icc (K + 1) (n : ℤ)) := by
  have hK0 : 0 ≤ K := by omega
  refine linkMax_indep_of_isMaxSumFree hM hK0 fun a ha b hb hmem => ?_
  obtain ⟨ha1, -⟩ := Finset.mem_Icc.mp ha
  obtain ⟨hb1, -⟩ := Finset.mem_Icc.mp hb
  obtain ⟨-, hle2⟩ := Finset.mem_Icc.mp hmem
  omega

/-! ## Counting -/

/-- Every `M ⊆ {1,…,n}` splits as `(M ∩ [1,K]) ∪ (M ∩ {K+1,…,n})`. -/
theorem inter_Icc_union_inter_Icc {n : ℕ} {M : Finset ℤ} {K : ℤ}
    (hM : M ⊆ interval n) :
    M ∩ Finset.Icc 1 K ∪ M ∩ Finset.Icc (K + 1) (n : ℤ) = M := by
  ext y
  simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_Icc]
  constructor
  · rintro (⟨hy, -, -⟩ | ⟨hy, -, -⟩) <;> exact hy
  · intro hy
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp (hM hy)
    by_cases hyK : y ≤ K
    · exact Or.inl ⟨hy, h1, hyK⟩
    · exact Or.inr ⟨hy, by omega, h2⟩

/-- **Counting through the link graph.**  Every `M ∈ minClass n m` splits
as `S ∪ t` with fingerprint `S = M ∩ [1,K]` and `t = M ∩ {K+1,…,n}` a
link-independent subset of `B`; the pair determines `M`, so the class size
is at most the total number of link-independent sets over all
fingerprints:
`|minClass n m| ≤ Σ_{S ⊆ [1,K]} |linkSets S {K+1,…,n}|`. -/
theorem minClass_card_le_sum_linkSets {n : ℕ} {m K : ℤ} :
    (minClass n m).card ≤
      ∑ S ∈ (Finset.Icc 1 K).powerset,
        (linkSets S (Finset.Icc (K + 1) (n : ℤ))).card := by
  classical
  have hsub : minClass n m ⊆ (Finset.Icc 1 K).powerset.biUnion
      fun S => (linkSets S (Finset.Icc (K + 1) (n : ℤ))).image (S ∪ ·) := by
    intro M hM
    rw [mem_minClass] at hM
    obtain ⟨hmax, -, -⟩ := hM
    have hMmax : IsMaxSumFree n M := mem_maxSumFreeSets.mp hmax
    rw [Finset.mem_biUnion]
    refine ⟨M ∩ Finset.Icc 1 K,
      Finset.mem_powerset.mpr Finset.inter_subset_right, ?_⟩
    rw [Finset.mem_image]
    refine ⟨M ∩ Finset.Icc (K + 1) (n : ℤ), ?_, ?_⟩
    · rw [mem_linkSets]
      exact ⟨Finset.inter_subset_right,
        linkIndepSet_of_isSumFree hMmax.2.1 Finset.inter_subset_left
          Finset.inter_subset_left⟩
    · show M ∩ Finset.Icc 1 K ∪ M ∩ Finset.Icc (K + 1) (n : ℤ) = M
      exact inter_Icc_union_inter_Icc hMmax.1
  calc (minClass n m).card
      ≤ ((Finset.Icc 1 K).powerset.biUnion
          fun S => (linkSets S (Finset.Icc (K + 1) (n : ℤ))).image
            (S ∪ ·)).card := Finset.card_le_card hsub
    _ ≤ ∑ S ∈ (Finset.Icc 1 K).powerset,
          ((linkSets S (Finset.Icc (K + 1) (n : ℤ))).image (S ∪ ·)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ S ∈ (Finset.Icc 1 K).powerset,
          (linkSets S (Finset.Icc (K + 1) (n : ℤ))).card :=
        Finset.sum_le_sum fun S _ => Finset.card_image_le

/-- **Fingerprint-times-max form.**  If every fingerprint `S ⊆ [1,K]` has
at most `C` link-independent subsets of `B = {K+1,…,n}`, then
`|minClass n m| ≤ 2^{K} · C`. -/
theorem minClass_card_le_two_pow_mul_linkSets {n : ℕ} {m K : ℤ} (C : ℕ)
    (hC : ∀ S ∈ (Finset.Icc 1 K).powerset,
      (linkSets S (Finset.Icc (K + 1) (n : ℤ))).card ≤ C) :
    (minClass n m).card ≤ 2 ^ K.toNat * C := by
  have e : (K : ℤ) + 1 - 1 = K := by ring
  calc (minClass n m).card
      ≤ ∑ S ∈ (Finset.Icc 1 K).powerset,
          (linkSets S (Finset.Icc (K + 1) (n : ℤ))).card :=
        minClass_card_le_sum_linkSets
    _ ≤ ∑ _S ∈ (Finset.Icc 1 K).powerset, C :=
        Finset.sum_le_sum fun S hS => hC S hS
    _ = (Finset.Icc 1 K).powerset.card * C := by
        rw [Finset.sum_const, smul_eq_mul]
    _ = 2 ^ K.toNat * C := by
        rw [Finset.card_powerset, Int.card_Icc, e]

/-- **Counting through maximal link-independent sets.**  When
`n < 2(K+1)` the ground set `B = {K+1,…,n}` is sum-free, so by
`linkMax_indep_of_isMaxSumFree_of_lt` the trace `M ∩ B` is even a
*maximal* link-independent set, and the class is counted by the smaller
family `linkMaxSets`:
`|minClass n m| ≤ Σ_{S ⊆ [1,K]} |linkMaxSets S {K+1,…,n}|`. -/
theorem minClass_card_le_sum_linkMaxSets {n : ℕ} {m K : ℤ}
    (hK : (n : ℤ) < 2 * (K + 1)) :
    (minClass n m).card ≤
      ∑ S ∈ (Finset.Icc 1 K).powerset,
        (linkMaxSets S (Finset.Icc (K + 1) (n : ℤ))).card := by
  classical
  have hsub : minClass n m ⊆ (Finset.Icc 1 K).powerset.biUnion
      fun S => (linkMaxSets S (Finset.Icc (K + 1) (n : ℤ))).image
        (S ∪ ·) := by
    intro M hM
    rw [mem_minClass] at hM
    obtain ⟨hmax, -, -⟩ := hM
    have hMmax : IsMaxSumFree n M := mem_maxSumFreeSets.mp hmax
    rw [Finset.mem_biUnion]
    refine ⟨M ∩ Finset.Icc 1 K,
      Finset.mem_powerset.mpr Finset.inter_subset_right, ?_⟩
    rw [Finset.mem_image]
    refine ⟨M ∩ Finset.Icc (K + 1) (n : ℤ), ?_, ?_⟩
    · rw [mem_linkMaxSets]
      exact ⟨Finset.inter_subset_right,
        linkMax_indep_of_isMaxSumFree_of_lt hMmax hK⟩
    · show M ∩ Finset.Icc 1 K ∪ M ∩ Finset.Icc (K + 1) (n : ℤ) = M
      exact inter_Icc_union_inter_Icc hMmax.1
  calc (minClass n m).card
      ≤ ((Finset.Icc 1 K).powerset.biUnion
          fun S => (linkMaxSets S (Finset.Icc (K + 1) (n : ℤ))).image
            (S ∪ ·)).card := Finset.card_le_card hsub
    _ ≤ ∑ S ∈ (Finset.Icc 1 K).powerset,
          ((linkMaxSets S (Finset.Icc (K + 1) (n : ℤ))).image
            (S ∪ ·)).card := Finset.card_biUnion_le
    _ ≤ ∑ S ∈ (Finset.Icc 1 K).powerset,
          (linkMaxSets S (Finset.Icc (K + 1) (n : ℤ))).card :=
        Finset.sum_le_sum fun S _ => Finset.card_image_le

/-- The Wolfovitz split at the complementary threshold `K = n − m`: for
`m ≤ (n+1)/2` the maximal link-independent counting bound applies,
`|minClass n m| ≤ Σ_{S ⊆ [1,n−m]} |linkMaxSets S {n−m+1,…,n}|`. -/
theorem minClass_card_le_sum_linkMaxSets_compl {n : ℕ} {m : ℤ}
    (hnm : (n : ℤ) < 2 * ((n : ℤ) - m + 1)) :
    (minClass n m).card ≤
      ∑ S ∈ (Finset.Icc 1 ((n : ℤ) - m)).powerset,
        (linkMaxSets S (Finset.Icc ((n : ℤ) - m + 1) (n : ℤ))).card :=
  minClass_card_le_sum_linkMaxSets hnm

/-! ## Stretch: the singleton fingerprint recovers the shift-free bound -/

/-- A link-independent set w.r.t. the singleton `{m}` is `m`-shift-free:
`x` and `x + m` are adjacent through the difference edge `m ∈ {m}`. -/
theorem shiftFree_of_linkIndepSet_singleton {m : ℤ} {t : Finset ℤ}
    (h : linkIndepSet {m} t) : shiftFree m t := by
  intro x hx hxm
  have hadj : linkAdj {m} x (x + m) := by
    refine Or.inr (Or.inr ?_)
    have e : x + m - x = m := by ring
    rw [e]
    exact Finset.mem_singleton_self m
  exact h.2 x hx (x + m) hxm hadj

/-- `linkSets {m} B` sits inside the `m`-shift-free subsets of `B`. -/
theorem linkSets_singleton_subset {m : ℤ} (B : Finset ℤ) :
    linkSets {m} B ⊆ B.powerset.filter (shiftFree m) := by
  intro t ht
  rw [mem_linkSets] at ht
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr ht.1, shiftFree_of_linkIndepSet_singleton ht.2⟩

/-- Cardinal form: `|linkSets {m} B|` is at most the number of
`m`-shift-free subsets of `B`. -/
theorem card_linkSets_singleton_le {m : ℤ} (B : Finset ℤ) :
    (linkSets {m} B).card ≤ (B.powerset.filter (shiftFree m)).card :=
  Finset.card_le_card (linkSets_singleton_subset B)

/-- **Fibonacci bound for a singleton fingerprint.**  `L_{m}`-independent
subsets of `{m+1,…,K}` are `m`-shift-free, hence counted by the per-rail
product `∏_{r=1}^{m} F_{⌊(K−r)/m⌋+2}` — recovering the determined bound
of `minClass_card_le_prod_fib` as the special case `S = {m}` (all edges
of `L_{m}` on `{m+1,…,K}` are difference edges `x ~ x + m`). -/
theorem card_linkSets_singleton_Icc_le_prod_fib {K m : ℤ} (hm : 1 ≤ m) :
    (linkSets {m} (Finset.Icc (m + 1) K)).card ≤
      ∏ r ∈ Finset.Icc 1 m, Nat.fib (((K - r) / m).toNat + 2) := by
  calc (linkSets {m} (Finset.Icc (m + 1) K)).card
      ≤ ((Finset.Icc (m + 1) K).powerset.filter (shiftFree m)).card :=
        card_linkSets_singleton_le _
    _ ≤ ∏ r ∈ Finset.Icc 1 m,
          ((prog m (r + m) (((K - r) / m).toNat)).powerset.filter
            (shiftFree m)).card :=
        card_powerset_filter_shiftFree_le_prod (Finset.Icc 1 m)
          (fun r => prog m (r + m) (((K - r) / m).toNat))
          (Finset.Icc (m + 1) K) (Icc_subset_biUnion_prog hm)
    _ = ∏ r ∈ Finset.Icc 1 m, Nat.fib (((K - r) / m).toNat + 2) :=
        Finset.prod_congr rfl fun r _ =>
          card_powerset_filter_shiftFree_prog (by omega) (r + m) _

end JSP000728
