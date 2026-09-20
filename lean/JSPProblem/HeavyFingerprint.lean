import JSPProblem.PerContainerGlue
import JSPProblem.ScanContainer
import JSPProblem.Supersat3

/-!
# JSP-000728 — the heavy fingerprint and the `DeterminingFingerprint` residual

This file attacks `DeterminingFingerprint` — the hypothesis that every
maximal sum-free `M` housed in a sparse container `C` admits a small
`T ⊆ M` with `M ∈ detFiber n C T` — via the **heavy-top fingerprint**

  `heavyT C M ω := M.filter (fun x => ω ≤ (C.filter fun a => x - a ∈ C).card)`

the elements of `M` that are the sum-coordinate ("top") of at least `ω`
Schur triples of the container.

## What is proved

* **Size bound** (`card_heavyT_mul_le`, `card_heavyT_le`,
  `card_heavyT_le_of_schurTripleCount_le`): the top-fibers over distinct
  `x` are disjoint, so `|heavyT C M ω| · ω ≤ schurTripleCount C`; for
  `schurTripleCount C ≤ δn²` and `ω = Θ(n)` this gives `|T| ≤ (δ/δ')·n =
  o(n)`.  The *size* half of the determining-fingerprint requirement is
  therefore unconditional.
* **The trace is `T`-independent** (`inter_detGround_eq_upper`): for any
  `T ⊆ M`, `M ∩ detGround n T C = M ∩ (n/2, n]`, because every element of
  a sum-free `M ⊇ T` is `T`-unlooped (`not_linkLoop_of_mem`).  The link
  independence of the trace is likewise automatic (`linkIndepSet_trace`).
* **The obstruction dichotomy** (`edge_or_lightObstruction`): for
  `x ∈ detGround n T C ∖ M`, the maximality obstruction of `x` either
  produces a `T`-edge into the upper trace — `x` is *dominated* — or is a
  `LightObstruction`: a representation `x = a + b` with both summands
  light (`a, b ∈ M \ T`), or with `a ∈ T` but the partner `b` light *and
  low* (`b ≤ n/2`, so `b ∉ detGround`), or a translate `a + x ∈ M` with
  `a` light.  (The fourth obstruction `x + x ∈ M` is impossible since
  `x > n/2`, and `a, b ∈ T` summing to `x` would be a loop, contradicting
  `x ∈ detGround`.)
* **The fiber membership decomposes** (`mem_detFiber_iff_dominated_unique`,
  `mem_detFiber_of_no_lightObstruction`): `M ∈ detFiber n C T` iff (i)
  every `x ∈ detGround ∖ M` is dominated — equivalently, no light
  obstruction occurs — and (ii) uniqueness: `M' ⊇ T` maximal in `C` with
  the same upper trace forces `M' = M`.
* **Sanity check** (`mem_detFiber_of_isSumFree_container`): for a
  *sum-free* container the empty fingerprint already determines `M` —
  every obstruction would be a Schur triple of `C`, hence impossible, so
  `detGround ⊆ M` and all maximal `M' ⊆ C` coincide.
* **The named residual** (`HeavyDeterminingFingerprint`) and the
  reduction `determiningFingerprint_of_heavyDeterminingFingerprint` —
  `HeavyDeterminingFingerprint → DeterminingFingerprint`.
* **A worked failure** (`not_mem_detFiber_ten`,
  `not_mem_detFiber_heavyT_ten`): at `n = 10` the container
  `C = {1,3,4,5,7,9}` (8 Schur triples) houses `M = {1,3,5,7,9}` (the
  odds) and `M' = {1,4,7,9}`, both maximal, with the same upper trace
  `{7,9}`; `heavyT C M 10 = ∅` does not determine `M`.

## The honest residual gap

Both residual clauses can fail for the bare heavy fingerprint, and the
counterexample shows the failure is not an artifact:

* **Light private blockers.**  A light element `a ∈ M \ T` tops fewer
  than `ω` triples of `C`, but may serve as *summand* in `Θ(n)` pairs —
  e.g. `M =` odds inside `C =` odds `∪ {4}` has `heavyT = ∅`, and every
  obstruction of an upper container element passes through light (here:
  no) fingerprint elements.  Smallness of `T` (a *top*-fiber count) does
  not control the *summand* usage of light elements, so the domination
  clause (`LightObstruction`-freeness on `detGround ∖ M`) is exactly the
  unmoved mathematical content.
* **Low-part uniqueness.**  `T` must pin down `M ∩ [1, n/2]` through the
  clause `M' ∩ detGround = M ∩ detGround`, which only fixes the *upper*
  trace; the `n = 10` example shows a genuinely different maximal `M'`
  sharing the trace.  Any proof of `DeterminingFingerprint` needs a
  fingerprint whose members force the low part via maximality — a
  "generating" fingerprint, not a "heavy" one.  The full lower trace
  works precisely because it *is* the low part
  (`mem_detFiber_full_trace`).

## The scan-fingerprint variant

`T' = scanFingerprint n M` satisfies `|T'| ≤ schurTripleCount
(scanContainer n M)` (each element tops a container triple,
`scanFingerprint_card_le_triples`), but `scanContainer n M` is not a
subset of `C` — the scan adjoins *every* unblocked element, whether or
not it lies in `C` — so `|T'|` is not bounded by `schurTripleCount C`.
What one can prove is the conditional bound
`scanFingerprint_card_le_of_scanContainer_subset`: *if*
`scanContainer n M ⊆ C` (e.g. when `C` itself is a scan container of the
family) then `|T'| ≤ schurTripleCount C`.  For `M =` odds the scan
fingerprint is even empty and `scanContainer n ∅ =` odds already covers
`M` — the scan fingerprint is a *container* device (`ScanContainer.lean`),
not a detFiber-determining one: `detGround n ∅ C` is much larger than
what `scanContainer` sees, and uniqueness fails exactly as for `T = ∅`.
-/

namespace JSP000728

/-! ## The heavy-top fingerprint -/

/-- The **heavy-top fingerprint** of `M` inside `C` at threshold `ω`: the
elements of `M` that top at least `ω` Schur triples of `C`, measured by
the top-fiber `C.filter (fun a => x - a ∈ C)` of
`card_schurTriples_fiber_top`. -/
def heavyT (C M : Finset ℤ) (ω : ℕ) : Finset ℤ :=
  M.filter fun x => ω ≤ (C.filter fun a => x - a ∈ C).card

theorem mem_heavyT {C M : Finset ℤ} {ω : ℕ} {x : ℤ} :
    x ∈ heavyT C M ω ↔
      x ∈ M ∧ ω ≤ (C.filter fun a => x - a ∈ C).card :=
  Finset.mem_filter

theorem heavyT_subset (C M : Finset ℤ) (ω : ℕ) : heavyT C M ω ⊆ M :=
  Finset.filter_subset _ _

theorem heavyT_subset_container {C M : Finset ℤ} (hMC : M ⊆ C) (ω : ℕ) :
    heavyT C M ω ⊆ C :=
  (heavyT_subset C M ω).trans hMC

/-- The fingerprint is monotone in `M`. -/
theorem heavyT_mono {C : Finset ℤ} {M₁ M₂ : Finset ℤ} (h : M₁ ⊆ M₂)
    (ω : ℕ) : heavyT C M₁ ω ⊆ heavyT C M₂ ω :=
  fun _x hx => Finset.mem_filter.mpr
    ⟨h (Finset.mem_filter.mp hx).1, (Finset.mem_filter.mp hx).2⟩

/-- The fingerprint is antitone in the threshold `ω`. -/
theorem heavyT_antitone {C M : Finset ℤ} {ω₁ ω₂ : ℕ} (h : ω₁ ≤ ω₂) :
    heavyT C M ω₂ ⊆ heavyT C M ω₁ :=
  fun _x hx => Finset.mem_filter.mpr
    ⟨(Finset.mem_filter.mp hx).1, h.trans (Finset.mem_filter.mp hx).2⟩

/-- **Fiber-sum bound.**  Erasing `heavyT C M ω ⊆ C` destroys at least
`|heavyT|·ω` Schur triples of `C` (`schurTripleCount_sdiff_le_of_heavy`:
the top-fibers over distinct tops are disjoint). -/
theorem card_heavyT_mul_le {C M : Finset ℤ} (hMC : M ⊆ C) (ω : ℕ) :
    (heavyT C M ω).card * ω ≤ schurTripleCount C := by
  have hsub : heavyT C M ω ⊆ C := heavyT_subset_container hMC ω
  have hheavy : ∀ x ∈ heavyT C M ω,
      ω ≤ (C.filter fun a => x - a ∈ C).card :=
    fun x hx => (Finset.mem_filter.mp hx).2
  have h := schurTripleCount_sdiff_le_of_heavy hsub hheavy
  omega

/-- Real form: `|heavyT C M ω| ≤ schurTripleCount C / ω`. -/
theorem card_heavyT_le {C M : Finset ℤ} (hMC : M ⊆ C) {ω : ℕ}
    (hω : 0 < ω) :
    ((heavyT C M ω).card : ℝ) ≤ schurTripleCount C / ω := by
  have hR : ((heavyT C M ω).card : ℝ) * (ω : ℝ) ≤ schurTripleCount C := by
    exact_mod_cast card_heavyT_mul_le hMC ω
  rwa [le_div_iff₀ (by exact_mod_cast hω : (0 : ℝ) < ω)]

/-- **The size half of `DeterminingFingerprint` is unconditional.**
Inside a `δn²`-sparse container, `|heavyT C M ω| ≤ δn²/ω`; taking
`ω = δ'n` gives `|T| ≤ (δ/δ')·n = o(n)`. -/
theorem card_heavyT_le_of_schurTripleCount_le {C M : Finset ℤ}
    (hMC : M ⊆ C) {ω n : ℕ} {δ : ℝ} (hω : 0 < ω)
    (hsp : (schurTripleCount C : ℝ) ≤ δ * (n : ℝ) ^ 2) :
    ((heavyT C M ω).card : ℝ) ≤ δ * (n : ℝ) ^ 2 / ω := by
  have hωR : (0 : ℝ) < ω := by exact_mod_cast hω
  calc ((heavyT C M ω).card : ℝ)
      ≤ schurTripleCount C / ω := card_heavyT_le hMC hω
    _ = schurTripleCount C * (ω : ℝ)⁻¹ := by rw [div_eq_mul_inv]
    _ ≤ δ * (n : ℝ) ^ 2 * (ω : ℝ)⁻¹ :=
        mul_le_mul_of_nonneg_right hsp
          (inv_nonneg.mpr hωR.le)
    _ = δ * (n : ℝ) ^ 2 / ω := by rw [div_eq_mul_inv]

/-! ## The trace on `detGround` does not see `T` -/

/-- No element of a sum-free `M ⊇ T` carries a `T`-loop. -/
theorem not_linkLoop_of_mem {M T : Finset ℤ} (hsf : IsSumFree M)
    (hT : T ⊆ M) {x : ℤ} (hx : x ∈ M) : ¬ linkLoop T x :=
  (linkIndepSet_of_isSumFree hsf hT (Finset.Subset.refl M)).1 x hx

/-- **The trace is `T`-independent.**  For `T ⊆ M ⊆ C` with `M` sum-free,
`M ∩ detGround n T C = M ∩ (⌊n/2⌋, n]`: elements of `M` are always
`T`-unlooped and lie in `C`.  So for *any* sub-fingerprint `T ⊆ M`, the
`detFiber` trace is simply the upper trace — `T` only enters through the
domination and uniqueness clauses. -/
theorem inter_detGround_eq_upper {n : ℕ} {C M T : Finset ℤ}
    (hsf : IsSumFree M) (hMC : M ⊆ C) (hT : T ⊆ M) :
    M ∩ detGround n T C = M ∩ Finset.Icc ((n : ℤ) / 2 + 1) (n : ℤ) := by
  apply Finset.Subset.antisymm
  · intro x hx
    obtain ⟨hxM, hxB⟩ := Finset.mem_inter.mp hx
    exact Finset.mem_inter.mpr
      ⟨hxM, (Finset.mem_inter.mp (Finset.mem_filter.mp hxB).1).2⟩
  · intro x hx
    obtain ⟨hxM, hxI⟩ := Finset.mem_inter.mp hx
    exact Finset.mem_inter.mpr ⟨hxM, Finset.mem_filter.mpr
      ⟨Finset.mem_inter.mpr ⟨hMC hxM, hxI⟩,
        not_linkLoop_of_mem hsf hT hxM⟩⟩

/-- The trace is always `T`-link-independent (it is a subset of the
sum-free `M`). -/
theorem linkIndepSet_trace {n : ℕ} {C M T : Finset ℤ}
    (hsf : IsSumFree M) (hT : T ⊆ M) :
    linkIndepSet T (M ∩ detGround n T C) :=
  linkIndepSet_of_isSumFree hsf hT Finset.inter_subset_left

/-- For `b ∈ M` the `detGround` membership reduces to `b > n/2`: a
`T`-invisible element of `M` is exactly a low element `b ≤ n/2`. -/
theorem mem_detGround_iff_of_mem {n : ℕ} {C M T : Finset ℤ} {b : ℤ}
    (hsub : M ⊆ interval n) (hsf : IsSumFree M) (hMC : M ⊆ C)
    (hT : T ⊆ M) (hb : b ∈ M) :
    b ∈ detGround n T C ↔ (n : ℤ) / 2 < b := by
  have hbI := Finset.mem_Icc.mp (hsub hb)
  constructor
  · intro h
    obtain ⟨-, hbI'⟩ := Finset.mem_inter.mp (Finset.mem_filter.mp h).1
    obtain ⟨h1, -⟩ := Finset.mem_Icc.mp hbI'
    omega
  · intro h
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_inter.mpr
        ⟨hMC hb, Finset.mem_Icc.mpr ⟨by omega, hbI.2⟩⟩,
        not_linkLoop_of_mem hsf hT hb⟩

/-! ## The obstruction dichotomy -/

/-- **The light obstruction.**  `x` is excluded from `M` in a way that
the fingerprint `T` cannot see:

* a representation `x = a + b` with *both* summands light
  (`a, b ∈ M \ T`);
* a representation `x = a + b` with `a ∈ T` but the partner `b` light
  and *low* (`b ≤ n/2`, equivalently `b ∉ detGround n T C` — the edge
  `x ~ b` does not land in the ground set);
* a translate `a + x ∈ M` with `a` light (the edge `x ~ a + x` would
  need `a ∈ T`).

These are precisely the shapes that defeat the heavy fingerprint: the
"private" blockers of `M` living below the heavy threshold. -/
def LightObstruction (n : ℕ) (T M : Finset ℤ) (x : ℤ) : Prop :=
  (∃ a ∈ M \ T, ∃ b ∈ M \ T, a + b = x) ∨
    (∃ a ∈ T, ∃ b ∈ M \ T, a + b = x ∧ b ≤ (n : ℤ) / 2) ∨
    (∃ a ∈ M \ T, a + x ∈ M)

/-- **The dichotomy.**  For `x ∈ detGround n T C ∖ M` (so `x > n/2`,
`T`-unlooped), the maximality obstruction of `x` either produces a
`T`-link edge from `x` into the upper trace `M ∩ detGround n T C`, or it
is a `LightObstruction`.  The case analysis:

* `a + b = x`, `a, b ∈ M`: both in `T` is impossible (it would be a
  `T`-loop at `x`, contradicting `x ∈ detGround`); if the `T`-summand's
  partner lies in `detGround` (`> n/2`), it dominates `x`; otherwise the
  obstruction is light.
* `a + x ∈ M` (or `x + a ∈ M`): the translate `a + x` lies in the upper
  half, in `C`, and is unlooped — so it is in the trace and dominates `x`
  via `(a + x) - x = a ∈ T` — provided `a ∈ T`; otherwise light.
* `x + x ∈ M`: impossible, `x > n/2` gives `x + x > n`. -/
theorem edge_or_lightObstruction {n : ℕ} {C M T : Finset ℤ} {x : ℤ}
    (hCn : C ⊆ interval n) (hM : IsMaxSumFree n M) (hMC : M ⊆ C)
    (hT : T ⊆ M) (hxB : x ∈ detGround n T C) (hxM : x ∉ M) :
    (∃ y ∈ M ∩ detGround n T C, linkAdj T x y) ∨
      LightObstruction n T M x := by
  classical
  have hsub : M ⊆ interval n := hM.1
  have hsf : IsSumFree M := hM.2.1
  have hxn : x ∈ interval n := hCn (detGround_subset_container n T C hxB)
  have hnoloop : ¬ linkLoop T x := (Finset.mem_filter.mp hxB).2
  have hx1 : (n : ℤ) / 2 + 1 ≤ x :=
    (Finset.mem_Icc.mp
      (Finset.mem_inter.mp (Finset.mem_filter.mp hxB).1).2).1
  -- Elements of `M` above `n/2` lie in `detGround`.
  have hupper : ∀ y ∈ M, (n : ℤ) / 2 < y → y ∈ detGround n T C :=
    fun y hy hyb => (mem_detGround_iff_of_mem hsub hsf hMC hT hy).mpr hyb
  -- The translate obstruction: `a + x ∈ M` dominates `x` iff `a ∈ T`.
  have htrans : ∀ a ∈ M, a + x ∈ M →
      (∃ y ∈ M ∩ detGround n T C, linkAdj T x y) ∨
        (∃ a ∈ M \ T, a + x ∈ M) := by
    intro a ha hax
    by_cases haT : a ∈ T
    · have ha1 : (0 : ℤ) < a := interval_pos (hsub ha)
      have haxup : (n : ℤ) / 2 < a + x := by omega
      refine Or.inl ⟨a + x,
        Finset.mem_inter.mpr ⟨hax, hupper _ hax haxup⟩, ?_⟩
      exact Or.inr (Or.inr (by rwa [show a + x - x = a from by ring]))
    · exact Or.inr ⟨a, Finset.mem_sdiff.mpr ⟨ha, haT⟩, hax⟩
  rcases hM.exists_obstruction hxn hxM with hsum | hax | hxa | hxx
  · obtain ⟨a, ha, b, hb, hab⟩ := hsum
    by_cases haT : a ∈ T <;> by_cases hbT : b ∈ T
    · -- `a, b ∈ T` gives a `T`-loop at `x`, contradicting `x ∈ detGround`.
      exact absurd (Or.inl ⟨a, haT,
        show x - a ∈ T from by rwa [show x - a = b from by omega]⟩ :
        linkLoop T x) hnoloop
    · -- `a ∈ T`, `b ∉ T`: dominated iff `b` lies in the ground set.
      by_cases hbB : (n : ℤ) / 2 < b
      · exact Or.inl ⟨b, Finset.mem_inter.mpr ⟨hb, hupper b hb hbB⟩,
          Or.inr (Or.inl (show x - b ∈ T from
            by rwa [show x - b = a from by omega]))⟩
      · exact Or.inr (Or.inr (Or.inl
          ⟨a, haT, b, Finset.mem_sdiff.mpr ⟨hb, hbT⟩, hab, by omega⟩))
    · -- symmetric: `a ∉ T`, `b ∈ T`.
      by_cases haB : (n : ℤ) / 2 < a
      · exact Or.inl ⟨a, Finset.mem_inter.mpr ⟨ha, hupper a ha haB⟩,
          Or.inr (Or.inl (show x - a ∈ T from
            by rwa [show x - a = b from by omega]))⟩
      · exact Or.inr (Or.inr (Or.inl
          ⟨b, hbT, a, Finset.mem_sdiff.mpr ⟨ha, haT⟩, by omega,
            by omega⟩))
    · -- both summands light.
      exact Or.inr (Or.inl ⟨a, Finset.mem_sdiff.mpr ⟨ha, haT⟩, b,
        Finset.mem_sdiff.mpr ⟨hb, hbT⟩, hab⟩)
  · obtain ⟨a, ha, hax⟩ := hax
    rcases htrans a ha hax with hed | hbad
    · exact Or.inl hed
    · exact Or.inr (Or.inr (Or.inr hbad))
  · obtain ⟨a, ha, hxa⟩ := hxa
    have hax : a + x ∈ M := add_comm x a ▸ hxa
    rcases htrans a ha hax with hed | hbad
    · exact Or.inl hed
    · exact Or.inr (Or.inr (Or.inr hbad))
  · -- `x + x ∈ M` is impossible since `x > n/2` gives `x + x > n`.
    have h2x : x + x ≤ (n : ℤ) := interval_le (hsub hxx)
    exact absurd h2x (not_le.mpr (by omega : (n : ℤ) < x + x))

/-- An undominated `x ∈ detGround ∖ M` always carries a light
obstruction — the contrapositive is the domination engine. -/
theorem lightObstruction_of_undominated {n : ℕ} {C M T : Finset ℤ}
    {x : ℤ} (hCn : C ⊆ interval n) (hM : IsMaxSumFree n M) (hMC : M ⊆ C)
    (hT : T ⊆ M) (hxB : x ∈ detGround n T C) (hxM : x ∉ M)
    (hund : ¬ ∃ y ∈ M ∩ detGround n T C, linkAdj T x y) :
    LightObstruction n T M x := by
  rcases edge_or_lightObstruction hCn hM hMC hT hxB hxM with hed | hbad
  · exact absurd hed hund
  · exact hbad

/-- If no `x ∈ detGround ∖ M` has a light obstruction, the upper trace is
a *maximal* link-independent set of `L_T` on `detGround n T C`. -/
theorem linkMaxIndepSet_trace_of_no_lightObstruction {n : ℕ}
    {C M T : Finset ℤ} (hCn : C ⊆ interval n) (hM : IsMaxSumFree n M)
    (hMC : M ⊆ C) (hT : T ⊆ M)
    (h : ∀ x ∈ detGround n T C, x ∉ M → ¬ LightObstruction n T M x) :
    linkMaxIndepSet T (detGround n T C) (M ∩ detGround n T C) := by
  refine ⟨Finset.inter_subset_right,
    linkIndepSet_of_isSumFree hM.2.1 hT Finset.inter_subset_left, ?_⟩
  intro x hxB hxt
  have hxM : x ∉ M := fun hxM => hxt (Finset.mem_inter.mpr ⟨hxM, hxB⟩)
  rcases edge_or_lightObstruction hCn hM hMC hT hxB hxM with hed | hbad
  · exact Or.inr hed
  · exact absurd hbad (h x hxB hxM)

/-- **Fiber membership from the two residual clauses.**  `M ∈ detFiber n
C T` once (i) no `x ∈ detGround ∖ M` has a light obstruction (the
domination clause) and (ii) `T` plus the upper trace pin down `M` (the
uniqueness clause). -/
theorem mem_detFiber_of_no_lightObstruction {n : ℕ} {C M T : Finset ℤ}
    (hCn : C ⊆ interval n) (hM : M ∈ maxSumFreeSets n) (hMC : M ⊆ C)
    (hT : T ⊆ M)
    (hdom : ∀ x ∈ detGround n T C, x ∉ M → ¬ LightObstruction n T M x)
    (huni : ∀ M' ∈ maxSumFreeSets n, M' ⊆ C → T ⊆ M' →
      M' ∩ detGround n T C = M ∩ detGround n T C → M' = M) :
    M ∈ detFiber n C T := by
  have hMmax := mem_maxSumFreeSets.mp hM
  refine mem_detFiber.mpr ⟨Finset.mem_filter.mpr ⟨hM, hMC⟩, hT, ?_, huni⟩
  exact mem_linkMaxSets.mpr ⟨Finset.inter_subset_right,
    linkMaxIndepSet_trace_of_no_lightObstruction hCn hMmax hMC hT hdom⟩

/-- **The residual, made precise.**  For `T ⊆ M ⊆ C ⊆ {1,…,n}` with `M`
maximal sum-free, `M ∈ detFiber n C T` is *equivalent* to domination of
`detGround ∖ M` plus uniqueness — `T ⊆ M` and link-independence of the
trace being automatic.  Combined with `edge_or_lightObstruction`, this
says: `T` determines `M` iff light elements of `M` are never the sole
obstruction and the low part of `M` is forced by `(T, M ∩ (n/2,n])`. -/
theorem mem_detFiber_iff_dominated_unique {n : ℕ} {C M T : Finset ℤ}
    (hM : M ∈ maxSumFreeSets n) (hMC : M ⊆ C) (hT : T ⊆ M) :
    M ∈ detFiber n C T ↔
      (∀ x ∈ detGround n T C, x ∉ M →
        ∃ y ∈ M ∩ detGround n T C, linkAdj T x y) ∧
        (∀ M' ∈ maxSumFreeSets n, M' ⊆ C → T ⊆ M' →
          M' ∩ detGround n T C = M ∩ detGround n T C → M' = M) := by
  have hMmax := mem_maxSumFreeSets.mp hM
  rw [mem_detFiber]
  constructor
  · rintro ⟨-, -, htrace, huni⟩
    refine ⟨?_, huni⟩
    intro x hxB hxM
    have hxnt : x ∉ M ∩ detGround n T C :=
      fun hh => hxM (Finset.mem_inter.mp hh).1
    obtain hloop | hed := (mem_linkMaxSets.mp htrace).2.2.2 x hxB hxnt
    · exact absurd hloop (Finset.mem_filter.mp hxB).2
    · exact hed
  · rintro ⟨hdom, huni⟩
    refine ⟨Finset.mem_filter.mpr ⟨hM, hMC⟩, hT, ?_, huni⟩
    rw [mem_linkMaxSets]
    refine ⟨Finset.inter_subset_right, Finset.inter_subset_right,
      linkIndepSet_of_isSumFree hMmax.2.1 hT Finset.inter_subset_left,
      ?_⟩
    intro x hxB hxt
    have hxM : x ∉ M := fun hxM => hxt (Finset.mem_inter.mpr ⟨hxM, hxB⟩)
    exact Or.inr (hdom x hxB hxM)

/-! ## The sum-free container sanity check -/

/-- In a sum-free container, `C` has no Schur triples to supply
obstructions: every `x ∈ C` already lies in any maximal `M ⊆ C`. -/
theorem mem_of_mem_container_of_isSumFree {n : ℕ} {C M : Finset ℤ}
    (hCn : C ⊆ interval n) (hCsf : IsSumFree C) (hM : IsMaxSumFree n M)
    (hMC : M ⊆ C) {x : ℤ} (hx : x ∈ C) : x ∈ M := by
  by_contra hxM
  rcases hM.exists_obstruction (hCn hx) hxM with h | h | h | h
  · obtain ⟨a, ha, b, hb, hab⟩ := h
    exact hCsf a (hMC ha) b (hMC hb) (by rwa [hab])
  · obtain ⟨a, ha, hax⟩ := h
    exact hCsf a (hMC ha) x hx (hMC hax)
  · obtain ⟨a, ha, hxa⟩ := h
    exact hCsf x hx a (hMC ha) (hMC hxa)
  · exact hCsf x hx x hx (hMC h)

/-- For `T = ∅` inside a sum-free container, `detGround ⊆ M`. -/
theorem detGround_empty_subset_of_isSumFree {n : ℕ} {C M : Finset ℤ}
    (hCn : C ⊆ interval n) (hCsf : IsSumFree C) (hM : IsMaxSumFree n M)
    (hMC : M ⊆ C) : detGround n ∅ C ⊆ M :=
  fun _ hx => mem_of_mem_container_of_isSumFree hCn hCsf hM hMC
    (detGround_subset_container n ∅ C hx)

/-- A sum-free container houses *at most one* maximal sum-free set:
`M ⊆ M'` elementwise (each `x ∈ M ⊆ C` must lie in `M'`), and maximality
of `M` gives the reverse. -/
theorem eq_of_maxSumFree_mem_isSumFree {n : ℕ} {C M M' : Finset ℤ}
    (hCn : C ⊆ interval n) (hCsf : IsSumFree C) (hM : IsMaxSumFree n M)
    (hMC : M ⊆ C) (hM' : IsMaxSumFree n M') (hM'C : M' ⊆ C) : M' = M := by
  have hMM' : M ⊆ M' :=
    fun x hx => mem_of_mem_container_of_isSumFree hCn hCsf hM' hM'C
      (hMC hx)
  have hM'M : M' ⊆ M :=
    (isMaxSumFree_iff_isMaximalSumFree.mp hM).2.2 M' hM'.1 hM'.2.1 hMM'
  exact Finset.Subset.antisymm hM'M hMM'

/-- **Sanity check.**  In a genuinely sum-free container `C`, the empty
fingerprint determines every maximal `M ⊆ C`: `detGround n ∅ C ⊆ M`
makes domination vacuous, and `eq_of_maxSumFree_mem_isSumFree` gives the
uniqueness clause for free.  `DeterminingFingerprint` is the
quantitative extension of this to `o(n²)`-sparse `C`. -/
theorem mem_detFiber_of_isSumFree_container {n : ℕ} {C M : Finset ℤ}
    (hCn : C ⊆ interval n) (hCsf : IsSumFree C)
    (hM : M ∈ maxSumFreeSets n) (hMC : M ⊆ C) :
    M ∈ detFiber n C ∅ := by
  have hMmax := mem_maxSumFreeSets.mp hM
  refine mem_detFiber_of_no_lightObstruction hCn hM hMC
    (Finset.empty_subset M) ?_ ?_
  · intro x hxB hxM
    exact absurd
      (detGround_empty_subset_of_isSumFree hCn hCsf hMmax hMC hxB) hxM
  · intro M' hM' hM'C _ _
    exact eq_of_maxSumFree_mem_isSumFree hCn hCsf hMmax hMC
      (mem_maxSumFreeSets.mp hM') hM'C

/-! ## The named residual and the reduction -/

/-- **The heavy determining-fingerprint hypothesis**: eventually, inside
every `δn²`-sparse container, every maximal sum-free `M` is determined by
its `n`-heavy-top fingerprint `heavyT C M n`.  Unlike
`DeterminingFingerprint`, the fingerprint is fixed explicitly; what it
leaves open is precisely the domination clause (no `LightObstruction`,
`edge_or_lightObstruction`) and the uniqueness clause of
`mem_detFiber_iff_dominated_unique` — and the worked example
`not_mem_detFiber_heavyT_ten` shows the uniqueness clause can genuinely
fail. -/
def HeavyDeterminingFingerprint : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n : ℕ in Filter.atTop,
    ∀ C : Finset ℤ, C ⊆ interval n →
      (schurTripleCount C : ℝ) ≤ δ * (n : ℝ) ^ 2 →
      ∀ M ∈ maxSumFreeSets n, M ⊆ C →
        M ∈ detFiber n C (heavyT C M n)

/-- **The reduction.**  If the `n`-heavy-top fingerprint determines every
maximal `M ⊆ C` inside `δn²`-sparse containers, then
`DeterminingFingerprint` holds: the size requirement is the fiber-sum
bound `|heavyT C M n| · n ≤ schurTripleCount C ≤ δn²`, i.e.
`|T| ≤ δn ≤ εn` for `δ ≤ ε`. -/
theorem determiningFingerprint_of_heavyDeterminingFingerprint
    (h : HeavyDeterminingFingerprint) : DeterminingFingerprint := by
  intro ε hε
  obtain ⟨δ₀, hδ₀, hdf⟩ := h ε hε
  refine ⟨min δ₀ ε, lt_min hδ₀ hε, ?_⟩
  filter_upwards [hdf, Filter.eventually_ge_atTop 1] with n hdfn hn1
  intro C hCn htr M hM hMC
  have hsp0 : (schurTripleCount C : ℝ) ≤ δ₀ * (n : ℝ) ^ 2 :=
    htr.trans (mul_le_mul_of_nonneg_right (min_le_left _ _)
      (sq_nonneg _))
  refine ⟨heavyT C M n, heavyT_subset _ _ _, ?_,
    hdfn C hCn hsp0 M hM hMC⟩
  -- `|heavyT C M n| · n ≤ schurTripleCount C ≤ min δ₀ ε · n²`.
  have hcardR : ((heavyT C M n).card : ℝ) * (n : ℝ)
      ≤ min δ₀ ε * (n : ℝ) ^ 2 := by
    have h1 : ((heavyT C M n).card : ℝ) * (n : ℝ)
        ≤ (schurTripleCount C : ℝ) := by
      exact_mod_cast card_heavyT_mul_le hMC n
    exact h1.trans htr
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have h1 : ((heavyT C M n).card : ℝ) ≤ min δ₀ ε * (n : ℝ) := by
    have h2 : ((heavyT C M n).card : ℝ)
        ≤ min δ₀ ε * (n : ℝ) ^ 2 / (n : ℝ) :=
      (le_div_iff₀ hnR).mpr hcardR
    have h3 : min δ₀ ε * (n : ℝ) ^ 2 / (n : ℝ) = min δ₀ ε * (n : ℝ) := by
      rw [div_eq_iff hnR.ne']
      ring
    exact h2.trans_eq h3
  calc ((heavyT C M n).card : ℝ)
      ≤ min δ₀ ε * (n : ℝ) := h1
    _ ≤ ε * (n : ℝ) :=
        mul_le_mul_of_nonneg_right (min_le_right _ _)
          (Nat.cast_nonneg _)

/-! ## The scan fingerprint -/

/-- **Conditional scan-fingerprint bound.**  If `M`'s scan container
happens to sit inside `C` — e.g. when `C` is itself a scan container —
then `|scanFingerprint n M| ≤ schurTripleCount C`: every fingerprint
element tops a Schur triple of the scan container
(`scanFingerprint_card_le_triples`).  The hypothesis is the honest gap:
in general `scanContainer n M ⊄ C`, since the scan adjoins every unblocked
element of `{1,…,n}`, inside `C` or not. -/
theorem scanFingerprint_card_le_of_scanContainer_subset {n : ℕ}
    {M C : Finset ℤ} (h : scanContainer n M ⊆ C) :
    (scanFingerprint n M).card ≤ schurTripleCount C :=
  (scanFingerprint_card_le_triples n M).trans (schurTripleCount_mono h)

/-- Under the same hypothesis, every scan-fingerprint element is `1`-heavy
in `C`: it tops a triple of `scanContainer n M ⊆ C`, hence a triple of
`C`. -/
theorem scanFingerprint_subset_heavyT_one {n : ℕ} {M C : Finset ℤ}
    (h : scanContainer n M ⊆ C) :
    scanFingerprint n M ⊆ heavyT C M 1 := by
  intro x hx
  rw [mem_scanFingerprint] at hx
  obtain ⟨hxM, -, a, ha, b, hb, hab⟩ := hx
  rw [mem_heavyT]
  refine ⟨hxM, ?_⟩
  have haC : a ∈ C := h (Finset.mem_inter.mp ha).1
  have hbC : x - a ∈ C := by
    have hbeq : x - a = b := by omega
    rw [hbeq]
    exact h (Finset.mem_inter.mp hb).1
  exact Finset.card_pos.mpr
    ⟨a, Finset.mem_filter.mpr ⟨haC, hbC⟩⟩

/-! ## A worked failure of the bare heavy fingerprint

At `n = 10` take `C = {1,3,4,5,7,9}` — eight Schur triples
(`1+3=4, 1+4=5, 3+4=7, 4+5=9` and symmetric) — and `M = {1,3,5,7,9}`, the
odds, maximal sum-free in `{1,…,10}`: every even `x` is `1 + (x-1)`.  The
fingerprint `heavyT C M 10 = ∅`: no element of `C` tops `≥ 10` triples.
But `M' = {1,4,7,9}` is also maximal sum-free, also lies in `C`, also has
upper trace `{7,9}` — so the fiber uniqueness clause fails, and
`M ∉ detFiber 10 C ∅`. -/

theorem heavyT_ten_empty :
    heavyT ({1, 3, 4, 5, 7, 9} : Finset ℤ)
      ({1, 3, 5, 7, 9} : Finset ℤ) 10 = ∅ := by
  decide

theorem schurTripleCount_ten :
    schurTripleCount ({1, 3, 4, 5, 7, 9} : Finset ℤ) = 8 := by
  decide

theorem not_mem_detFiber_ten :
    ({1, 3, 5, 7, 9} : Finset ℤ) ∉
      detFiber 10 ({1, 3, 4, 5, 7, 9} : Finset ℤ) ∅ := by
  intro h
  rw [mem_detFiber] at h
  obtain ⟨-, -, -, huni⟩ := h
  have hM' : ({1, 4, 7, 9} : Finset ℤ) ∈ maxSumFreeSets 10 :=
    mem_maxSumFreeSets.mpr (by decide)
  have hC : ({1, 4, 7, 9} : Finset ℤ) ⊆
      ({1, 3, 4, 5, 7, 9} : Finset ℤ) := by decide
  have htr : ({1, 4, 7, 9} : Finset ℤ) ∩
        detGround 10 ∅ ({1, 3, 4, 5, 7, 9} : Finset ℤ) =
      ({1, 3, 5, 7, 9} : Finset ℤ) ∩
        detGround 10 ∅ ({1, 3, 4, 5, 7, 9} : Finset ℤ) := by
    decide
  have heq := huni _ hM' hC (Finset.empty_subset _) htr
  exact absurd heq (by decide)

/-- The same failure for `heavyT` itself: `heavyT C M 10 = ∅`, so
`M ∉ detFiber 10 C (heavyT C M 10)`. -/
theorem not_mem_detFiber_heavyT_ten :
    ({1, 3, 5, 7, 9} : Finset ℤ) ∉
      detFiber 10 ({1, 3, 4, 5, 7, 9} : Finset ℤ)
        (heavyT ({1, 3, 4, 5, 7, 9} : Finset ℤ)
          ({1, 3, 5, 7, 9} : Finset ℤ) 10) := by
  rw [heavyT_ten_empty]
  exact not_mem_detFiber_ten

end JSP000728
