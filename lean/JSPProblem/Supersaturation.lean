import JSPProblem.Containers
import JSPProblem.MaxCard
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SDiff
import Mathlib.Data.Int.Interval
import Mathlib.Data.Prod.Basic
import Mathlib.Tactic.Ring

/-!
# JSP-000728 — Schur-triple supersaturation and the easy removal direction

Structural inputs for the BLST18 container-method upper bound.  The two
ingredients proved here are:

* **Fiber decomposition** (`schurTripleCount_eq_sum_filter`): the Schur
  triples `(x, y, z)` of `s` split according to their sum `z`, and the fiber
  over `z` bijects with `{x ∈ s : z - x ∈ s}` via `x ↦ (x, z - x, z)`.
* **Supersaturation / inclusion–exclusion**
  (`card_filter_sub_mem_ge`, `schurTripleCount_ge_sum`,
  `two_mul_card_le_add_schurTripleCount`): for each `z`, the sets
  `A = s ∩ {1,…,z-1}` and `z - A` both live in `{1,…,z-1}`, so
  `|A ∩ (z - A)| ≥ 2|A| - (z-1)`, and `A ∩ (z - A)` sits inside the fiber
  `{x ∈ s : z - x ∈ s}`.  Summed over `z ∈ s` this gives a quantitative
  lower bound on `schurTripleCount s`; applied at `z = max s` it yields
  `2·|s| ≤ n + 1 + schurTripleCount s` for `s ⊆ {1,…,n}`, whence any set
  larger than `(n+1)/2` must contain a Schur triple
  (`schurTripleCount_pos_of_card_gt`, the contrapositive of
  `card_le_of_isSumFree`).
* **Removal-lemma converse** (`schurTripleCount_le_sdiff_mul_of_isSumFree`):
  if `t` is a sum-free subset of `s` then every Schur triple of `s` meets
  `s ∖ t` in at least one coordinate, so
  `schurTripleCount s ≤ 3·|s ∖ t|·|s|²`.  Equivalently, deleting
  `schurTripleCount s / (3|s|²)` elements never suffices to make `s`
  sum-free — the *easy* direction of the arithmetic removal lemma.
-/

namespace JSP000728

/-! ## Fiber decomposition of the Schur-triple count -/

/-- For each `z ∈ s`, the Schur triples ending in `z` biject with
`{x ∈ s : z - x ∈ s}` via `x ↦ (x, z - x, z)`.  Hence
`schurTripleCount s = ∑ z ∈ s, |{x ∈ s : z - x ∈ s}|`. -/
theorem schurTripleCount_eq_sum_filter (s : Finset ℤ) :
    schurTripleCount s = ∑ z ∈ s, (s.filter fun x => z - x ∈ s).card := by
  classical
  have hmem : (↑(schurTriples s) : Set (ℤ × ℤ × ℤ)).MapsTo
      (fun t => t.2.2) ↑s := by
    intro t ht
    rw [Finset.mem_coe] at ht ⊢
    rw [schurTriples, Finset.mem_filter, Finset.mem_product,
      Finset.mem_product] at ht
    exact ht.1.2.2
  have key : schurTripleCount s
      = ∑ z ∈ s, ((schurTriples s).filter fun t => t.2.2 = z).card := by
    rw [schurTripleCount]
    exact Finset.card_eq_sum_card_fiberwise hmem
  rw [key]
  refine Finset.sum_congr rfl fun z hz => ?_
  have hfiber : ((schurTriples s).filter fun t => t.2.2 = z)
      = (s.filter fun x => z - x ∈ s).image fun x => (x, z - x, z) := by
    apply subset_antisymm
    · intro a ha
      obtain ⟨ha1, ha2⟩ := Finset.mem_filter.mp ha
      rcases a with ⟨b, c, d⟩
      rw [schurTriples, Finset.mem_filter, Finset.mem_product,
        Finset.mem_product] at ha1
      obtain ⟨⟨hb, hc, hd⟩, hsum⟩ := ha1
      have hsum' : b + c = d := hsum
      have ha2' : d = z := ha2
      rw [Finset.mem_image]
      refine ⟨b, ?_, ?_⟩
      · rw [Finset.mem_filter]
        have h1 : z - b = c := by omega
        exact ⟨hb, h1 ▸ hc⟩
      · show (b, z - b, z) = (b, c, d)
        have h1 : z - b = c := by omega
        have h2 : z = d := ha2'.symm
        rw [h1, h2]
    · intro a ha
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨hxs, hzx⟩ := Finset.mem_filter.mp hx
      rw [Finset.mem_filter]
      refine ⟨?_, rfl⟩
      rw [schurTriples, Finset.mem_filter, Finset.mem_product,
        Finset.mem_product]
      exact ⟨⟨hxs, hzx, hz⟩, by show x + (z - x) = z; omega⟩
  have hinj : Function.Injective fun x : ℤ => (x, z - x, z) := by
    intro a b h
    have h' : (a, z - a, z) = (b, z - b, z) := h
    exact (Prod.mk_inj.mp h').1
  rw [hfiber, Finset.card_image_of_injective _ hinj]

/-! ## Inclusion–exclusion lower bound for a single fiber -/

/-- **Inclusion–exclusion.**  For `A = s ∩ {1,…,z-1}` and its reflection
`z - A`, both subsets of `{1,…,z-1}`, one has
`|A ∩ (z-A)| ≥ |A| + |z-A| - (z-1) = 2|A| - (z-1)`, and `A ∩ (z-A)` lies
inside `{x ∈ s : z - x ∈ s}`.  Stated additively in `ℕ`. -/
theorem card_filter_sub_mem_ge (s : Finset ℤ) (z : ℤ) :
    2 * (s ∩ Finset.Icc 1 (z - 1)).card
      ≤ (z - 1).toNat + (s.filter fun x => z - x ∈ s).card := by
  classical
  have hA : ∀ x ∈ s ∩ Finset.Icc 1 (z - 1), x ∈ s ∧ 1 ≤ x ∧ x ≤ z - 1 := by
    intro x hx
    obtain ⟨hxs, hxI⟩ := Finset.mem_inter.mp hx
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hxI
    exact ⟨hxs, h1, h2⟩
  have hBsub : (s ∩ Finset.Icc 1 (z - 1)).image (fun x => z - x)
      ⊆ Finset.Icc 1 (z - 1) := by
    intro y hy
    obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp hy
    obtain ⟨-, hx1, hxz⟩ := hA x hx
    have hxy' : z - x = y := hxy
    rw [Finset.mem_Icc]
    omega
  have hBcard : ((s ∩ Finset.Icc 1 (z - 1)).image fun x => z - x).card
      = (s ∩ Finset.Icc 1 (z - 1)).card := by
    apply Finset.card_image_of_injOn
    intro a _ b _ hab
    have hab' : z - a = z - b := hab
    omega
  have hintersub : s ∩ Finset.Icc 1 (z - 1)
      ∩ (s ∩ Finset.Icc 1 (z - 1)).image (fun x => z - x)
        ⊆ s.filter fun x => z - x ∈ s := by
    intro x hx
    obtain ⟨hxA, hxB⟩ := Finset.mem_inter.mp hx
    obtain ⟨a, ha, hax⟩ := Finset.mem_image.mp hxB
    obtain ⟨hxs, -, -⟩ := hA x hxA
    obtain ⟨has, -, -⟩ := hA a ha
    rw [Finset.mem_filter]
    have hax' : z - a = x := hax
    have hxa : z - x = a := by omega
    exact ⟨hxs, hxa ▸ has⟩
  have hunion : (s ∩ Finset.Icc 1 (z - 1)
      ∪ (s ∩ Finset.Icc 1 (z - 1)).image fun x => z - x).card
        ≤ (z - 1).toNat := by
    have hAsub : s ∩ Finset.Icc 1 (z - 1) ⊆ Finset.Icc 1 (z - 1) :=
      Finset.inter_subset_right
    have h := Finset.card_le_card (Finset.union_subset hAsub hBsub)
    rw [Int.card_Icc] at h
    have e : z - 1 + 1 - 1 = z - 1 := by omega
    rw [e] at h
    exact h
  have hinter : (s ∩ Finset.Icc 1 (z - 1)
      ∩ (s ∩ Finset.Icc 1 (z - 1)).image fun x => z - x).card
        ≤ (s.filter fun x => z - x ∈ s).card :=
    Finset.card_le_card hintersub
  have hsum := Finset.card_union_add_card_inter (s ∩ Finset.Icc 1 (z - 1))
    ((s ∩ Finset.Icc 1 (z - 1)).image fun x => z - x)
  omega

/-- **Supersaturation, summed form.**  Summing the inclusion–exclusion
bound over all `z ∈ s` gives a lower bound on the total number of Schur
triples of `s`. -/
theorem schurTripleCount_ge_sum (s : Finset ℤ) :
    (∑ z ∈ s, (2 * (s ∩ Finset.Icc 1 (z - 1)).card - (z - 1).toNat))
      ≤ schurTripleCount s := by
  rw [schurTripleCount_eq_sum_filter s]
  apply Finset.sum_le_sum
  intro z _
  have h := card_filter_sub_mem_ge s z
  omega

/-- **Supersaturation, cardinality form.**  For `s ⊆ {1,…,n}` with maximum
`M`, the fiber over `M` already contributes
`2(|s| - 1) - (M - 1) ≥ 2|s| - n - 1` Schur triples, so
`2·|s| ≤ n + 1 + schurTripleCount s`. -/
theorem two_mul_card_le_add_schurTripleCount {n : ℕ} {s : Finset ℤ}
    (hsub : s ⊆ interval n) :
    2 * s.card ≤ n + 1 + schurTripleCount s := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | hne
  · simp
  obtain ⟨M, hMmem, hMle⟩ : ∃ M ∈ s, ∀ x ∈ s, x ≤ M :=
    ⟨s.max' hne, s.max'_mem hne, fun x hx => s.le_max' x hx⟩
  have hMI := Finset.mem_Icc.mp (hsub hMmem)
  have hA : s ∩ Finset.Icc 1 (M - 1) = s.erase M := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_Icc, Finset.mem_erase]
    constructor
    · rintro ⟨hxs, -, hxM⟩
      exact ⟨by omega, hxs⟩
    · rintro ⟨hxne, hxs⟩
      obtain ⟨hx1, -⟩ := Finset.mem_Icc.mp (hsub hxs)
      have hxlt : x < M := lt_of_le_of_ne (hMle x hxs) hxne
      exact ⟨hxs, hx1, by omega⟩
  have hge := card_filter_sub_mem_ge s M
  rw [hA, Finset.card_erase_of_mem hMmem] at hge
  have hfib : (s.filter fun x => M - x ∈ s).card ≤ schurTripleCount s := by
    rw [schurTripleCount_eq_sum_filter s]
    exact Finset.single_le_sum
      (f := fun z : ℤ => (s.filter fun x => z - x ∈ s).card)
      (fun i _ => Nat.zero_le _) hMmem
  have hMnat : (M - 1).toNat + 1 ≤ n := by omega
  have hcardpos : 0 < s.card := Finset.card_pos.mpr hne
  omega

/-- **Contrapositive of `card_le_of_isSumFree`:** any subset of `{1,…,n}`
with more than `(n+1)/2` elements contains a Schur triple. -/
theorem schurTripleCount_pos_of_card_gt {n : ℕ} {s : Finset ℤ}
    (hsub : s ⊆ interval n) (hcard : (n + 1) / 2 < s.card) :
    0 < schurTripleCount s := by
  have h := two_mul_card_le_add_schurTripleCount hsub
  omega

/-! ## The easy direction of the arithmetic removal lemma -/

/-- **Removal-lemma converse.**  If `t` is a sum-free subset of `s`, every
Schur triple `(x, y, z)` of `s` must touch `s ∖ t` in at least one of its
three coordinates (otherwise `x, y, z ∈ t` with `x + y = z`, contradicting
sum-freeness).  Hence `schurTripleCount s ≤ 3·|s ∖ t|·|s|²`. -/
theorem schurTripleCount_le_sdiff_mul_of_isSumFree {s t : Finset ℤ}
    (_hts : t ⊆ s) (ht : IsSumFree t) :
    schurTripleCount s ≤ 3 * (s \ t).card * s.card ^ 2 := by
  classical
  have hsub : schurTriples s
      ⊆ (s \ t) ×ˢ (s ×ˢ s) ∪ s ×ˢ ((s \ t) ×ˢ s)
          ∪ s ×ˢ (s ×ˢ (s \ t)) := by
    rintro ⟨x, y, z⟩ hp
    rw [schurTriples, Finset.mem_filter, Finset.mem_product,
      Finset.mem_product] at hp
    obtain ⟨⟨hx, hy, hz⟩, heq⟩ := hp
    have heq' : x + y = z := heq
    rcases em (x ∈ t) with hxt | hxt
    · rcases em (y ∈ t) with hyt | hyt
      · rcases em (z ∈ t) with hzt | hzt
        · rw [← heq'] at hzt
          exact absurd hzt (ht x hxt y hyt)
        · refine Finset.mem_union_right _
            (Finset.mem_product.mpr ⟨hx, ?_⟩)
          exact Finset.mem_product.mpr
            ⟨hy, Finset.mem_sdiff.mpr ⟨hz, hzt⟩⟩
      · refine Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_product.mpr ⟨hx, ?_⟩))
        exact Finset.mem_product.mpr
          ⟨Finset.mem_sdiff.mpr ⟨hy, hyt⟩, hz⟩
    · refine Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_product.mpr ⟨Finset.mem_sdiff.mpr ⟨hx, hxt⟩, ?_⟩))
      exact Finset.mem_product.mpr ⟨hy, hz⟩
  have hcard : ((s \ t) ×ˢ (s ×ˢ s) ∪ s ×ˢ ((s \ t) ×ˢ s)
      ∪ s ×ˢ (s ×ˢ (s \ t))).card
      ≤ 3 * (s \ t).card * s.card ^ 2 := by
    have e1 : ((s \ t) ×ˢ (s ×ˢ s)).card
        = (s \ t).card * (s.card * s.card) := by
      rw [Finset.card_product, Finset.card_product]
    have e2 : (s ×ˢ ((s \ t) ×ˢ s)).card
        = s.card * ((s \ t).card * s.card) := by
      rw [Finset.card_product, Finset.card_product]
    have e3 : (s ×ˢ (s ×ˢ (s \ t))).card
        = s.card * (s.card * (s \ t).card) := by
      rw [Finset.card_product, Finset.card_product]
    have h1 := Finset.card_union_le
      ((s \ t) ×ˢ (s ×ˢ s) ∪ s ×ˢ ((s \ t) ×ˢ s)) (s ×ˢ (s ×ˢ (s \ t)))
    have h2 := Finset.card_union_le ((s \ t) ×ˢ (s ×ˢ s))
      (s ×ˢ ((s \ t) ×ˢ s))
    have hle : ((s \ t) ×ˢ (s ×ˢ s) ∪ s ×ˢ ((s \ t) ×ˢ s)
        ∪ s ×ˢ (s ×ˢ (s \ t))).card
        ≤ (s \ t).card * (s.card * s.card)
            + s.card * ((s \ t).card * s.card)
            + s.card * (s.card * (s \ t).card) := by
      omega
    refine hle.trans_eq ?_
    ring
  calc schurTripleCount s
      ≤ ((s \ t) ×ˢ (s ×ˢ s) ∪ s ×ˢ ((s \ t) ×ˢ s)
          ∪ s ×ˢ (s ×ˢ (s \ t))).card := Finset.card_le_card hsub
    _ ≤ 3 * (s \ t).card * s.card ^ 2 := hcard

end JSP000728
