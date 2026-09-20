import JSPProblem.RemovalFragment
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Lattice.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# JSP-000728 — balanced supersaturation for Schur triples

The *averaging* engine for the container argument: if `s` has many Schur
triples, then many elements of `s` are *heavy* — they occur as the top (or
as a summand) of many triples.  These are the elementary "balanced
supersaturation" inputs feeding the fingerprint iteration.

## Contents

* **Fibers.** `card_schurTriples_fiber_top` / `card_schurTriples_fiber_fst`:
  the fiber of `schurTriples s` over a fixed top `z` (resp. first summand
  `x`) has size `|{a ∈ s : z - a ∈ s}|` (resp. `|{b ∈ s : x + b ∈ s}|`).
* **Averaging** (`schurTripleCount_le_mul_add_card_mul` and `_fst`):
  `schurTripleCount s ≤ |s|·ω + (heavy vertices)·|s|`, so a large triple
  count forces many heavy tops (`exists_heavy_tops`) or heavy summands
  (`exists_heavy_summands`).
* **Deletion bookkeeping** (`schurTripleCount_erase_add_fiber_le`,
  `schurTripleCount_sdiff_add_sum_fiber_le`,
  `schurTripleCount_sdiff_le_of_heavy`): erasing a vertex kills at least
  its top-fiber; erasing a set `h` kills at least `∑_{x ∈ h}` of the
  top-fibers, hence at least `|h|·ω` when all deleted vertices are heavy.
  This is the fingerprint-termination accounting.
* **Disjoint packings / hitting sets** (`DisjointSchurTriples`,
  `exists_maximal_disjointSchurTriples`, `exists_hittingSet_card_le`,
  `exists_isSumFree_sub_card_le_packing`): a maximal pairwise
  vertex-disjoint family `P` of Schur triples of `s` covers all triples by
  its `≤ 3|P|` vertices, so `s` becomes sum-free after deleting them.
* **Special removal cases** (`isSumFree_filter_upper`,
  `removal_of_small_low_part`): the part of `C ⊆ {1,…,n}` above `n/2` is
  automatically sum-free, so the removal number is bounded by the size of
  the low part.
* **Band counting** (`schurTripleCount_ge_of_band`,
  `schurTripleCount_ge_of_low_dense`): for `L ⊆ (n/4, n/2] ∩ C`, the pairs
  `(a, b) ∈ L²` land in `(n/2, n]`, and injectivity of `a ↦ a + b` bounds
  the triple count below by `|L|² − |L|·|(n/2,n] ∖ U|` for `U ⊆ C ∩ (n/2,n]`.
-/

namespace JSP000728

/-! ## Fibers of the Schur-triple set -/

/-- The fiber of `schurTriples s` over a fixed top `z ∈ s` bijects with
`{x ∈ s : z - x ∈ s}` via `x ↦ (x, z - x, z)`. -/
theorem card_schurTriples_fiber_top (s : Finset ℤ) {z : ℤ} (hz : z ∈ s) :
    ((schurTriples s).filter fun t => t.2.2 = z).card
      = (s.filter fun x => z - x ∈ s).card := by
  classical
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
    exact (Prod.mk_inj.mp h).1
  rw [hfiber, Finset.card_image_of_injective _ hinj]

/-- The fiber of `schurTriples s` over a fixed first summand `x ∈ s` bijects
with `{y ∈ s : x + y ∈ s}` via `y ↦ (x, y, x + y)`. -/
theorem card_schurTriples_fiber_fst (s : Finset ℤ) {x : ℤ} (hx : x ∈ s) :
    ((schurTriples s).filter fun t => t.1 = x).card
      = (s.filter fun y => x + y ∈ s).card := by
  classical
  have hfiber : ((schurTriples s).filter fun t => t.1 = x)
      = (s.filter fun y => x + y ∈ s).image fun y => (x, y, x + y) := by
    apply subset_antisymm
    · intro a ha
      obtain ⟨ha1, ha2⟩ := Finset.mem_filter.mp ha
      rcases a with ⟨b, c, d⟩
      rw [schurTriples, Finset.mem_filter, Finset.mem_product,
        Finset.mem_product] at ha1
      obtain ⟨⟨hb, hc, hd⟩, hsum⟩ := ha1
      have hsum' : b + c = d := hsum
      have ha2' : b = x := ha2
      rw [Finset.mem_image]
      refine ⟨c, ?_, ?_⟩
      · rw [Finset.mem_filter]
        refine ⟨hc, ?_⟩
        have h1 : x + c = d := by omega
        exact h1 ▸ hd
      · show (x, c, x + c) = (b, c, d)
        rw [← ha2', hsum']
    · intro a ha
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨hys, hxy⟩ := Finset.mem_filter.mp hy
      rw [Finset.mem_filter]
      refine ⟨?_, rfl⟩
      rw [schurTriples, Finset.mem_filter, Finset.mem_product,
        Finset.mem_product]
      exact ⟨⟨hx, hys, hxy⟩, rfl⟩
  have hinj : Function.Injective fun y : ℤ => (x, y, x + y) := by
    intro a b h
    exact (Prod.mk_inj.mp (Prod.mk_inj.mp h).2).1
  rw [hfiber, Finset.card_image_of_injective _ hinj]

/-- The Schur-triple count as a sum over first summands:
`schurTripleCount s = ∑ x ∈ s, |{y ∈ s : x + y ∈ s}|`. -/
theorem schurTripleCount_eq_sum_fst (s : Finset ℤ) :
    schurTripleCount s = ∑ x ∈ s, (s.filter fun y => x + y ∈ s).card := by
  classical
  have hmem : (↑(schurTriples s) : Set (ℤ × ℤ × ℤ)).MapsTo
      (fun t => t.1) ↑s := by
    intro t ht
    rw [Finset.mem_coe] at ht ⊢
    rw [schurTriples, Finset.mem_filter, Finset.mem_product,
      Finset.mem_product] at ht
    exact ht.1.1
  have key : schurTripleCount s
      = ∑ x ∈ s, ((schurTriples s).filter fun t => t.1 = x).card := by
    rw [schurTripleCount]
    exact Finset.card_eq_sum_card_fiberwise hmem
  rw [key]
  exact Finset.sum_congr rfl fun x hx => card_schurTriples_fiber_fst s hx

/-! ## Averaging: many triples force many heavy vertices -/

/-- **Light/heavy top decomposition.**  Splitting
`schurTripleCount s = ∑ z ∈ s, |{x ∈ s : z - x ∈ s}|` into light tops
(`< ω` triples) and heavy tops (`≥ ω` triples), bounding each light fiber
by `ω` and each heavy fiber by `|s|`, gives
`schurTripleCount s ≤ |s|·ω + (heavy tops)·|s|`. -/
theorem schurTripleCount_le_mul_add_card_mul (s : Finset ℤ) (ω : ℕ) :
    schurTripleCount s
      ≤ s.card * ω
        + (s.filter fun z => ω
            ≤ (s.filter fun x => z - x ∈ s).card).card * s.card := by
  classical
  have hsplit := Finset.sum_filter_add_sum_filter_not s
    (fun z => ω ≤ (s.filter fun x => z - x ∈ s).card)
    (fun z => (s.filter fun x => z - x ∈ s).card)
  rw [schurTripleCount_eq_sum_filter s, ← hsplit]
  have hHeavy : ∑ z ∈ s.filter
        (fun z => ω ≤ (s.filter fun x => z - x ∈ s).card),
        (s.filter fun x => z - x ∈ s).card
      ≤ (s.filter fun z => ω
          ≤ (s.filter fun x => z - x ∈ s).card).card * s.card := by
    calc ∑ z ∈ s.filter
          (fun z => ω ≤ (s.filter fun x => z - x ∈ s).card),
          (s.filter fun x => z - x ∈ s).card
        ≤ ∑ _z ∈ s.filter
            (fun z => ω ≤ (s.filter fun x => z - x ∈ s).card), s.card :=
          Finset.sum_le_sum fun z _ => Finset.card_filter_le _ _
      _ = (s.filter fun z => ω
            ≤ (s.filter fun x => z - x ∈ s).card).card * s.card := by
          rw [Finset.sum_const, smul_eq_mul]
  have hLight : ∑ z ∈ s.filter
        (fun z => ¬ ω ≤ (s.filter fun x => z - x ∈ s).card),
        (s.filter fun x => z - x ∈ s).card
      ≤ s.card * ω := by
    calc ∑ z ∈ s.filter
          (fun z => ¬ ω ≤ (s.filter fun x => z - x ∈ s).card),
          (s.filter fun x => z - x ∈ s).card
        ≤ ∑ _z ∈ s.filter
            (fun z => ¬ ω ≤ (s.filter fun x => z - x ∈ s).card), ω := by
          apply Finset.sum_le_sum
          intro z hz
          rw [Finset.mem_filter] at hz
          exact (not_le.mp hz.2).le
      _ = (s.filter fun z => ¬ ω
            ≤ (s.filter fun x => z - x ∈ s).card).card * ω := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ s.card * ω :=
          Nat.mul_le_mul_right _ (Finset.card_filter_le _ _)
  calc ∑ z ∈ s.filter
        (fun z => ω ≤ (s.filter fun x => z - x ∈ s).card),
        (s.filter fun x => z - x ∈ s).card
      + ∑ z ∈ s.filter
          (fun z => ¬ ω ≤ (s.filter fun x => z - x ∈ s).card),
          (s.filter fun x => z - x ∈ s).card
      ≤ (s.filter fun z => ω
            ≤ (s.filter fun x => z - x ∈ s).card).card * s.card
          + s.card * ω := Nat.add_le_add hHeavy hLight
    _ = s.card * ω
          + (s.filter fun z => ω
              ≤ (s.filter fun x => z - x ∈ s).card).card * s.card := by
        ring

/-- **Light/heavy summand decomposition**, the first-summand analogue of
`schurTripleCount_le_mul_add_card_mul`. -/
theorem schurTripleCount_le_mul_add_card_mul_fst (s : Finset ℤ) (ω : ℕ) :
    schurTripleCount s
      ≤ s.card * ω
        + (s.filter fun x => ω
            ≤ (s.filter fun y => x + y ∈ s).card).card * s.card := by
  classical
  have hsplit := Finset.sum_filter_add_sum_filter_not s
    (fun x => ω ≤ (s.filter fun y => x + y ∈ s).card)
    (fun x => (s.filter fun y => x + y ∈ s).card)
  rw [schurTripleCount_eq_sum_fst s, ← hsplit]
  have hHeavy : ∑ x ∈ s.filter
        (fun x => ω ≤ (s.filter fun y => x + y ∈ s).card),
        (s.filter fun y => x + y ∈ s).card
      ≤ (s.filter fun x => ω
          ≤ (s.filter fun y => x + y ∈ s).card).card * s.card := by
    calc ∑ x ∈ s.filter
          (fun x => ω ≤ (s.filter fun y => x + y ∈ s).card),
          (s.filter fun y => x + y ∈ s).card
        ≤ ∑ _x ∈ s.filter
            (fun x => ω ≤ (s.filter fun y => x + y ∈ s).card), s.card :=
          Finset.sum_le_sum fun x _ => Finset.card_filter_le _ _
      _ = (s.filter fun x => ω
            ≤ (s.filter fun y => x + y ∈ s).card).card * s.card := by
          rw [Finset.sum_const, smul_eq_mul]
  have hLight : ∑ x ∈ s.filter
        (fun x => ¬ ω ≤ (s.filter fun y => x + y ∈ s).card),
        (s.filter fun y => x + y ∈ s).card
      ≤ s.card * ω := by
    calc ∑ x ∈ s.filter
          (fun x => ¬ ω ≤ (s.filter fun y => x + y ∈ s).card),
          (s.filter fun y => x + y ∈ s).card
        ≤ ∑ _x ∈ s.filter
            (fun x => ¬ ω ≤ (s.filter fun y => x + y ∈ s).card), ω := by
          apply Finset.sum_le_sum
          intro x hx
          rw [Finset.mem_filter] at hx
          exact (not_le.mp hx.2).le
      _ = (s.filter fun x => ¬ ω
            ≤ (s.filter fun y => x + y ∈ s).card).card * ω := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ s.card * ω :=
          Nat.mul_le_mul_right _ (Finset.card_filter_le _ _)
  calc ∑ x ∈ s.filter
        (fun x => ω ≤ (s.filter fun y => x + y ∈ s).card),
        (s.filter fun y => x + y ∈ s).card
      + ∑ x ∈ s.filter
          (fun x => ¬ ω ≤ (s.filter fun y => x + y ∈ s).card),
          (s.filter fun y => x + y ∈ s).card
      ≤ (s.filter fun x => ω
            ≤ (s.filter fun y => x + y ∈ s).card).card * s.card
          + s.card * ω := Nat.add_le_add hHeavy hLight
    _ = s.card * ω
          + (s.filter fun x => ω
              ≤ (s.filter fun y => x + y ∈ s).card).card * s.card := by
        ring

/-- The number of heavy tops times `|s|` dominates the triple count beyond
the light contribution `|s|·ω`. -/
theorem heavyTops_card_mul_ge (s : Finset ℤ) (ω : ℕ) :
    schurTripleCount s - s.card * ω
      ≤ (s.filter fun z => ω
          ≤ (s.filter fun x => z - x ∈ s).card).card * s.card := by
  have h := schurTripleCount_le_mul_add_card_mul s ω
  omega

/-- The summand analogue of `heavyTops_card_mul_ge`. -/
theorem heavySummands_card_mul_ge (s : Finset ℤ) (ω : ℕ) :
    schurTripleCount s - s.card * ω
      ≤ (s.filter fun x => ω
          ≤ (s.filter fun y => x + y ∈ s).card).card * s.card := by
  have h := schurTripleCount_le_mul_add_card_mul_fst s ω
  omega

/-- **Many heavy tops.**  If `s ⊆ {1,…,n}` has at least `δ·n²` Schur
triples and `ω ≤ δ·n/2`, then at least `δ·n/2` elements `z ∈ s` are the
top of at least `ω` triples: light tops account for at most
`|s|·ω ≤ δ·n²/2` triples, so the remaining `≥ δ·n²/2` triples need
`≥ δ·n/2` heavy tops (each carrying at most `|s| ≤ n` triples). -/
theorem exists_heavy_tops {n : ℕ} {s : Finset ℤ} (hsub : s ⊆ interval n)
    {ω : ℕ} {δ : ℝ} (hn : 0 < n)
    (hω : (ω : ℝ) ≤ δ * (n : ℝ) / 2)
    (hcount : δ * (n : ℝ) ^ 2 ≤ schurTripleCount s) :
    δ * (n : ℝ) / 2
      ≤ ((s.filter fun z => ω
          ≤ (s.filter fun x => z - x ∈ s).card).card : ℝ) := by
  classical
  have hcard : (s.card : ℝ) ≤ n := by
    have hc := Finset.card_le_card hsub
    rw [card_interval] at hc
    exact_mod_cast hc
  have hnn : (0 : ℝ) < n := by exact_mod_cast hn
  have havg : (schurTripleCount s : ℝ)
      ≤ s.card * ω
        + ((s.filter fun z => ω
            ≤ (s.filter fun x => z - x ∈ s).card).card : ℝ) * s.card := by
    exact_mod_cast schurTripleCount_le_mul_add_card_mul s ω
  have hωn : (s.card : ℝ) * (ω : ℝ) ≤ n * ω :=
    mul_le_mul_of_nonneg_right hcard (Nat.cast_nonneg _)
  have hHn : ((s.filter fun z => ω
        ≤ (s.filter fun x => z - x ∈ s).card).card : ℝ) * s.card
      ≤ ((s.filter fun z => ω
        ≤ (s.filter fun x => z - x ∈ s).card).card : ℝ) * n :=
    mul_le_mul_of_nonneg_left hcard (Nat.cast_nonneg _)
  have hnω : (n : ℝ) * (ω : ℝ) ≤ (δ * n / 2) * n := by
    have h1 := mul_le_mul_of_nonneg_left hω hnn.le
    have h2 : (n : ℝ) * (δ * n / 2) = (δ * n / 2) * n := mul_comm _ _
    rwa [h2] at h1
  have key : (δ * (n : ℝ) / 2) * n
      ≤ ((s.filter fun z => ω
        ≤ (s.filter fun x => z - x ∈ s).card).card : ℝ) * n := by
    have e : δ * (n : ℝ) ^ 2 = 2 * ((δ * n / 2) * n) := by ring
    linarith [hcount, havg, hωn, hHn, hnω]
  exact le_of_mul_le_mul_right key hnn

/-- **Many heavy summands**, the first-summand analogue of
`exists_heavy_tops`. -/
theorem exists_heavy_summands {n : ℕ} {s : Finset ℤ} (hsub : s ⊆ interval n)
    {ω : ℕ} {δ : ℝ} (hn : 0 < n)
    (hω : (ω : ℝ) ≤ δ * (n : ℝ) / 2)
    (hcount : δ * (n : ℝ) ^ 2 ≤ schurTripleCount s) :
    δ * (n : ℝ) / 2
      ≤ ((s.filter fun x => ω
          ≤ (s.filter fun y => x + y ∈ s).card).card : ℝ) := by
  classical
  have hcard : (s.card : ℝ) ≤ n := by
    have hc := Finset.card_le_card hsub
    rw [card_interval] at hc
    exact_mod_cast hc
  have hnn : (0 : ℝ) < n := by exact_mod_cast hn
  have havg : (schurTripleCount s : ℝ)
      ≤ s.card * ω
        + ((s.filter fun x => ω
            ≤ (s.filter fun y => x + y ∈ s).card).card : ℝ) * s.card := by
    exact_mod_cast schurTripleCount_le_mul_add_card_mul_fst s ω
  have hωn : (s.card : ℝ) * (ω : ℝ) ≤ n * ω :=
    mul_le_mul_of_nonneg_right hcard (Nat.cast_nonneg _)
  have hHn : ((s.filter fun x => ω
        ≤ (s.filter fun y => x + y ∈ s).card).card : ℝ) * s.card
      ≤ ((s.filter fun x => ω
        ≤ (s.filter fun y => x + y ∈ s).card).card : ℝ) * n :=
    mul_le_mul_of_nonneg_left hcard (Nat.cast_nonneg _)
  have hnω : (n : ℝ) * (ω : ℝ) ≤ (δ * n / 2) * n := by
    have h1 := mul_le_mul_of_nonneg_left hω hnn.le
    have h2 : (n : ℝ) * (δ * n / 2) = (δ * n / 2) * n := mul_comm _ _
    rwa [h2] at h1
  have key : (δ * (n : ℝ) / 2) * n
      ≤ ((s.filter fun x => ω
        ≤ (s.filter fun y => x + y ∈ s).card).card : ℝ) * n := by
    have e : δ * (n : ℝ) ^ 2 = 2 * ((δ * n / 2) * n) := by ring
    linarith [hcount, havg, hωn, hHn, hnω]
  exact le_of_mul_le_mul_right key hnn

/-! ## Deletion bookkeeping -/

/-- Erasing `z ∈ s` destroys at least the whole top-fiber over `z`:
the triples of `s.erase z` are disjoint from the `z`-topped triples of
`s`. -/
theorem schurTripleCount_erase_add_fiber_le (s : Finset ℤ) {z : ℤ}
    (hz : z ∈ s) :
    schurTripleCount (s.erase z) + (s.filter fun x => z - x ∈ s).card
      ≤ schurTripleCount s := by
  classical
  have hsub : schurTriples (s.erase z)
      ⊆ (schurTriples s).filter fun t => ¬ t.2.2 = z := by
    intro t ht
    rw [Finset.mem_filter]
    refine ⟨schurTriples_mono (Finset.erase_subset z s) ht, ?_⟩
    rw [schurTriples, Finset.mem_filter, Finset.mem_product,
      Finset.mem_product] at ht
    exact (Finset.mem_erase.mp ht.1.2.2).1
  have hle := Finset.card_le_card hsub
  have hpart := Finset.card_filter_add_card_filter_not
    (s := schurTriples s) (p := fun t => t.2.2 = z)
  have hfib := card_schurTriples_fiber_top s hz
  unfold schurTripleCount at hfib hpart ⊢
  omega

/-- Erasing `x ∈ s` destroys at least the whole first-summand fiber over
`x`. -/
theorem schurTripleCount_erase_add_fiber_fst_le (s : Finset ℤ) {x : ℤ}
    (hx : x ∈ s) :
    schurTripleCount (s.erase x) + (s.filter fun y => x + y ∈ s).card
      ≤ schurTripleCount s := by
  classical
  have hsub : schurTriples (s.erase x)
      ⊆ (schurTriples s).filter fun t => ¬ t.1 = x := by
    intro t ht
    rw [Finset.mem_filter]
    refine ⟨schurTriples_mono (Finset.erase_subset x s) ht, ?_⟩
    rw [schurTriples, Finset.mem_filter, Finset.mem_product,
      Finset.mem_product] at ht
    exact (Finset.mem_erase.mp ht.1.1).1
  have hle := Finset.card_le_card hsub
  have hpart := Finset.card_filter_add_card_filter_not
    (s := schurTriples s) (p := fun t => t.1 = x)
  have hfib := card_schurTriples_fiber_fst s hx
  unfold schurTripleCount at hfib hpart ⊢
  omega

/-- **Iteration bookkeeping (tops).**  Erasing a set `h ⊆ s` destroys at
least the sum of the top-fibers over `h`: triples of `s ∖ h` have top
`∉ h`, while the `h`-topped triples of `s` (counted exactly by the fiber
sum) are all destroyed. -/
theorem schurTripleCount_sdiff_add_sum_fiber_le {s h : Finset ℤ}
    (hh : h ⊆ s) :
    schurTripleCount (s \ h)
      + ∑ x ∈ h, (s.filter fun a => x - a ∈ s).card
        ≤ schurTripleCount s := by
  classical
  have hsub : schurTriples (s \ h)
      ⊆ (schurTriples s).filter fun t => ¬ t.2.2 ∈ h := by
    intro t ht
    rw [Finset.mem_filter]
    refine ⟨schurTriples_mono Finset.sdiff_subset ht, ?_⟩
    rw [schurTriples, Finset.mem_filter, Finset.mem_product,
      Finset.mem_product] at ht
    exact fun hc => (Finset.mem_sdiff.mp ht.1.2.2).2 hc
  have hle := Finset.card_le_card hsub
  have hsum : ((schurTriples s).filter fun t => t.2.2 ∈ h).card
      = ∑ x ∈ h, (s.filter fun a => x - a ∈ s).card := by
    have hmap : (↑((schurTriples s).filter fun t => t.2.2 ∈ h)
          : Set (ℤ × ℤ × ℤ)).MapsTo (fun t => t.2.2) ↑h := by
      intro t ht
      rw [Finset.mem_coe] at ht ⊢
      exact (Finset.mem_filter.mp ht).2
    rw [Finset.card_eq_sum_card_fiberwise hmap]
    apply Finset.sum_congr rfl
    intro x hx
    have e : ((schurTriples s).filter fun t => t.2.2 ∈ h).filter
        (fun t => t.2.2 = x)
        = (schurTriples s).filter fun t => t.2.2 = x := by
      rw [Finset.filter_filter]
      apply Finset.filter_congr
      intro t _
      constructor
      · rintro ⟨-, htx⟩; exact htx
      · intro htx; exact ⟨by rw [htx]; exact hx, htx⟩
    rw [e]
    exact card_schurTriples_fiber_top s (hh hx)
  have hpart := Finset.card_filter_add_card_filter_not
    (s := schurTriples s) (p := fun t => t.2.2 ∈ h)
  unfold schurTripleCount at hpart ⊢
  omega

/-- **Iteration bookkeeping (first summands)**, the analogue of
`schurTripleCount_sdiff_add_sum_fiber_le` for the first coordinate. -/
theorem schurTripleCount_sdiff_add_sum_fiber_fst_le {s h : Finset ℤ}
    (hh : h ⊆ s) :
    schurTripleCount (s \ h)
      + ∑ x ∈ h, (s.filter fun b => x + b ∈ s).card
        ≤ schurTripleCount s := by
  classical
  have hsub : schurTriples (s \ h)
      ⊆ (schurTriples s).filter fun t => ¬ t.1 ∈ h := by
    intro t ht
    rw [Finset.mem_filter]
    refine ⟨schurTriples_mono Finset.sdiff_subset ht, ?_⟩
    rw [schurTriples, Finset.mem_filter, Finset.mem_product,
      Finset.mem_product] at ht
    exact fun hc => (Finset.mem_sdiff.mp ht.1.1).2 hc
  have hle := Finset.card_le_card hsub
  have hsum : ((schurTriples s).filter fun t => t.1 ∈ h).card
      = ∑ x ∈ h, (s.filter fun b => x + b ∈ s).card := by
    have hmap : (↑((schurTriples s).filter fun t => t.1 ∈ h)
          : Set (ℤ × ℤ × ℤ)).MapsTo (fun t => t.1) ↑h := by
      intro t ht
      rw [Finset.mem_coe] at ht ⊢
      exact (Finset.mem_filter.mp ht).2
    rw [Finset.card_eq_sum_card_fiberwise hmap]
    apply Finset.sum_congr rfl
    intro x hx
    have e : ((schurTriples s).filter fun t => t.1 ∈ h).filter
        (fun t => t.1 = x)
        = (schurTriples s).filter fun t => t.1 = x := by
      rw [Finset.filter_filter]
      apply Finset.filter_congr
      intro t _
      constructor
      · rintro ⟨-, htx⟩; exact htx
      · intro htx; exact ⟨by rw [htx]; exact hx, htx⟩
    rw [e]
    exact card_schurTriples_fiber_fst s (hh hx)
  have hpart := Finset.card_filter_add_card_filter_not
    (s := schurTriples s) (p := fun t => t.1 ∈ h)
  unfold schurTripleCount at hpart ⊢
  omega

/-- **Heavy deletion drops the count.**  Erasing `h ⊆ s`, where every
`x ∈ h` is a heavy top (`≥ ω` triples over it), drops the Schur-triple
count by at least `|h|·ω`.  The `ω`-heaviness may be measured in `s`
itself, hence also at any intermediate deletion stage. -/
theorem schurTripleCount_sdiff_le_of_heavy {s h : Finset ℤ} {ω : ℕ}
    (hh : h ⊆ s)
    (hheavy : ∀ x ∈ h, ω ≤ (s.filter fun a => x - a ∈ s).card) :
    schurTripleCount (s \ h) + h.card * ω ≤ schurTripleCount s := by
  have h1 := schurTripleCount_sdiff_add_sum_fiber_le hh
  have h2 : h.card * ω ≤ ∑ x ∈ h, (s.filter fun a => x - a ∈ s).card := by
    calc h.card * ω = ∑ _x ∈ h, ω := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ x ∈ h, (s.filter fun a => x - a ∈ s).card :=
          Finset.sum_le_sum hheavy
  omega

/-- The first-summand analogue of `schurTripleCount_sdiff_le_of_heavy`. -/
theorem schurTripleCount_sdiff_le_of_heavy_fst {s h : Finset ℤ} {ω : ℕ}
    (hh : h ⊆ s)
    (hheavy : ∀ x ∈ h, ω ≤ (s.filter fun b => x + b ∈ s).card) :
    schurTripleCount (s \ h) + h.card * ω ≤ schurTripleCount s := by
  have h1 := schurTripleCount_sdiff_add_sum_fiber_fst_le hh
  have h2 : h.card * ω ≤ ∑ x ∈ h, (s.filter fun b => x + b ∈ s).card := by
    calc h.card * ω = ∑ _x ∈ h, ω := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ x ∈ h, (s.filter fun b => x + b ∈ s).card :=
          Finset.sum_le_sum hheavy
  omega

/-! ## Disjoint packings and hitting sets -/

/-- The vertex set `{t.1, t.2.1, t.2.2}` of a triple `t = (a, b, c)`. -/
def tripleVertices (t : ℤ × ℤ × ℤ) : Finset ℤ := {t.1, t.2.1, t.2.2}

theorem mem_tripleVertices {t : ℤ × ℤ × ℤ} {a : ℤ} :
    a ∈ tripleVertices t ↔ a = t.1 ∨ a = t.2.1 ∨ a = t.2.2 := by
  simp [tripleVertices]

theorem tripleVertices_card_le (t : ℤ × ℤ × ℤ) :
    (tripleVertices t).card ≤ 3 := by
  have h1 := Finset.card_insert_le t.1
    (insert t.2.1 ({t.2.2} : Finset ℤ))
  have h2 := Finset.card_insert_le t.2.1 ({t.2.2} : Finset ℤ)
  have h3 : ({t.2.2} : Finset ℤ).card = 1 := Finset.card_singleton _
  have e : tripleVertices t
      = insert t.1 (insert t.2.1 ({t.2.2} : Finset ℤ)) := rfl
  rw [e]
  omega

theorem fst_mem_tripleVertices (t : ℤ × ℤ × ℤ) :
    t.1 ∈ tripleVertices t :=
  Finset.mem_insert_self _ _

theorem tripleVertices_nonempty (t : ℤ × ℤ × ℤ) :
    (tripleVertices t).Nonempty :=
  ⟨t.1, fst_mem_tripleVertices t⟩

theorem tripleVertices_subset {s : Finset ℤ} {t : ℤ × ℤ × ℤ}
    (ht : t ∈ schurTriples s) : tripleVertices t ⊆ s := by
  rw [schurTriples, Finset.mem_filter, Finset.mem_product,
    Finset.mem_product] at ht
  intro x hx
  rw [mem_tripleVertices] at hx
  rcases hx with rfl | rfl | rfl
  · exact ht.1.1
  · exact ht.1.2.1
  · exact ht.1.2.2

/-- A family of triples with pairwise vertex-disjoint members. -/
def DisjointSchurTriples (P : Finset (ℤ × ℤ × ℤ)) : Prop :=
  ∀ p ∈ P, ∀ q ∈ P, p ≠ q →
    Disjoint (tripleVertices p) (tripleVertices q)

/-- **Maximal disjoint packing.**  Among subfamilies of `schurTriples s`
that are pairwise vertex-disjoint there is a maximal one `P`, and
maximality means every Schur triple of `s` shares a vertex with some
member of `P`. -/
theorem exists_maximal_disjointSchurTriples (s : Finset ℤ) :
    ∃ P : Finset (ℤ × ℤ × ℤ), P ⊆ schurTriples s ∧ DisjointSchurTriples P ∧
      ∀ t ∈ schurTriples s,
        ∃ p ∈ P, (tripleVertices t ∩ tripleVertices p).Nonempty := by
  classical
  set fam := (schurTriples s).powerset.filter DisjointSchurTriples with hfam
  have hne : fam.Nonempty := by
    refine ⟨∅, ?_⟩
    rw [hfam, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.empty_subset _,
      fun p hp => (Finset.notMem_empty _ hp).elim⟩
  obtain ⟨P, hPfam, hPmax⟩ := Finset.exists_max_image fam Finset.card hne
  rw [hfam, Finset.mem_filter, Finset.mem_powerset] at hPfam
  obtain ⟨hPsub, hPdisj⟩ := hPfam
  refine ⟨P, hPsub, hPdisj, fun t ht => ?_⟩
  rcases em (∃ p ∈ P,
      (tripleVertices t ∩ tripleVertices p).Nonempty) with h | hcon
  · exact h
  · exfalso
    have hall : ∀ p ∈ P,
        Disjoint (tripleVertices t) (tripleVertices p) := by
      intro p hp
      have hnp : ¬ (tripleVertices t ∩ tripleVertices p).Nonempty :=
        fun hh => hcon ⟨p, hp, hh⟩
      rw [Finset.not_nonempty_iff_eq_empty] at hnp
      exact Finset.disjoint_iff_inter_eq_empty.mpr hnp
    have htP : t ∉ P := by
      intro htP
      have h := hall t htP
      rw [Finset.disjoint_self_iff_empty] at h
      have := fst_mem_tripleVertices t
      rw [h] at this
      exact Finset.notMem_empty _ this
    have hdisj' : DisjointSchurTriples (insert t P) := by
      intro p₁ hp₁ p₂ hp₂ hne12
      rw [Finset.mem_insert] at hp₁ hp₂
      rcases hp₁ with rfl | hp₁ <;> rcases hp₂ with rfl | hp₂
      · exact absurd rfl hne12
      · exact hall p₂ hp₂
      · exact (hall p₁ hp₁).symm
      · exact hPdisj p₁ hp₁ p₂ hp₂ hne12
    have hmem : insert t P ∈ fam := by
      rw [hfam, Finset.mem_filter, Finset.mem_powerset]
      exact ⟨Finset.insert_subset ht hPsub, hdisj'⟩
    have hcard := hPmax (insert t P) hmem
    rw [Finset.card_insert_of_notMem htP] at hcard
    omega

/-- **Hitting set from a packing.**  The `≤ 3|P|` vertices of a maximal
disjoint family `P` hit every Schur triple of `s`. -/
theorem exists_hittingSet_card_le (s : Finset ℤ) :
    ∃ P : Finset (ℤ × ℤ × ℤ), P ⊆ schurTriples s ∧ DisjointSchurTriples P ∧
      ∃ h : Finset ℤ, h ⊆ s ∧ h.card ≤ 3 * P.card ∧
        ∀ t ∈ schurTriples s, (tripleVertices t ∩ h).Nonempty := by
  classical
  obtain ⟨P, hPsub, hPdisj, hPmax⟩ := exists_maximal_disjointSchurTriples s
  refine ⟨P, hPsub, hPdisj, P.biUnion tripleVertices, ?_, ?_, ?_⟩
  · intro x hx
    rw [Finset.mem_biUnion] at hx
    obtain ⟨p, hp, hxp⟩ := hx
    exact tripleVertices_subset (hPsub hp) hxp
  · calc (P.biUnion tripleVertices).card
        ≤ ∑ p ∈ P, (tripleVertices p).card := Finset.card_biUnion_le
      _ ≤ ∑ _p ∈ P, 3 :=
          Finset.sum_le_sum fun p _ => tripleVertices_card_le p
      _ = 3 * P.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  · intro t ht
    obtain ⟨p, hp, hpp⟩ := hPmax t ht
    obtain ⟨x, hx⟩ := hpp
    rw [Finset.mem_inter] at hx
    exact ⟨x, Finset.mem_inter.mpr
      ⟨hx.1, Finset.mem_biUnion.mpr ⟨p, hp, hx.2⟩⟩⟩

/-- **Removal bound by packing number.**  Deleting the `≤ 3|P|` vertices
of a maximal disjoint family `P` leaves a sum-free set:
`|s ∖ t| ≤ 3·|P|`. -/
theorem exists_isSumFree_sub_card_le_packing (s : Finset ℤ) :
    ∃ t : Finset ℤ, t ⊆ s ∧ IsSumFree t ∧
      ∃ P : Finset (ℤ × ℤ × ℤ), P ⊆ schurTriples s ∧
        DisjointSchurTriples P ∧ (s \ t).card ≤ 3 * P.card := by
  classical
  obtain ⟨P, hPsub, hPdisj, h, hhs, hhcard, hhit⟩ :=
    exists_hittingSet_card_le s
  refine ⟨s \ h, Finset.sdiff_subset, ?_, P, hPsub, hPdisj, ?_⟩
  · intro x hx y hy hxy
    obtain ⟨hxs, hxh⟩ := Finset.mem_sdiff.mp hx
    obtain ⟨hys, hyh⟩ := Finset.mem_sdiff.mp hy
    obtain ⟨hxys, hxyh⟩ := Finset.mem_sdiff.mp hxy
    have htri : (x, y, x + y) ∈ schurTriples s := by
      rw [schurTriples, Finset.mem_filter, Finset.mem_product,
        Finset.mem_product]
      exact ⟨⟨hxs, hys, hxys⟩, rfl⟩
    obtain ⟨a, ha⟩ := hhit _ htri
    rw [Finset.mem_inter] at ha
    obtain ⟨ha1, ha2⟩ := ha
    rw [mem_tripleVertices] at ha1
    rcases ha1 with rfl | rfl | rfl
    · exact hxh ha2
    · exact hyh ha2
    · exact hxyh ha2
  · have e : s \ (s \ h) = h := Finset.sdiff_sdiff_eq_self hhs
    rw [e]
    exact hhcard

/-! ## Special removal cases -/

/-- The part of `C ⊆ {1,…,n}` lying above `n/2` is sum-free: any two of its
elements sum to more than `n`, hence leave `interval n ⊇ C`. -/
theorem isSumFree_filter_upper {n : ℕ} {C : Finset ℤ}
    (hC : C ⊆ interval n) :
    IsSumFree (C.filter fun x => 2 * x > (n : ℤ)) := by
  intro x hx y hy hxy
  obtain ⟨-, hxx⟩ := Finset.mem_filter.mp hx
  obtain ⟨-, hyy⟩ := Finset.mem_filter.mp hy
  obtain ⟨hxyC, -⟩ := Finset.mem_filter.mp hxy
  have hle := (Finset.mem_Icc.mp (hC hxyC)).2
  simp only [gt_iff_lt] at hxx hyy
  omega

/-- **Removal by a small low part.**  If at most `k` elements of `C` lie
at or below `n/2`, deleting them leaves the (sum-free) upper part. -/
theorem removal_of_small_low_part {n : ℕ} {C : Finset ℤ}
    (hC : C ⊆ interval n) {k : ℕ}
    (hk : (C.filter fun x => 2 * x ≤ (n : ℤ)).card ≤ k) :
    ∃ t : Finset ℤ, t ⊆ C ∧ IsSumFree t ∧ (C \ t).card ≤ k := by
  classical
  refine ⟨C.filter fun x => 2 * x > (n : ℤ), Finset.filter_subset _ _,
    isSumFree_filter_upper hC, ?_⟩
  have e : C \ (C.filter fun x => 2 * x > (n : ℤ))
      = C.filter fun x => 2 * x ≤ (n : ℤ) := by
    ext x
    constructor
    · intro hx
      obtain ⟨hxC, hx2⟩ := Finset.mem_sdiff.mp hx
      refine Finset.mem_filter.mpr ⟨hxC, ?_⟩
      by_contra hcon
      exact hx2 (Finset.mem_filter.mpr ⟨hxC, by omega⟩)
    · intro hx
      obtain ⟨hxC, hxle⟩ := Finset.mem_filter.mp hx
      refine Finset.mem_sdiff.mpr ⟨hxC, fun hf => ?_⟩
      have h2 := (Finset.mem_filter.mp hf).2
      omega
  rw [e]
  exact hk

/-! ## Band counting -/

/-- **Band lower bound.**  Let `L ⊆ C` lie in `(n/4, n/2]` and `U ⊆ C` in
`(n/2, n]`.  For each `b ∈ L` the injection `a ↦ a + b` sends `L` into
`(n/2, n]`, so at most `|(n/2,n] ∖ U|` elements `a ∈ L` have `a + b ∉ U`.
Hence `|L|² ≤ schurTripleCount C + |L|·|(n/2,n] ∖ U|`. -/
theorem schurTripleCount_ge_of_band {n : ℕ} {C L U : Finset ℤ}
    (hLC : L ⊆ C) (hUC : U ⊆ C)
    (hL : L ⊆ Finset.Icc ((n : ℤ) / 4 + 1) ((n : ℤ) / 2))
    (_hU : U ⊆ Finset.Icc ((n : ℤ) / 2 + 1) (n : ℤ)) :
    L.card * L.card
      ≤ schurTripleCount C
        + L.card * ((Finset.Icc ((n : ℤ) / 2 + 1) (n : ℤ)) \ U).card := by
  classical
  set B := Finset.Icc ((n : ℤ) / 2 + 1) (n : ℤ) \ U with hB
  -- Per `b ∈ L`: at most `|B|` bad first summands.
  have hgood : ∀ b ∈ L,
      L.card ≤ (L.filter fun a => a + b ∈ U).card + B.card := by
    intro b hb
    have hbnd : ∀ a ∈ L,
        a + b ∈ Finset.Icc ((n : ℤ) / 2 + 1) (n : ℤ) := by
      intro a ha
      obtain ⟨ha1, ha2⟩ := Finset.mem_Icc.mp (hL ha)
      obtain ⟨hb1, hb2⟩ := Finset.mem_Icc.mp (hL hb)
      rw [Finset.mem_Icc]
      omega
    have hbim : ((L.filter fun a => ¬ a + b ∈ U).image fun a => a + b)
        ⊆ B := by
      intro z hz
      obtain ⟨a, ha, haz⟩ := Finset.mem_image.mp hz
      obtain ⟨haL, haU⟩ := Finset.mem_filter.mp ha
      rw [hB, Finset.mem_sdiff]
      refine ⟨?_, ?_⟩
      · have hmem := hbnd a haL
        rwa [haz] at hmem
      · intro hzU
        exact haU (haz ▸ hzU)
    have hbadcard : (L.filter fun a => ¬ a + b ∈ U).card ≤ B.card := by
      calc (L.filter fun a => ¬ a + b ∈ U).card
          = ((L.filter fun a => ¬ a + b ∈ U).image
              fun a => a + b).card := by
            symm
            apply Finset.card_image_of_injOn
            intro a₁ _ a₂ _ h12
            change a₁ + b = a₂ + b at h12
            omega
        _ ≤ B.card := Finset.card_le_card hbim
    have hsplit := Finset.card_filter_add_card_filter_not (s := L)
      (p := fun a => a + b ∈ U)
    omega
  -- The good pairs `L × L` with sum in `U`.
  set D := (L ×ˢ L).filter fun p => p.1 + p.2 ∈ U with hD
  have hpairs : D.card
      = ∑ b ∈ L, (L.filter fun a => a + b ∈ U).card := by
    rw [hD, Finset.card_filter, Finset.sum_product_right]
    exact Finset.sum_congr rfl fun b _ =>
      (Finset.card_filter _ L).symm
  have hinj : D.card ≤ schurTripleCount C := by
    rw [hD]
    refine Finset.card_le_card_of_injOn
      (fun p : ℤ × ℤ => (p.1, p.2, p.1 + p.2)) ?_ ?_
    · intro p hp
      rw [Finset.mem_coe] at hp
      obtain ⟨hpL, hpU⟩ := Finset.mem_filter.mp hp
      rw [Finset.mem_product] at hpL
      rw [Finset.mem_coe, schurTriples, Finset.mem_filter,
        Finset.mem_product, Finset.mem_product]
      exact ⟨⟨hLC hpL.1, hLC hpL.2, hUC hpU⟩, rfl⟩
    · intro p _ q _ h
      simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2, -⟩ := h
      exact Prod.ext h1 h2
  have hsumle : L.card * L.card
      ≤ ∑ b ∈ L, (L.filter fun a => a + b ∈ U).card + L.card * B.card := by
    have h1 : ∑ b ∈ L, L.card
        ≤ ∑ b ∈ L, ((L.filter fun a => a + b ∈ U).card + B.card) :=
      Finset.sum_le_sum hgood
    rw [Finset.sum_add_distrib] at h1
    rw [Finset.sum_const, smul_eq_mul] at h1
    have h2 : ∑ _b ∈ L, B.card = L.card * B.card := by
      rw [Finset.sum_const, smul_eq_mul]
    rw [h2] at h1
    exact h1
  rw [← hpairs] at hsumle
  omega

/-- **Low-dense lower bound.**  Taking `U = C ∩ (n/2, n]` in
`schurTripleCount_ge_of_band`: a dense low band `L ⊆ C ∩ (n/4, n/2]`
produces `|L|² − |L|·|(n/2,n] ∖ C|` Schur triples. -/
theorem schurTripleCount_ge_of_low_dense {n : ℕ} {C L : Finset ℤ}
    (hLC : L ⊆ C)
    (hL : L ⊆ Finset.Icc ((n : ℤ) / 4 + 1) ((n : ℤ) / 2)) :
    L.card * L.card
      ≤ schurTripleCount C
        + L.card
          * ((Finset.Icc ((n : ℤ) / 2 + 1) (n : ℤ)) \ C).card := by
  have e : Finset.Icc ((n : ℤ) / 2 + 1) (n : ℤ)
        \ (C ∩ Finset.Icc ((n : ℤ) / 2 + 1) (n : ℤ))
      = Finset.Icc ((n : ℤ) / 2 + 1) (n : ℤ) \ C := by
    ext z
    simp only [Finset.mem_sdiff, Finset.mem_inter, not_and]
    constructor
    · rintro ⟨hz, h⟩
      exact ⟨hz, fun hc => h hc hz⟩
    · rintro ⟨hz, h⟩
      exact ⟨hz, fun hc _ => h hc⟩
  have h := schurTripleCount_ge_of_band hLC Finset.inter_subset_left hL
    Finset.inter_subset_right
  rw [e] at h
  exact h

end JSP000728
