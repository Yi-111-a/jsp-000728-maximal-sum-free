import JSPProblem.Basic
import JSPProblem.Odds
import JSPProblem.MaxCard
import JSPProblem.Containers
import JSPProblem.OddBound
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# JSP-000728 — parity stability: sparse containers housing a large odd set

A *removal-lemma-free* amplification argument for the odd-type case of the
BLST trichotomy.  If a container `C ⊆ {1,…,n}` contains a large all-odd set
`M₀` (e.g. a maximal sum-free `M₀ ⊆ odds n` with `|M₀| > 2n/5`), then every
even `e ∈ C` participates in many Schur triples inside `C`:

* `DR e = {y ∈ M₀ : y + e ∈ M₀}` — difference representations `e + y = z`;
* `SR e = {x ∈ M₀ : e - x ∈ M₀}` — sum representations `x + (e - x) = e`.

Both `DR e` and `SR e` are intersections of two large subsets of the odd
slots of an interval, so a pigeonhole on the `≈ ℓ/2` odd integers in an
interval of length `ℓ` gives

    |DR e| ≥ 2·|M₀| − e − (n − e)/2 − O(1),
    |SR e| ≥ 2·|M₀| − (n − e) − e/2 − O(1),

and the `e`-dependence cancels:

    |DR e| + |SR e| ≥ 4·|M₀| − 3n/2 − O(1) ≥ n/10 − O(1).

Each representation produces a distinct Schur triple of `C` (difference
triples `(e, y, e+y)` start with an even number, sum triples `(x, e−x, e)`
with an odd one, so the two families are disjoint), hence

    |C ∖ odds n| · (n/10 − 4) ≤ schurTripleCount C.

Consequently `|C ∖ odds n| ≤ 10·schurTripleCount(C)/n + 40`, which is `o(n)`
for `δn²`-sparse `C` — the conclusion `|C ∖ odds n| ≤ εn` of the odd-type
case of `container_trichotomy`, obtained here **without** the Schur removal
lemma.

## Contents

* `card_oddIcc_le` — an interval `[a,b]` contains at most `(b−a)/2 + 1` odd
  integers (real-valued bound).
* `even_card_le_of_large_odd_subset` — the amplification lemma above.
* `even_card_mul_le_of_large_odd` — the multiplied-out form
  `|C ∖ odds n| · n ≤ 10·schurTripleCount C + 40n`.
* `even_card_le_of_exists_large_odd_maximal` — the same bound under the
  hypothesis `M₀ ∈ maxSumFreeSets n`.
* `maxSumFreeSets_filter_card_le_of_large_odd` — the assembled odd-case
  counting bound: a `δn²`-sparse `C` housing a large odd maximal sum-free
  set contains at most `2^{(1/4+ε)n}` maximal sum-free sets (reuses
  `card_maxSumFreeSets_filter_union_le_two_pow_mul` and the proved
  `oddContainerBound`).
-/

namespace JSP000728

/-- The odd integers in the integer interval `[a, b]`. -/
private def oddIcc (a b : ℤ) : Finset ℤ :=
  (Finset.Icc a b).filter fun x => x % 2 = 1

private theorem mem_oddIcc {a b x : ℤ} :
    x ∈ oddIcc a b ↔ a ≤ x ∧ x ≤ b ∧ x % 2 = 1 := by
  rw [oddIcc, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨h, h2⟩; exact ⟨h.1, h.2, h2⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, h3⟩

/-- An interval `[a, b]` (with `a ≤ b`) contains at most `(b − a)/2 + 1` odd
integers: `x ↦ (x + 1)/2` injects them into `Icc ((a+2)/2) ((b+1)/2)`. -/
private theorem card_oddIcc_le {a b : ℤ} (hab : a ≤ b) :
    ((oddIcc a b).card : ℝ) ≤ ((b - a : ℤ) : ℝ) / 2 + 1 := by
  classical
  have hinj : Set.InjOn (fun x : ℤ => (x + 1) / 2) (↑(oddIcc a b) : Set ℤ) := by
    intro x hx y hy hxy
    rw [Finset.mem_coe, mem_oddIcc] at hx hy
    omega
  have himg : (oddIcc a b).image (fun x : ℤ => (x + 1) / 2) ⊆
      Finset.Icc ((a + 2) / 2) ((b + 1) / 2) := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hax, hxb, hodd⟩ := mem_oddIcc.mp hx
    rw [Finset.mem_Icc]
    constructor <;> omega
  have hcard : (oddIcc a b).card ≤ ((b + 1) / 2 - (a + 2) / 2 + 1).toNat := by
    calc (oddIcc a b).card
        = ((oddIcc a b).image fun x : ℤ => (x + 1) / 2).card :=
          (Finset.card_image_of_injOn hinj).symm
      _ ≤ (Finset.Icc ((a + 2) / 2) ((b + 1) / 2)).card :=
          Finset.card_le_card himg
      _ = ((b + 1) / 2 - (a + 2) / 2 + 1).toNat := by
          rw [Int.card_Icc]
          congr 1
          ring
  -- turn the `toNat` bound into the real bound `(b - a)/2 + 1`
  have hz : (b + 1) / 2 - (a + 2) / 2 + 1 ≤ (b - a) / 2 + 1 := by omega
  have hw : (0 : ℤ) ≤ (b - a) / 2 + 1 := by omega
  have hcard2 : (oddIcc a b).card ≤ ((b - a) / 2 + 1).toNat :=
    hcard.trans (Int.toNat_le_toNat hz)
  have hcast : ((oddIcc a b).card : ℝ) ≤ (((b - a) / 2 + 1 : ℤ) : ℝ) := by
    have h1 : ((oddIcc a b).card : ℝ) ≤ ((((b - a) / 2 + 1).toNat : ℕ) : ℝ) := by
      exact_mod_cast hcard2
    have h2 : ((((b - a) / 2 + 1).toNat : ℕ) : ℝ) = (((b - a) / 2 + 1 : ℤ) : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg hw
    rwa [h2] at h1
  refine hcast.trans ?_
  push_cast
  have h4 : (2 : ℤ) * ((b - a) / 2) ≤ b - a := by omega
  have h5 : (2 : ℝ) * (((b - a) / 2 : ℤ) : ℝ) ≤ (b - a : ℝ) := by
    exact_mod_cast h4
  linarith

/-- **Amplification.**  If `C ⊆ {1,…,n}` contains a large all-odd set `M₀`
(`|M₀| > 2n/5`), then every even element `e` of `C` has
`|DR e| + |SR e| ≥ n/10 − O(1)` representations as `e + y = z` or
`x + (e − x) = e` with odd partners in `M₀ ⊆ C`; these are pairwise distinct
Schur triples of `C`, so `|C ∖ odds n| · (n/10 − 4) ≤ schurTripleCount C`. -/
theorem even_card_le_of_large_odd_subset {n : ℕ} {C M₀ : Finset ℤ}
    (hCI : C ⊆ interval n) (hMC : M₀ ⊆ C) (hModd : M₀ ⊆ odds n)
    (hMbig : (2 / 5 : ℝ) * (n : ℝ) < (M₀.card : ℝ)) :
    ((C \ odds n).card : ℝ) * ((n : ℝ) / 10 - 4) ≤
      (schurTripleCount C : ℝ) := by
  classical
  set E : Finset ℤ := C \ odds n with hE
  have hE_mem : ∀ e ∈ E, 1 ≤ e ∧ e ≤ (n : ℤ) ∧ e % 2 = 0 := by
    intro e he
    rw [hE, Finset.mem_sdiff] at he
    obtain ⟨heC, heno⟩ := he
    have heI := Finset.mem_Icc.mp (hCI heC)
    have hmod : e % 2 = 0 := by
      rcases Int.emod_two_eq_zero_or_one e with h | h
      · exact h
      · exact absurd (mem_odds.mpr ⟨Finset.mem_Icc.mpr heI, h⟩) heno
    exact ⟨heI.1, heI.2, hmod⟩
  have hMmem : ∀ x ∈ M₀, 1 ≤ x ∧ x ≤ (n : ℤ) ∧ x % 2 = 1 := by
    intro x hx
    obtain ⟨hxI, hodd⟩ := mem_odds.mp (hModd hx)
    obtain ⟨h1, hn⟩ := Finset.mem_Icc.mp hxI
    exact ⟨h1, hn, hodd⟩
  set DR : ℤ → Finset ℤ := fun e => M₀.filter fun y => y + e ∈ M₀ with hDR
  set SR : ℤ → Finset ℤ := fun e => M₀.filter fun x => e - x ∈ M₀ with hSR
  -- The per-element representation bound.
  have hrep : ∀ e ∈ E,
      (n : ℝ) / 10 - 4 ≤ ((DR e).card : ℝ) + ((SR e).card : ℝ) := by
    intro e he
    obtain ⟨he1, hen, hep⟩ := hE_mem e he
    -- `M₀` split at `n − e`, at `e` and at `e − 1`.
    have hsplit1 : M₀ ⊆ (M₀ ∩ Finset.Icc 1 ((n : ℤ) - e)) ∪
        oddIcc ((n : ℤ) - e + 1) (n : ℤ) := by
      intro x hx
      obtain ⟨hx1, hxn, hodd⟩ := hMmem x hx
      rw [Finset.mem_union]
      rcases le_or_gt x ((n : ℤ) - e) with h | h
      · exact Or.inl (Finset.mem_inter.mpr ⟨hx, Finset.mem_Icc.mpr ⟨hx1, h⟩⟩)
      · exact Or.inr (mem_oddIcc.mpr ⟨by omega, hxn, hodd⟩)
    have hcard1 : M₀.card ≤ (M₀ ∩ Finset.Icc 1 ((n : ℤ) - e)).card +
        (oddIcc ((n : ℤ) - e + 1) (n : ℤ)).card :=
      (Finset.card_le_card hsplit1).trans (Finset.card_union_le _ _)
    have hsplit2 : M₀ ⊆ (M₀ ∩ Finset.Icc (e + 1) (n : ℤ)) ∪ oddIcc 1 e := by
      intro x hx
      obtain ⟨hx1, hxn, hodd⟩ := hMmem x hx
      rw [Finset.mem_union]
      rcases le_or_gt x e with h | h
      · exact Or.inr (mem_oddIcc.mpr ⟨hx1, h, hodd⟩)
      · exact Or.inl (Finset.mem_inter.mpr ⟨hx, Finset.mem_Icc.mpr ⟨by omega, hxn⟩⟩)
    have hcard2 : M₀.card ≤ (M₀ ∩ Finset.Icc (e + 1) (n : ℤ)).card +
        (oddIcc 1 e).card :=
      (Finset.card_le_card hsplit2).trans (Finset.card_union_le _ _)
    have hsplit3 : M₀ ⊆ (M₀ ∩ Finset.Icc 1 (e - 1)) ∪ oddIcc e (n : ℤ) := by
      intro x hx
      obtain ⟨hx1, hxn, hodd⟩ := hMmem x hx
      rw [Finset.mem_union]
      rcases le_or_gt x (e - 1) with h | h
      · exact Or.inl (Finset.mem_inter.mpr ⟨hx, Finset.mem_Icc.mpr ⟨hx1, h⟩⟩)
      · exact Or.inr (mem_oddIcc.mpr ⟨by omega, hxn, hodd⟩)
    have hcard3 : M₀.card ≤ (M₀ ∩ Finset.Icc 1 (e - 1)).card +
        (oddIcc e (n : ℤ)).card :=
      (Finset.card_le_card hsplit3).trans (Finset.card_union_le _ _)
    -- `|DR e| ≥ |M₀ ∩ [1, n−e]| + |M₀ ∩ [e+1, n]| − |oddIcc 1 (n−e)|`.
    set L : Finset ℤ := M₀ ∩ Finset.Icc 1 ((n : ℤ) - e) with hLdef
    set U' : Finset ℤ := (M₀ ∩ Finset.Icc (e + 1) (n : ℤ)).image (· - e) with hUdef
    have hUcard : U'.card = (M₀ ∩ Finset.Icc (e + 1) (n : ℤ)).card :=
      Finset.card_image_of_injective _ (fun a b h => by omega)
    have hLUsub : L ∪ U' ⊆ oddIcc 1 ((n : ℤ) - e) := by
      intro y hy
      rcases Finset.mem_union.mp hy with hy | hy
      · obtain ⟨hyM, hyI⟩ := Finset.mem_inter.mp hy
        obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hyI
        exact mem_oddIcc.mpr ⟨h1, h2, (hMmem y hyM).2.2⟩
      · obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
        obtain ⟨hzM, hzI⟩ := Finset.mem_inter.mp hz
        obtain ⟨hz1, hz2⟩ := Finset.mem_Icc.mp hzI
        refine mem_oddIcc.mpr ⟨by omega, by omega, ?_⟩
        have hodd := (hMmem z hzM).2.2
        omega
    have hLUin : L ∩ U' ⊆ DR e := by
      intro y hy
      obtain ⟨hyL, hyU⟩ := Finset.mem_inter.mp hy
      obtain ⟨z, hz, hzeq⟩ := Finset.mem_image.mp hyU
      obtain ⟨hzM, -⟩ := Finset.mem_inter.mp hz
      rw [hDR, Finset.mem_filter]
      refine ⟨(Finset.mem_inter.mp hyL).1, ?_⟩
      have hze : y + e = z := by omega
      rw [hze]
      exact hzM
    have hUunion : (L ∪ U').card ≤ (oddIcc 1 ((n : ℤ) - e)).card :=
      Finset.card_le_card hLUsub
    have hinter : (L ∩ U').card ≤ (DR e).card := Finset.card_le_card hLUin
    have hUUI := Finset.card_union_add_card_inter L U'
    rw [hUcard] at hUUI
    have hDRnat : (DR e).card + (oddIcc 1 ((n : ℤ) - e)).card ≥
        L.card + (M₀ ∩ Finset.Icc (e + 1) (n : ℤ)).card := by omega
    -- `|SR e| ≥ 2·|M₀ ∩ [1, e−1]| − |oddIcc 1 (e−1)|`.
    set L1 : Finset ℤ := M₀ ∩ Finset.Icc 1 (e - 1) with hL1def
    set S' : Finset ℤ := L1.image (e - ·) with hSdef
    have hScard : S'.card = L1.card :=
      Finset.card_image_of_injective _ (fun a b h => by omega)
    have hLSsub : L1 ∪ S' ⊆ oddIcc 1 (e - 1) := by
      intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · obtain ⟨hxM, hxI⟩ := Finset.mem_inter.mp hx
        obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hxI
        exact mem_oddIcc.mpr ⟨h1, h2, (hMmem x hxM).2.2⟩
      · obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
        obtain ⟨hzM, hzI⟩ := Finset.mem_inter.mp hz
        obtain ⟨hz1, hz2⟩ := Finset.mem_Icc.mp hzI
        refine mem_oddIcc.mpr ⟨by omega, by omega, ?_⟩
        have hodd := (hMmem z hzM).2.2
        omega
    have hLSin : L1 ∩ S' ⊆ SR e := by
      intro x hx
      obtain ⟨hxL, hxS⟩ := Finset.mem_inter.mp hx
      obtain ⟨z, hz, hzeq⟩ := Finset.mem_image.mp hxS
      obtain ⟨hzM, -⟩ := Finset.mem_inter.mp hz
      rw [hSR, Finset.mem_filter]
      refine ⟨(Finset.mem_inter.mp hxL).1, ?_⟩
      have hze : e - x = z := by omega
      rw [hze]
      exact hzM
    have hLSunion : (L1 ∪ S').card ≤ (oddIcc 1 (e - 1)).card :=
      Finset.card_le_card hLSsub
    have hinter2 : (L1 ∩ S').card ≤ (SR e).card := Finset.card_le_card hLSin
    have hLSI := Finset.card_union_add_card_inter L1 S'
    rw [hScard] at hLSI
    have hSRnat : (SR e).card + (oddIcc 1 (e - 1)).card ≥ 2 * L1.card := by omega
    -- real-valued bounds on the odd-slot counts
    have ho1 : ((oddIcc ((n : ℤ) - e + 1) (n : ℤ)).card : ℝ) ≤
        ((e : ℝ) - 1) / 2 + 1 := by
      have h := card_oddIcc_le (a := (n : ℤ) - e + 1) (b := (n : ℤ)) (by omega)
      have heq : (((n : ℤ) - ((n : ℤ) - e + 1) : ℤ) : ℝ) = (e : ℝ) - 1 := by
        push_cast; ring
      rwa [heq] at h
    have ho2 : ((oddIcc 1 e).card : ℝ) ≤ ((e : ℝ) - 1) / 2 + 1 := by
      have h := card_oddIcc_le (a := (1 : ℤ)) (b := e) (by omega)
      have heq : (((e - 1 : ℤ)) : ℝ) = (e : ℝ) - 1 := by push_cast; ring
      rwa [heq] at h
    have ho3 : ((oddIcc 1 ((n : ℤ) - e)).card : ℝ) ≤
        (((n : ℤ) - e - 1 : ℤ) : ℝ) / 2 + 1 := by
      rcases le_or_gt 1 ((n : ℤ) - e) with hle | hgt
      · exact card_oddIcc_le (a := (1 : ℤ)) (b := (n : ℤ) - e) hle
      · have hempty : oddIcc 1 ((n : ℤ) - e) = ∅ := by
          have h : Finset.Icc (1 : ℤ) ((n : ℤ) - e) = ∅ :=
            Finset.Icc_eq_empty_iff.mpr (by omega)
          rw [oddIcc, h, Finset.filter_empty]
        rw [hempty, Finset.card_empty]
        have hi : (0 : ℤ) ≤ (n : ℤ) - e := by omega
        have hr : (0 : ℝ) ≤ ((n : ℤ) - e : ℝ) := by exact_mod_cast hi
        push_cast
        linarith
    have ho4 : ((oddIcc e (n : ℤ)).card : ℝ) ≤
        (((n : ℤ) - e : ℤ) : ℝ) / 2 + 1 :=
      card_oddIcc_le (a := e) (b := (n : ℤ)) (by omega)
    have ho5 : ((oddIcc 1 (e - 1)).card : ℝ) ≤ (e : ℝ) / 2 := by
      have h := card_oddIcc_le (a := (1 : ℤ)) (b := e - 1) (by omega)
      have heq : (((e - 1 - 1 : ℤ)) : ℝ) / 2 + 1 = (e : ℝ) / 2 := by
        push_cast; ring
      rwa [heq] at h
    -- cast the nat inequalities
    have hLr : ((M₀ ∩ Finset.Icc 1 ((n : ℤ) - e)).card : ℝ) ≥
        (M₀.card : ℝ) - (((e : ℝ) - 1) / 2 + 1) := by
      have h' : (M₀.card : ℝ) ≤
          ((M₀ ∩ Finset.Icc 1 ((n : ℤ) - e)).card : ℝ) +
            ((oddIcc ((n : ℤ) - e + 1) (n : ℤ)).card : ℝ) := by
        exact_mod_cast hcard1
      linarith
    have hUr : ((M₀ ∩ Finset.Icc (e + 1) (n : ℤ)).card : ℝ) ≥
        (M₀.card : ℝ) - (((e : ℝ) - 1) / 2 + 1) := by
      have h' : (M₀.card : ℝ) ≤
          ((M₀ ∩ Finset.Icc (e + 1) (n : ℤ)).card : ℝ) +
            ((oddIcc 1 e).card : ℝ) := by
        exact_mod_cast hcard2
      linarith
    have hL1r : ((M₀ ∩ Finset.Icc 1 (e - 1)).card : ℝ) ≥
        (M₀.card : ℝ) - ((((n : ℤ) - e : ℤ) : ℝ) / 2 + 1) := by
      have h' : (M₀.card : ℝ) ≤
          ((M₀ ∩ Finset.Icc 1 (e - 1)).card : ℝ) +
            ((oddIcc e (n : ℤ)).card : ℝ) := by
        exact_mod_cast hcard3
      linarith
    have hDRr : ((DR e).card : ℝ) + ((oddIcc 1 ((n : ℤ) - e)).card : ℝ) ≥
        ((M₀ ∩ Finset.Icc 1 ((n : ℤ) - e)).card : ℝ) +
          ((M₀ ∩ Finset.Icc (e + 1) (n : ℤ)).card : ℝ) := by
      exact_mod_cast hDRnat
    have hSRr : ((SR e).card : ℝ) + ((oddIcc 1 (e - 1)).card : ℝ) ≥
        2 * ((M₀ ∩ Finset.Icc 1 (e - 1)).card : ℝ) := by
      exact_mod_cast hSRnat
    -- `|DR| + |SR| ≥ 4|M₀| − 3n/2 − 7/2 ≥ n/10 − 4`.
    have hMge : (M₀.card : ℝ) ≥ (2 / 5 : ℝ) * (n : ℝ) := le_of_lt hMbig
    have hne : ((n : ℝ)) = (((n : ℤ)) : ℝ) := by norm_cast
    linarith
  -- Sum over `E`: at least `|E| · (n/10 − 4)` Schur triples.
  have hsumr : (E.card : ℝ) * ((n : ℝ) / 10 - 4) ≤
      ∑ e ∈ E, (((DR e).card : ℝ) + ((SR e).card : ℝ)) := by
    have h := Finset.sum_le_sum (fun e he => hrep e he)
    rwa [Finset.sum_const, nsmul_eq_mul] at h
  -- The two families of Schur triples in `C`.
  have hnat : (∑ e ∈ E, ((DR e).card + (SR e).card)) ≤ schurTripleCount C := by
    have hinj1 : Function.Injective (fun p : ℤ × ℤ => (p.1, p.2, p.1 + p.2)) := by
      intro p q h
      have h1 : p.1 = q.1 := congrArg Prod.fst h
      have h2 : p.2 = q.2 := congrArg (fun t => t.2.1) h
      exact Prod.ext_iff.mpr ⟨h1, h2⟩
    have hinj2 : Function.Injective
        (fun p : ℤ × ℤ => (p.2, p.1 - p.2, p.1)) := by
      intro p q h
      have h2 : p.2 = q.2 := congrArg Prod.fst h
      have h1 : p.1 = q.1 := congrArg (fun t => t.2.2) h
      exact Prod.ext_iff.mpr ⟨h1, h2⟩
    have himg1 : (E.sigma fun e => DR e).image (fun p : ℤ × ℤ =>
        (p.1, p.2, p.1 + p.2)) ⊆ schurTriples C := by
      intro t ht
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ht
      obtain ⟨he, hy⟩ := Finset.mem_sigma.mp hp
      rw [hDR, Finset.mem_filter] at hy
      obtain ⟨heC, -⟩ := Finset.mem_sdiff.mp (hE ▸ he)
      rw [schurTriples, Finset.mem_filter]
      simp only [Finset.mem_product]
      exact ⟨⟨heC, hMC hy.1, hMC hy.2⟩, rfl⟩
    have himg2 : (E.sigma fun e => SR e).image (fun p : ℤ × ℤ =>
        (p.2, p.1 - p.2, p.1)) ⊆ schurTriples C := by
      intro t ht
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ht
      obtain ⟨he, hx⟩ := Finset.mem_sigma.mp hp
      rw [hSR, Finset.mem_filter] at hx
      obtain ⟨heC, -⟩ := Finset.mem_sdiff.mp (hE ▸ he)
      rw [schurTriples, Finset.mem_filter]
      simp only [Finset.mem_product]
      exact ⟨⟨hMC hx.1, hMC hx.2, heC⟩, by ring⟩
    have hdisj : Disjoint
        ((E.sigma fun e => DR e).image (fun p : ℤ × ℤ => (p.1, p.2, p.1 + p.2)))
        ((E.sigma fun e => SR e).image
          (fun p : ℤ × ℤ => (p.2, p.1 - p.2, p.1))) := by
      rw [Finset.disjoint_left]
      intro t ht1 ht2
      obtain ⟨p1, hp1, rfl⟩ := Finset.mem_image.mp ht1
      obtain ⟨p2, hp2, htp2⟩ := Finset.mem_image.mp ht2
      obtain ⟨he1, hy1⟩ := Finset.mem_sigma.mp hp1
      obtain ⟨he2, hx2⟩ := Finset.mem_sigma.mp hp2
      rw [hSR, Finset.mem_filter] at hx2
      have h1 : p1.1 % 2 = 0 := (hE_mem p1.1 he1).2.2
      have h2 : p2.2 % 2 = 1 := (hMmem p2.2 hx2.1).2.2
      have h3 : p2.2 = p1.1 := congrArg Prod.fst htp2
      omega
    have hcard1 : ((E.sigma fun e => DR e).image
        (fun p : ℤ × ℤ => (p.1, p.2, p.1 + p.2))).card =
        ∑ e ∈ E, (DR e).card := by
      rw [Finset.card_image_of_injective _ hinj1, Finset.card_sigma]
    have hcard2 : ((E.sigma fun e => SR e).image
        (fun p : ℤ × ℤ => (p.2, p.1 - p.2, p.1))).card =
        ∑ e ∈ E, (SR e).card := by
      rw [Finset.card_image_of_injective _ hinj2, Finset.card_sigma]
    calc (∑ e ∈ E, ((DR e).card + (SR e).card))
        = (∑ e ∈ E, (DR e).card) + (∑ e ∈ E, (SR e).card) :=
          Finset.sum_add_distrib
      _ = ((E.sigma fun e => DR e).image
            (fun p : ℤ × ℤ => (p.1, p.2, p.1 + p.2))).card +
          ((E.sigma fun e => SR e).image
            (fun p : ℤ × ℤ => (p.2, p.1 - p.2, p.1))).card := by
          rw [hcard1, hcard2]
      _ = (((E.sigma fun e => DR e).image
              (fun p : ℤ × ℤ => (p.1, p.2, p.1 + p.2))) ∪
            ((E.sigma fun e => SR e).image
              (fun p : ℤ × ℤ => (p.2, p.1 - p.2, p.1)))).card :=
          (Finset.card_union_of_disjoint hdisj).symm
      _ ≤ (schurTriples C).card :=
          Finset.card_le_card (Finset.union_subset himg1 himg2)
      _ = schurTripleCount C := rfl
  have hstc : (∑ e ∈ E, (((DR e).card : ℝ) + ((SR e).card : ℝ))) ≤
      (schurTripleCount C : ℝ) := by
    have h' : ((∑ e ∈ E, ((DR e).card + (SR e).card) : ℕ) : ℝ) ≤
        (schurTripleCount C : ℝ) := by
      exact_mod_cast hnat
    push_cast at h'
    exact h'
  exact hsumr.trans hstc

/-- Multiplied-out form: `|C ∖ odds n| · n ≤ 10·schurTripleCount C + 40n`.
In particular `|C ∖ odds n| ≤ 10·δ·n + 40` whenever `C` is `δn²`-sparse. -/
theorem even_card_mul_le_of_large_odd {n : ℕ} {C M₀ : Finset ℤ}
    (hCI : C ⊆ interval n) (hMC : M₀ ⊆ C) (hModd : M₀ ⊆ odds n)
    (hMbig : (2 / 5 : ℝ) * (n : ℝ) < (M₀.card : ℝ)) :
    ((C \ odds n).card : ℝ) * (n : ℝ) ≤
      10 * (schurTripleCount C : ℝ) + 40 * (n : ℝ) := by
  have h := even_card_le_of_large_odd_subset hCI hMC hModd hMbig
  have hEle : ((C \ odds n).card : ℝ) ≤ (n : ℝ) := by
    have hsub : (C \ odds n).card ≤ (interval n).card :=
      Finset.card_le_card (Finset.sdiff_subset.trans hCI)
    rw [interval, Int.card_Icc] at hsub
    have hnn : ((n : ℤ) + 1 - 1).toNat = n := by simp
    rw [hnn] at hsub
    exact_mod_cast hsub
  linarith

/-- **The core lemma, maximal-set form.**  If a sparse container `C` houses a
large all-odd *maximal* sum-free set `M₀`, then `C` has few even elements:
`|C ∖ odds n| · (n/10 − 4) ≤ schurTripleCount C`.  (Maximality is not needed
by the proof — only `M₀ ⊆ odds n`, `M₀ ⊆ C` and `|M₀| > 2n/5`.) -/
theorem even_card_le_of_exists_large_odd_maximal {n : ℕ} {C M₀ : Finset ℤ}
    (hCI : C ⊆ interval n) (hM : M₀ ∈ maxSumFreeSets n) (hMC : M₀ ⊆ C)
    (hModd : M₀ ⊆ odds n) (hMbig : (2 / 5 : ℝ) * (n : ℝ) < (M₀.card : ℝ)) :
    ((C \ odds n).card : ℝ) * ((n : ℝ) / 10 - 4) ≤
      (schurTripleCount C : ℝ) :=
  even_card_le_of_large_odd_subset hCI hMC hModd hMbig

/-- Multiplied-out maximal-set form:
`|C ∖ odds n| · n ≤ 10·schurTripleCount C + 40n`. -/
theorem even_card_mul_le_of_exists_large_odd_maximal {n : ℕ}
    {C M₀ : Finset ℤ}
    (hCI : C ⊆ interval n) (hM : M₀ ∈ maxSumFreeSets n) (hMC : M₀ ⊆ C)
    (hModd : M₀ ⊆ odds n) (hMbig : (2 / 5 : ℝ) * (n : ℝ) < (M₀.card : ℝ)) :
    ((C \ odds n).card : ℝ) * (n : ℝ) ≤
      10 * (schurTripleCount C : ℝ) + 40 * (n : ℝ) :=
  even_card_mul_le_of_large_odd hCI hMC hModd hMbig

/-- **Assembled odd-case counting bound** (removal-free).  For every `ε > 0`
there is `δ > 0` such that eventually every `δn²`-sparse `C ⊆ {1,…,n}` that
houses a large all-odd maximal sum-free set `M₀ ⊆ odds n` (`|M₀| > 2n/5`)
contains at most `2^{(1/4+ε)n}` maximal sum-free sets of `{1,…,n}`.

The proof is the odd-type branch of `sparseFingerprintBound_of_removal_dfst_odd`
with the removal/DFST-derived bound `|C ∖ odds n| ≤ ε₁n` replaced by the
amplification bound `even_card_mul_le_of_large_odd`: the fingerprint
`M ∩ (C ∖ odds n)` is a sum-free set of *even* numbers, so the proved
`oddContainerBound` controls the link-MIS count, while the `2^{|C∖odds|}`
fingerprint count is `≤ 2^{εn/2}`. -/
theorem maxSumFreeSets_filter_card_le_of_large_odd {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n : ℕ in Filter.atTop,
      ∀ C M₀ : Finset ℤ, C ⊆ interval n → M₀ ∈ maxSumFreeSets n →
        M₀ ⊆ C → M₀ ⊆ odds n → (2 / 5 : ℝ) * (n : ℝ) < (M₀.card : ℝ) →
        (schurTripleCount C : ℝ) ≤ δ * (n : ℝ) ^ 2 →
        (((maxSumFreeSets n).filter (· ⊆ C)).card : ℝ) ≤
          (2 : ℝ) ^ ((1 / 4 + ε) * (n : ℝ)) := by
  have hε2 : 0 < ε / 2 := by linarith
  have hOCB := oddContainerBound (ε / 2) hε2
  refine ⟨ε / 40, by linarith, ?_⟩
  filter_upwards [hOCB, Filter.eventually_ge_atTop ⌈160 / ε⌉₊,
    Filter.eventually_ge_atTop 1] with n hOCBn hn160 hn1
  intro C M₀ hCI hM hMC hModd hMbig hsp
  have hnn : (0 : ℝ) < (n : ℝ) := by
    have : (1 : ℕ) ≤ n := hn1
    exact_mod_cast this
  have hnn' : (0 : ℝ) ≤ (n : ℝ) := hnn.le
  -- `|C ∖ odds n| ≤ 10δn + 40 ≤ εn/2`.
  have hkey := even_card_mul_le_of_exists_large_odd_maximal
    hCI hM hMC hModd hMbig
  have h160 : (160 : ℝ) / ε ≤ (n : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hn160)
  have hεn : 160 ≤ ε * (n : ℝ) := by
    rw [div_le_iff₀ hε] at h160
    linarith [h160]
  have hEε : ((C \ odds n).card : ℝ) ≤ (ε / 2) * (n : ℝ) := by
    have hsp' : (schurTripleCount C : ℝ) ≤ (ε / 40) * (n : ℝ) ^ 2 := hsp
    have h1 : ((C \ odds n).card : ℝ) * (n : ℝ) ≤
        10 * (ε / 40) * (n : ℝ) ^ 2 + 40 * (n : ℝ) := by linarith [hkey]
    have h2 : ((C \ odds n).card : ℝ) ≤
        10 * (ε / 40) * (n : ℝ) + 40 := by
      have h3 : (10 * (ε / 40) * (n : ℝ) ^ 2 + 40 * (n : ℝ)) =
          (10 * (ε / 40) * (n : ℝ) + 40) * (n : ℝ) := by ring
      rw [h3] at h1
      exact le_of_mul_le_mul_right h1 hnn
    linarith [h2, hεn]
  -- housed maximal sets via the fingerprint decomposition `odds ∪ (C∖odds)`
  have hcover : C ⊆ odds n ∪ (C \ odds n) := by
    intro x hx
    rw [Finset.mem_union]
    by_cases hxo : x ∈ odds n
    · exact Or.inl hxo
    · exact Or.inr (Finset.mem_sdiff.mpr ⟨hx, hxo⟩)
  have hmono : ((maxSumFreeSets n).filter (· ⊆ C)).card ≤
      ((maxSumFreeSets n).filter (· ⊆ odds n ∪ (C \ odds n))).card := by
    apply Finset.card_le_card
    intro M hM'
    rw [Finset.mem_filter] at hM' ⊢
    exact ⟨hM'.1, hM'.2.trans hcover⟩
  have hb : ∀ S : Finset ℤ, S ⊆ C \ odds n → IsSumFree S →
      ((linkMaxSets S (odds n)).card : ℝ) ≤
        (2 : ℝ) ^ ((1 / 4 + ε / 2) * (n : ℝ)) := by
    intro S hS hSsf
    refine hOCBn S (hS.trans (Finset.sdiff_subset.trans hCI)) hSsf ?_
    intro x hx
    obtain ⟨hxC, hxno⟩ := Finset.mem_sdiff.mp (hS hx)
    have hxI := Finset.mem_Icc.mp (hCI hxC)
    by_contra hne
    exact hxno (mem_odds.mpr ⟨Finset.mem_Icc.mpr hxI, by omega⟩)
  have hbound := card_maxSumFreeSets_filter_union_le_two_pow_mul
    (A := odds n) (B := C \ odds n) (odds_subset_interval n)
    (isSumFree_odds n)
    (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _).le hb
  have hcardB : (2 : ℝ) ^ ((C \ odds n).card : ℝ) ≤
      (2 : ℝ) ^ ((ε / 2) * (n : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hEε
  calc (((maxSumFreeSets n).filter (· ⊆ C)).card : ℝ)
      ≤ (((maxSumFreeSets n).filter
          (· ⊆ odds n ∪ (C \ odds n))).card : ℝ) := by
        exact_mod_cast hmono
    _ ≤ (2 : ℝ) ^ ((C \ odds n).card : ℝ) *
          (2 : ℝ) ^ ((1 / 4 + ε / 2) * (n : ℝ)) := hbound
    _ ≤ (2 : ℝ) ^ ((ε / 2) * (n : ℝ)) *
          (2 : ℝ) ^ ((1 / 4 + ε / 2) * (n : ℝ)) := by
        exact mul_le_mul_of_nonneg_right hcardB
          (Real.rpow_nonneg (by norm_num) _)
    _ = (2 : ℝ) ^ ((ε / 2) * (n : ℝ) + (1 / 4 + ε / 2) * (n : ℝ)) := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    _ = (2 : ℝ) ^ ((1 / 4 + ε) * (n : ℝ)) := by
        congr 1
        ring

end JSP000728
