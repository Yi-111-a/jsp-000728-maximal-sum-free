import JSPProblem.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Int.Interval
import Mathlib.Data.Nat.Fib.Basic

/-!
# JSP-000728 — no-consecutive subsets and shift-free factorisation

Combinatorial machinery for the Fibonacci path bound.

* `noConsec t` : `t : Finset ℕ` has no two consecutive elements; `ncSets L` is
  the family of such subsets of `Finset.range L`, counted by `Nat.fib (L+2)`
  (`ncSets_card`).
* `shiftFree m s` : `x ∈ s → x + m ∉ s`, the translate constraint coming from
  sum-freeness (`x, m ∈ M` forces `x + m ∉ M`).  Shift-free subsets of a union
  restrict to shift-free subsets of the parts, giving the product bound
  `card_powerset_filter_shiftFree_le_prod`.
* `prog m a L` is the progression `a, a+m, …, a+m(L-1)`; its shift-free subsets
  are counted by `Nat.fib (L+2)` (`card_powerset_filter_shiftFree_prog`) via the
  order-isomorphism `k ↦ a + m·k` with `range L`.
* `cls n m r` is the residue class of `r` inside `Icc (m+1) n`; the classes
  partition the interval (`biUnion_cls`) into progressions of total length
  `n - m` (`sum_cls_card`).
-/

namespace JSP000728

/-- A finset of naturals with no two consecutive elements. -/
def noConsec (t : Finset ℕ) : Prop := ∀ x ∈ t, x + 1 ∉ t

instance decidableNoConsec (t : Finset ℕ) : Decidable (noConsec t) := by
  unfold noConsec; infer_instance

/-- The family of no-two-consecutive subsets of `Finset.range L`. -/
def ncSets (L : ℕ) : Finset (Finset ℕ) := (Finset.range L).powerset.filter noConsec

theorem mem_ncSets {L : ℕ} {t : Finset ℕ} :
    t ∈ ncSets L ↔ t ⊆ Finset.range L ∧ noConsec t := by
  simp [ncSets]

/-- Subsets of `range (L+1)` whose insertion of `L+1` stays no-consecutive are
exactly the no-consecutive subsets of `range L`. -/
theorem ncSets_insert_filter (L : ℕ) :
    (Finset.range (L + 1)).powerset.filter (fun t => noConsec (insert (L + 1) t)) =
      ncSets L := by
  ext t
  rw [Finset.mem_filter, Finset.mem_powerset, mem_ncSets]
  constructor
  · rintro ⟨ht, hnc⟩
    refine ⟨?_, ?_⟩
    · intro x hx
      have hxlt : x < L + 1 := Finset.mem_range.mp (ht hx)
      rw [Finset.mem_range]
      by_cases h : x = L
      · rw [h] at hx
        exact absurd (Finset.mem_insert_self (L + 1) t)
          (hnc L (Finset.mem_insert_of_mem hx))
      · omega
    · intro x hx hx1
      exact hnc x (Finset.mem_insert_of_mem hx) (Finset.mem_insert_of_mem hx1)
  · rintro ⟨ht, hnc⟩
    refine ⟨?_, ?_⟩
    · intro x hx
      have := Finset.mem_range.mp (ht hx)
      exact Finset.mem_range.mpr (by omega)
    · intro x hx hcontra
      rw [Finset.mem_insert] at hx hcontra
      rcases hx with rfl | hx
      · rcases hcontra with h | h
        · omega
        · have := Finset.mem_range.mp (ht h)
          omega
      · have hxlt : x < L := Finset.mem_range.mp (ht hx)
        rcases hcontra with h | h
        · omega
        · exact hnc x hx h

/-- The two-step recursion for `ncSets`: subsets of `range (L+2)` either avoid
`L+1` (subsets of `range (L+1)`) or contain it (insertions into subsets of
`range L`). -/
theorem ncSets_succ_succ (L : ℕ) :
    ncSets (L + 2) =
      ncSets (L + 1) ∪ (ncSets L).image (insert (L + 1)) := by
  unfold ncSets
  rw [Finset.range_add_one, Finset.powerset_insert, Finset.filter_union,
    Finset.filter_image, ncSets_insert_filter]
  rfl

/-- `|ncSets (L+2)| = |ncSets (L+1)| + |ncSets L|`. -/
theorem ncSets_card_add_two (L : ℕ) :
    (ncSets (L + 2)).card = (ncSets (L + 1)).card + (ncSets L).card := by
  have hd : Disjoint (ncSets (L + 1)) ((ncSets L).image (insert (L + 1))) := by
    rw [Finset.disjoint_left]
    intro s hs hsB
    rw [Finset.mem_image] at hsB
    obtain ⟨t, -, rfl⟩ := hsB
    rw [mem_ncSets] at hs
    have := Finset.mem_range.mp (hs.1 (Finset.mem_insert_self (L + 1) t))
    omega
  rw [ncSets_succ_succ, Finset.card_union_of_disjoint hd]
  congr 1
  apply Finset.card_image_of_injOn
  intro t₁ ht₁ t₂ ht₂ h
  rw [Finset.mem_coe, mem_ncSets] at ht₁ ht₂
  have h1 : L + 1 ∉ t₁ := by
    intro hmem
    have := Finset.mem_range.mp (ht₁.1 hmem)
    omega
  have h2 : L + 1 ∉ t₂ := by
    intro hmem
    have := Finset.mem_range.mp (ht₂.1 hmem)
    omega
  have e := congrArg (Finset.erase · (L + 1)) h
  rwa [Finset.erase_insert h1, Finset.erase_insert h2] at e

/-- The Fibonacci count: `range L` has `F_{L+2}` no-consecutive subsets. -/
theorem ncSets_card (L : ℕ) : (ncSets L).card = Nat.fib (L + 2) := by
  suffices h : ∀ L : ℕ, (ncSets L).card = Nat.fib (L + 2) ∧
      (ncSets (L + 1)).card = Nat.fib (L + 3) from (h L).1
  intro L
  induction L with
  | zero =>
    constructor
    · show (ncSets 0).card = Nat.fib 2
      have h0 : ncSets 0 = {∅} := by
        ext t
        rw [mem_ncSets, Finset.range_zero, Finset.subset_empty, Finset.mem_singleton]
        refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
        subst h
        intro x hx
        exact absurd hx (Finset.notMem_empty _)
      rw [h0, Finset.card_singleton]
      exact Nat.fib_two.symm
    · show (ncSets 1).card = Nat.fib 3
      have h1 : ncSets 1 = {∅, {0}} := by
        ext t
        rw [mem_ncSets, Finset.range_one, Finset.subset_singleton_iff,
          Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨h, -⟩
          exact h
        · rintro (rfl | rfl)
          · exact ⟨Or.inl rfl, fun x hx => absurd hx (Finset.notMem_empty _)⟩
          · refine ⟨Or.inr rfl, ?_⟩
            intro x hx
            rw [Finset.mem_singleton] at hx ⊢
            subst hx
            decide
      rw [h1, Finset.card_pair (by simp)]
      show 2 = Nat.fib (1 + 2)
      rw [Nat.fib_add_two, Nat.fib_one, Nat.fib_two]
  | succ L ih =>
    obtain ⟨ih1, ih2⟩ := ih
    refine ⟨ih2, ?_⟩
    show (ncSets (L + 2)).card = Nat.fib (L + 1 + 3)
    rw [ncSets_card_add_two, ih2, ih1,
      show Nat.fib (L + 1 + 3) = Nat.fib (L + 2) + Nat.fib (L + 3) from Nat.fib_add_two]
    exact add_comm _ _

/-- `s` is *shift-free* for the shift `m` when `x ∈ s` forces `x + m ∉ s`. -/
def shiftFree (m : ℤ) (s : Finset ℤ) : Prop := ∀ x ∈ s, x + m ∉ s

instance decidableShiftFree (m : ℤ) (s : Finset ℤ) : Decidable (shiftFree m s) := by
  unfold shiftFree; infer_instance

theorem shiftFree.mono {m : ℤ} {s t : Finset ℤ} (h : shiftFree m s) (hts : t ⊆ s) :
    shiftFree m t :=
  fun x hx hxm => h x (hts hx) (hts hxm)

/-- **Binary factorisation.**  A shift-free subset of `T ⊆ T₁ ∪ T₂` restricts to
shift-free subsets of the parts, and `s ↦ (s ∩ T₁, s ∩ T₂)` is injective. -/
theorem card_powerset_filter_shiftFree_le_mul {m : ℤ} {T T₁ T₂ : Finset ℤ}
    (hT : T ⊆ T₁ ∪ T₂) :
    (T.powerset.filter (shiftFree m)).card ≤
      (T₁.powerset.filter (shiftFree m)).card *
        (T₂.powerset.filter (shiftFree m)).card := by
  rw [← Finset.card_product]
  refine Finset.card_le_card_of_injOn (fun s => (s ∩ T₁, s ∩ T₂)) ?_ ?_
  · intro s hs
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset] at hs
    rw [Finset.mem_coe, Finset.mem_product, Finset.mem_filter, Finset.mem_powerset,
      Finset.mem_filter, Finset.mem_powerset]
    exact ⟨⟨Finset.inter_subset_right, hs.2.mono Finset.inter_subset_left⟩,
      ⟨Finset.inter_subset_right, hs.2.mono Finset.inter_subset_left⟩⟩
  · intro s hs t ht h
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset] at hs ht
    have e1 : s ∩ T₁ = t ∩ T₁ := congrArg Prod.fst h
    have e2 : s ∩ T₂ = t ∩ T₂ := congrArg Prod.snd h
    calc s = s ∩ T₁ ∪ s ∩ T₂ := by
          rw [← Finset.inter_union_distrib_left,
            Finset.inter_eq_left.mpr (hs.1.trans hT)]
      _ = t ∩ T₁ ∪ t ∩ T₂ := by rw [e1, e2]
      _ = t := by
          rw [← Finset.inter_union_distrib_left,
            Finset.inter_eq_left.mpr (ht.1.trans hT)]

/-- **Product bound.**  If `T` is covered by the family `C`, shift-free subsets
of `T` are at most the product over the family of their shift-free subsets. -/
theorem card_powerset_filter_shiftFree_le_prod {m : ℤ} {ι : Type*} [DecidableEq ι]
    (R : Finset ι) (C : ι → Finset ℤ) (T : Finset ℤ) (hT : T ⊆ R.biUnion C) :
    (T.powerset.filter (shiftFree m)).card ≤
      ∏ r ∈ R, ((C r).powerset.filter (shiftFree m)).card := by
  suffices h : ∀ (R : Finset ι) (T : Finset ℤ), T ⊆ R.biUnion C →
      (T.powerset.filter (shiftFree m)).card ≤
        ∏ r ∈ R, ((C r).powerset.filter (shiftFree m)).card from h R T hT
  intro R
  induction R using Finset.induction with
  | empty =>
    intro T hT
    rw [Finset.biUnion_empty, Finset.subset_empty] at hT
    subst hT
    rw [Finset.prod_empty]
    calc ((∅ : Finset ℤ).powerset.filter (shiftFree m)).card
        ≤ (Finset.powerset (∅ : Finset ℤ)).card :=
          Finset.card_le_card (Finset.filter_subset _ _)
      _ = 1 := by rw [Finset.powerset_empty, Finset.card_singleton]
  | insert a s ha ih =>
    intro T hT
    rw [Finset.biUnion_insert] at hT
    refine (card_powerset_filter_shiftFree_le_mul hT).trans ?_
    rw [Finset.prod_insert ha]
    exact Nat.mul_le_mul le_rfl (ih _ Finset.Subset.rfl)

/-- The progression `a, a + m, a + 2m, …` of length `L`. -/
def prog (m : ℤ) (a : ℤ) (L : ℕ) : Finset ℤ :=
  (Finset.range L).image fun k : ℕ => a + m * (k : ℤ)

theorem prog_eq_image (m : ℤ) (a : ℤ) (L : ℕ) :
    prog m a L = (Finset.range L).image fun k : ℕ => a + m * (k : ℤ) := rfl

/-- Shift-free subsets of a length-`L` progression with step `m` correspond
(under `k ↦ a + m·k`) to no-consecutive subsets of `range L`; hence there are
`F_{L+2}` of them. -/
theorem card_powerset_filter_shiftFree_prog {m : ℤ} (hm : 0 < m) (a : ℤ) (L : ℕ) :
    ((prog m a L).powerset.filter (shiftFree m)).card = Nat.fib (L + 2) := by
  rw [prog_eq_image]
  set g : ℕ → ℤ := fun k => a + m * (k : ℤ) with hg_def
  have hg : Function.Injective g := by
    intro k₁ k₂ h
    simp only [hg_def] at h
    have h1 : m * (k₁ : ℤ) = m * (k₂ : ℤ) := add_left_cancel h
    have h2 : (k₁ : ℤ) = (k₂ : ℤ) := mul_left_cancel₀ (ne_of_gt hm) h1
    exact_mod_cast h2
  have hstep : ∀ k : ℕ, g k + m = g (k + 1) := by
    intro k
    simp only [hg_def]
    push_cast
    ring
  have hset : ((Finset.range L).image g).powerset.filter (shiftFree m) =
      (ncSets L).image (fun t => t.image g) := by
    ext u
    rw [Finset.mem_filter, Finset.mem_powerset]
    constructor
    · rintro ⟨hu, hsf⟩
      refine Finset.mem_image.mpr ⟨(Finset.range L).filter fun k => g k ∈ u, ?_, ?_⟩
      · rw [mem_ncSets]
        refine ⟨Finset.filter_subset _ _, ?_⟩
        intro k hk hcontra
        rw [Finset.mem_filter] at hk hcontra
        have h1 : g (k + 1) ∉ u := by
          have h2 := hsf (g k) hk.2
          rwa [hstep k] at h2
        exact h1 hcontra.2
      · ext x
        rw [Finset.mem_image]
        constructor
        · intro hx
          obtain ⟨k, hk, rfl⟩ := hx
          exact (Finset.mem_filter.mp hk).2
        · intro hx
          obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp (hu hx)
          exact ⟨k, Finset.mem_filter.mpr ⟨hk, hx⟩, rfl⟩
    · intro h
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp h
      rw [mem_ncSets] at ht
      refine ⟨Finset.image_subset_image ht.1, ?_⟩
      intro x hx
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
      rw [hstep k]
      intro h
      obtain ⟨k', hk', hkk'⟩ := Finset.mem_image.mp h
      have : k' = k + 1 := hg hkk'
      exact ht.2 k hk (this ▸ hk')
  rw [hset, Finset.card_image_of_injective _ (Finset.image_injective hg), ncSets_card]

/-- The residue class of `r` inside `Icc (m+1) n`, realised as the progression
`r + m, r + 2m, …`. -/
def cls (n : ℕ) (m r : ℤ) : Finset ℤ :=
  prog m (r + m) ((((n : ℤ) - r) / m).toNat)

theorem cls_eq_prog (n : ℕ) (m r : ℤ) :
    cls n m r = prog m (r + m) ((((n : ℤ) - r) / m).toNat) := rfl

theorem card_cls {n : ℕ} {m r : ℤ} (hm : m ≠ 0) :
    (cls n m r).card = (((n : ℤ) - r) / m).toNat := by
  have hg : Function.Injective (fun k : ℕ => r + m + m * (k : ℤ)) := by
    intro k₁ k₂ h
    simp only at h
    have h1 : m * (k₁ : ℤ) = m * (k₂ : ℤ) := add_left_cancel h
    have h2 : (k₁ : ℤ) = (k₂ : ℤ) := mul_left_cancel₀ hm h1
    exact_mod_cast h2
  rw [cls_eq_prog, prog_eq_image, Finset.card_image_of_injective _ hg,
    Finset.card_range]

/-- Every element of the class `r` lies in `Icc (m+1) n`. -/
theorem cls_subset_Icc {n : ℕ} {m r : ℤ} (hm : 1 ≤ m) (hr : 1 ≤ r) :
    cls n m r ⊆ Finset.Icc (m + 1) (n : ℤ) := by
  intro x hx
  rw [cls_eq_prog, prog_eq_image, Finset.mem_image] at hx
  obtain ⟨k, hk, rfl⟩ := hx
  rw [Finset.mem_range] at hk
  rw [Finset.mem_Icc]
  have hkz : (k : ℤ) < ((n : ℤ) - r) / m := Int.lt_toNat.mp hk
  have hmul : m * (k : ℤ) + m ≤ (n : ℤ) - r := by
    have h := (Int.le_ediv_iff_mul_le (by omega : 0 < m)).mp
      (show (k : ℤ) + 1 ≤ ((n : ℤ) - r) / m by omega)
    calc m * (k : ℤ) + m = ((k : ℤ) + 1) * m := by ring
      _ ≤ (n : ℤ) - r := h
  have hmk : 0 ≤ m * (k : ℤ) := Int.mul_nonneg (by omega) (by omega)
  constructor <;> omega

/-- Distinct residue classes are disjoint: `r₁ ≡ r₂ (mod m)` with
`r₁, r₂ ∈ [1, m]` forces `r₁ = r₂`. -/
theorem cls_pairwise {n : ℕ} {m : ℤ} (hm : 1 ≤ m) :
    (↑(Finset.Icc 1 m) : Set ℤ).PairwiseDisjoint (cls n m) := by
  intro r₁ hr₁ r₂ hr₂ hne
  show Disjoint (cls n m r₁) (cls n m r₂)
  rw [Finset.disjoint_left]
  intro x hx1 hx2
  rw [cls_eq_prog, prog_eq_image, Finset.mem_image] at hx1 hx2
  obtain ⟨k₁, -, e1⟩ := hx1
  obtain ⟨k₂, -, e2⟩ := hx2
  rw [Finset.mem_coe, Finset.mem_Icc] at hr₁ hr₂
  have h : r₁ + m + m * (k₁ : ℤ) = r₂ + m + m * (k₂ : ℤ) := e1.trans e2.symm
  have hdiff : r₂ - r₁ = m * ((k₁ : ℤ) - (k₂ : ℤ)) := by
    have h2 : m * ((k₁ : ℤ) - (k₂ : ℤ)) = m * (k₁ : ℤ) - m * (k₂ : ℤ) := by ring
    rw [h2]
    omega
  rcases lt_trichotomy ((k₁ : ℤ) - (k₂ : ℤ)) 0 with hc | hc | hc
  · have hle : m * ((k₁ : ℤ) - (k₂ : ℤ)) ≤ -m := by
      have h := (Int.mul_le_mul_left (by omega : 0 < m)).mpr
        (show (k₁ : ℤ) - (k₂ : ℤ) ≤ -1 by omega)
      rwa [mul_neg_one] at h
    omega
  · rw [hc, mul_zero] at hdiff
    omega
  · have hle : m ≤ m * ((k₁ : ℤ) - (k₂ : ℤ)) := by
      have h := (Int.mul_le_mul_left (by omega : 0 < m)).mpr
        (show 1 ≤ (k₁ : ℤ) - (k₂ : ℤ) by omega)
      rwa [mul_one] at h
    omega

/-- Every `x ∈ Icc (m+1) n` lies in its residue class `r = (x-1) % m + 1`. -/
theorem Icc_subset_biUnion_cls {n : ℕ} {m : ℤ} (hm : 1 ≤ m) :
    Finset.Icc (m + 1) (n : ℤ) ⊆ (Finset.Icc 1 m).biUnion (cls n m) := by
  intro x hx
  rw [Finset.mem_Icc] at hx
  obtain ⟨hx1, hx2⟩ := hx
  have hm0 : m ≠ 0 := by omega
  set e := (x - 1) % m with he_def
  set j := (x - 1) / m with hj_def
  have he0 : 0 ≤ e := Int.emod_nonneg _ hm0
  have helm : e < m := Int.emod_lt_of_pos _ (by omega)
  have hdecomp : m * j + e = x - 1 := by
    have h := Int.mul_ediv_add_emod (x - 1) m
    rwa [← hj_def, ← he_def] at h
  set r := e + 1 with hr_def
  have hrm : r ∈ Finset.Icc 1 m := by rw [Finset.mem_Icc]; omega
  rw [Finset.mem_biUnion]
  refine ⟨r, hrm, ?_⟩
  have hj1 : 1 ≤ j := by
    rw [hj_def, Int.le_ediv_iff_mul_le (by omega : 0 < m)]
    omega
  have hjle : j ≤ ((n : ℤ) - r) / m := by
    rw [Int.le_ediv_iff_mul_le (by omega : 0 < m), mul_comm j m]
    omega
  rw [cls_eq_prog, prog_eq_image, Finset.mem_image]
  refine ⟨(j - 1).toNat, ?_, ?_⟩
  · rw [Finset.mem_range, Int.lt_toNat]
    have hkj : ((j - 1).toNat : ℤ) = j - 1 := Int.toNat_of_nonneg (by omega)
    omega
  · have hkj : ((j - 1).toNat : ℤ) = j - 1 := Int.toNat_of_nonneg (by omega)
    rw [hkj]
    have hsub : m * (j - 1) = m * j - m := by ring
    rw [hsub]
    omega

/-- The classes partition `Icc (m+1) n`. -/
theorem biUnion_cls {n : ℕ} {m : ℤ} (hm : 1 ≤ m) :
    (Finset.Icc 1 m).biUnion (cls n m) = Finset.Icc (m + 1) (n : ℤ) := by
  apply le_antisymm
  · rw [Finset.biUnion_subset]
    intro r hr
    exact cls_subset_Icc hm (Finset.mem_Icc.mp hr).1
  · exact Icc_subset_biUnion_cls hm

/-- The class lengths sum to `n - m`. -/
theorem sum_cls_card {n : ℕ} {m : ℤ} (hm : 1 ≤ m) :
    ∑ r ∈ Finset.Icc 1 m, (((n : ℤ) - r) / m).toNat = ((n : ℤ) - m).toNat := by
  have h1 : ∑ r ∈ Finset.Icc 1 m, (((n : ℤ) - r) / m).toNat =
      ∑ r ∈ Finset.Icc 1 m, (cls n m r).card := by
    apply Finset.sum_congr rfl
    intro r _
    exact (card_cls (by omega : m ≠ 0)).symm
  rw [h1, ← Finset.card_biUnion (cls_pairwise hm), biUnion_cls hm, Int.card_Icc]
  congr 1
  omega

/-- The shift-free count of a residue class. -/
theorem card_powerset_filter_shiftFree_cls {n : ℕ} {m r : ℤ} (hm : 1 ≤ m) :
    ((cls n m r).powerset.filter (shiftFree m)).card =
      Nat.fib ((((n : ℤ) - r) / m).toNat + 2) :=
  card_powerset_filter_shiftFree_prog (by omega) (r + m) _

end JSP000728
