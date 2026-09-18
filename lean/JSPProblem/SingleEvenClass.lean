import JSPProblem.EvenOdd
import JSPProblem.FibBound

/-!
# JSP-000728 — maximal sum-free sets with a single even element

The "single-even" class: inclusion-maximal sum-free subsets
`M ⊆ {1,…,n}` whose even part is a singleton `{e}`.

* `singleEvenClass n e` — the class itself, with membership formulations
  `mem_singleEvenClass` and `mem_singleEvenClass_iff` (equivalence of the
  "even part equals `{e}`" and "unique even element" points of view,
  `filter_even_eq_singleton_iff`).
* Constraints on the odd part `O = M.filter Odd`:
  - `shiftFree_oddPart` — distance-`e` edges: `x ∈ O → x + e ∉ O`;
  - `sub_notMem_oddPart` — the same edge backwards: `x - e ∉ O`;
  - `add_ne_of_mem_oddPart`, `sub_e_notMem_oddPart` — the matching
    constraint `x, y ∈ O → x + y ≠ e`.
* `multiEvenPartSets n` — maximal sets with at least two even elements.
* `mixedPartSets_subset_biUnion_union_multiEven` — the parity
  decomposition: every mixed maximal set has a unique even element `e`
  (necessarily `2 ≤ e ≤ n`, so it lies in `singleEvenClass n e`) or at
  least two evens.
* Cardinality: the odd part of a member of `singleEvenClass n e` is an
  `e`-shift-free subset of the odd residue classes `r, r+e, r+2e, …`
  (`odds_subset_biUnion_prog`), so the Fibonacci path bound gives
  `card_singleEvenClass_le_prod`, and summing the path lengths gives
  the closed form `card_singleEvenClass_le_goldenRatio`:
  `(singleEvenClass n e).card ≤ φ ^ n` for `2 ≤ e ≤ n`, `e` even.
-/

namespace JSP000728

/-- Maximal sum-free subsets of `{1,…,n}` whose even part is the
singleton `{e}`. -/
def singleEvenClass (n : ℕ) (e : ℤ) : Finset (Finset ℤ) :=
  (maxSumFreeSets n).filter fun M => M.filter Even = {e}

theorem mem_singleEvenClass {n : ℕ} {M : Finset ℤ} {e : ℤ} :
    M ∈ singleEvenClass n e ↔ IsMaxSumFree n M ∧ M.filter Even = {e} := by
  rw [singleEvenClass, Finset.mem_filter, mem_maxSumFreeSets]

/-- The singleton even part unpacked: `M.filter Even = {e}` iff `e` is an
even element of `M` and every even element of `M` equals `e`. -/
theorem filter_even_eq_singleton_iff {M : Finset ℤ} {e : ℤ} :
    M.filter Even = {e} ↔ Even e ∧ e ∈ M ∧ ∀ x ∈ M, Even x → x = e := by
  constructor
  · intro h
    have he : e ∈ M.filter Even := by
      rw [h]; exact Finset.mem_singleton_self e
    rw [Finset.mem_filter] at he
    refine ⟨he.2, he.1, fun x hxM hxE => ?_⟩
    have hx : x ∈ M.filter Even := Finset.mem_filter.mpr ⟨hxM, hxE⟩
    rw [h] at hx
    exact Finset.mem_singleton.mp hx
  · rintro ⟨heE, heM, huniq⟩
    rw [Finset.eq_singleton_iff_unique_mem]
    exact ⟨Finset.mem_filter.mpr ⟨heM, heE⟩,
      fun x hx => huniq x (Finset.mem_filter.mp hx).1
        (Finset.mem_filter.mp hx).2⟩

/-- Equivalent membership formulation for `singleEvenClass`: maximal
sum-free, `e ∈ M` even, and `e` is the unique even element. -/
theorem mem_singleEvenClass_iff {n : ℕ} {M : Finset ℤ} {e : ℤ} :
    M ∈ singleEvenClass n e ↔
      IsMaxSumFree n M ∧ Even e ∧ e ∈ M ∧ ∀ x ∈ M, Even x → x = e := by
  rw [mem_singleEvenClass, filter_even_eq_singleton_iff]

theorem singleEvenClass_even {n : ℕ} {M : Finset ℤ} {e : ℤ}
    (hM : M ∈ singleEvenClass n e) : Even e :=
  (mem_singleEvenClass_iff.mp hM).2.1

theorem singleEvenClass_mem {n : ℕ} {M : Finset ℤ} {e : ℤ}
    (hM : M ∈ singleEvenClass n e) : e ∈ M :=
  (mem_singleEvenClass_iff.mp hM).2.2.1

theorem singleEvenClass_unique {n : ℕ} {M : Finset ℤ} {e : ℤ}
    (hM : M ∈ singleEvenClass n e) {x : ℤ} (hx : x ∈ M) (hxE : Even x) :
    x = e :=
  (mem_singleEvenClass_iff.mp hM).2.2.2 x hx hxE

/-- The even and odd parts of a finset of integers partition it. -/
theorem filter_even_union_filter_odd (M : Finset ℤ) :
    M.filter Even ∪ M.filter Odd = M := by
  have h : M.filter Odd = M.filter fun x => ¬ Even x := by
    ext x
    rw [Finset.mem_filter, Finset.mem_filter, Int.not_even_iff_odd]
  rw [h, Finset.filter_union_filter_not_eq]

/-- A member of `singleEvenClass n e` is `{e}` together with its odd
part. -/
theorem singleEvenClass_decomp {n : ℕ} {M : Finset ℤ} {e : ℤ}
    (hM : M ∈ singleEvenClass n e) : insert e (M.filter Odd) = M := by
  have hfilter := (mem_singleEvenClass.mp hM).2
  rw [Finset.insert_eq, ← hfilter, filter_even_union_filter_odd]

/-- The odd part of a member of `singleEvenClass n e` lies in `odds n`. -/
theorem oddPart_subset_odds {n : ℕ} {M : Finset ℤ} {e : ℤ}
    (hM : M ∈ singleEvenClass n e) : M.filter Odd ⊆ odds n := by
  intro x hx
  obtain ⟨hxM, hxO⟩ := Finset.mem_filter.mp hx
  exact mem_odds.mpr
    ⟨(mem_singleEvenClass.mp hM).1.1 hxM, Int.odd_iff.mp hxO⟩

/-- **Distance-`e` constraint (forward):** `x` in the odd part forces
`x + e` out of the odd part — `x, e ∈ M` sum to `x + e ∉ M`.  The odd
part is therefore an independent set in the distance-`e` graph on the
odd numbers of `{1,…,n}`. -/
theorem shiftFree_oddPart {n : ℕ} {M : Finset ℤ} {e : ℤ}
    (hM : M ∈ singleEvenClass n e) : shiftFree e (M.filter Odd) := by
  intro x hx hxe
  have hmax := (mem_singleEvenClass.mp hM).1
  have hxM : x ∈ M := (Finset.mem_filter.mp hx).1
  have heM : e ∈ M := singleEvenClass_mem hM
  exact hmax.2.1 x hxM e heM (Finset.mem_of_mem_filter _ hxe)

/-- **Distance-`e` constraint (backward):** `x ∈ O` forces `x - e ∉ O`,
since `(x - e) + e = x ∈ M` would violate sum-freeness. -/
theorem sub_notMem_oddPart {n : ℕ} {M : Finset ℤ} {e : ℤ}
    (hM : M ∈ singleEvenClass n e) {x : ℤ} (hx : x ∈ M.filter Odd) :
    x - e ∉ M.filter Odd := by
  intro h
  have hmax := (mem_singleEvenClass.mp hM).1
  have hsub : x - e ∈ M := Finset.mem_of_mem_filter _ h
  have heM : e ∈ M := singleEvenClass_mem hM
  have hxM : x ∈ M := Finset.mem_of_mem_filter _ hx
  have h1 : x - e + e ∉ M := hmax.2.1 (x - e) hsub e heM
  rw [sub_add_cancel] at h1
  exact h1 hxM

/-- **Sum-to-`e` constraint:** two elements of the odd part cannot sum to
`e`, since `e ∈ M` and `M` is sum-free. -/
theorem add_ne_of_mem_oddPart {n : ℕ} {M : Finset ℤ} {e : ℤ}
    (hM : M ∈ singleEvenClass n e) {x y : ℤ}
    (hx : x ∈ M.filter Odd) (hy : y ∈ M.filter Odd) : x + y ≠ e := by
  intro hxy
  have hmax := (mem_singleEvenClass.mp hM).1
  have heM : e ∈ M := singleEvenClass_mem hM
  have h1 : x + y ∉ M :=
    hmax.2.1 x (Finset.mem_of_mem_filter _ hx)
      y (Finset.mem_of_mem_filter _ hy)
  rw [hxy] at h1
  exact h1 heM

/-- The matching form of the sum-to-`e` constraint: `x ∈ O` forces
`e - x ∉ O`. -/
theorem sub_e_notMem_oddPart {n : ℕ} {M : Finset ℤ} {e : ℤ}
    (hM : M ∈ singleEvenClass n e) {x : ℤ} (hx : x ∈ M.filter Odd) :
    e - x ∉ M.filter Odd := by
  intro h
  exact add_ne_of_mem_oddPart hM hx h (by omega)

/-- The map `M ↦ M.filter Odd` injects `singleEvenClass n e` into the
`e`-shift-free subsets of `odds n`: `M` is recovered as `{e} ∪ O`. -/
theorem card_singleEvenClass_le {n : ℕ} {e : ℤ} :
    (singleEvenClass n e).card ≤
      ((odds n).powerset.filter (shiftFree e)).card := by
  refine Finset.card_le_card_of_injOn (fun M => M.filter Odd) ?_ ?_
  · intro M hM
    show M.filter Odd ∈ (odds n).powerset.filter (shiftFree e)
    rw [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨oddPart_subset_odds hM, shiftFree_oddPart hM⟩
  · intro M₁ h₁ M₂ h₂ h
    have h' : M₁.filter Odd = M₂.filter Odd := h
    rw [← singleEvenClass_decomp h₁, ← singleEvenClass_decomp h₂, h']

/-- For even `e ≥ 2` the odd residues in `{1,…,e}` are exactly
`1, 3, …, e-1`: there are `e/2` of them. -/
theorem card_filter_odd_Icc {e : ℤ} (he : Even e) (he2 : 2 ≤ e) :
    ((Finset.Icc 1 e).filter Odd).card = (e / 2).toNat := by
  obtain ⟨t, ht⟩ := he
  have hset : (Finset.Icc 1 e).filter Odd =
      (Finset.range (e / 2).toNat).image (fun k : ℕ => (2 : ℤ) * k + 1) := by
    ext x
    rw [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨⟨hx1, hxe⟩, k, hk⟩
      refine ⟨k.toNat, ?_, ?_⟩
      · rw [Finset.mem_range]
        omega
      · omega
    · rintro ⟨k, hk, rfl⟩
      rw [Finset.mem_range] at hk
      refine ⟨⟨by omega, by omega⟩, (k : ℤ), by omega⟩
  rw [hset, Finset.card_image_of_injective _
    (by intro a b h; have h' : (2 : ℤ) * a + 1 = 2 * b + 1 := h; omega),
    Finset.card_range]

/-- The odd residue classes `r, r+e, r+2e, …` for odd `r ∈ {1,…,e}` cover
`odds n` whenever `e` is a positive even integer.  (Each odd `x` is
`r + e·j` with `r = (x-1) % e + 1`, which is odd because `x - 1` and `e`
are both even.) -/
theorem odds_subset_biUnion_prog {n : ℕ} {e : ℤ} (he : Even e) (he0 : 0 < e) :
    odds n ⊆ ((Finset.Icc 1 e).filter Odd).biUnion
      (fun r => prog e r ((((n : ℤ) - r) / e).toNat + 1)) := by
  intro x hx
  obtain ⟨hxI, hxmod⟩ := mem_odds.mp hx
  obtain ⟨hx1, hxn⟩ := Finset.mem_Icc.mp hxI
  obtain ⟨a, ha⟩ := Int.odd_iff.mpr hxmod
  obtain ⟨t, ht⟩ := he
  set d := (x - 1) % e with hd_def
  set j := (x - 1) / e with hj_def
  have hd0 : 0 ≤ d := Int.emod_nonneg _ (by omega)
  have hde : d < e := Int.emod_lt_of_pos _ he0
  have hdecomp : e * j + d = x - 1 := by
    have h := Int.mul_ediv_add_emod (x - 1) e
    omega
  set r := d + 1 with hr_def
  have hrIcc : r ∈ Finset.Icc 1 e := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hje : e * j = 2 * (t * j) := by rw [ht]; ring
  have hdEven : Even d := ⟨a - t * j, by omega⟩
  obtain ⟨b, hb⟩ := hdEven
  have hrOdd : Odd r := ⟨b, by omega⟩
  rw [Finset.mem_biUnion]
  refine ⟨r, Finset.mem_filter.mpr ⟨hrIcc, hrOdd⟩, ?_⟩
  rw [prog_eq_image, Finset.mem_image]
  have hj0 : 0 ≤ j := by
    rw [hj_def, Int.le_ediv_iff_mul_le he0]
    omega
  have hjn : j ≤ ((n : ℤ) - r) / e := by
    rw [Int.le_ediv_iff_mul_le he0]
    have hje' : j * e = e * j := mul_comm _ _
    omega
  refine ⟨j.toNat, Finset.mem_range.mpr (by omega), ?_⟩
  show r + e * (j.toNat : ℤ) = x
  have hjj : (j.toNat : ℤ) = j := Int.toNat_of_nonneg hj0
  rw [hjj]
  omega

/-- **Product bound.**  The odd part of a member of `singleEvenClass n e`
restricts to a shift-free subset of each residue class, so the class has
at most `∏_{r odd ∈ [1,e]} F_{Lᵣ + 3}` elements, where `Lᵣ` is the number
of terms `r, r+e, …, ≤ n`. -/
theorem card_singleEvenClass_le_prod {n : ℕ} {e : ℤ}
    (he : Even e) (he0 : 0 < e) :
    (singleEvenClass n e).card ≤
      ∏ r ∈ (Finset.Icc 1 e).filter Odd,
        Nat.fib ((((n : ℤ) - r) / e).toNat + 3) := by
  calc (singleEvenClass n e).card
      ≤ ((odds n).powerset.filter (shiftFree e)).card :=
        card_singleEvenClass_le
    _ ≤ ∏ r ∈ (Finset.Icc 1 e).filter Odd,
          ((prog e r ((((n : ℤ) - r) / e).toNat + 1)).powerset.filter
            (shiftFree e)).card :=
        card_powerset_filter_shiftFree_le_prod _ _ _
          (odds_subset_biUnion_prog he he0)
    _ = ∏ r ∈ (Finset.Icc 1 e).filter Odd,
          Nat.fib ((((n : ℤ) - r) / e).toNat + 3) :=
        Finset.prod_congr rfl fun r _ =>
          card_powerset_filter_shiftFree_prog he0 r _

/-- **Closed form.**  For `2 ≤ e ≤ n` even, the single-even class has at
most `φ ^ n` members: each factor `F_{Lᵣ+3} ≤ φ^{Lᵣ+2}`, and the
exponents sum to at most `n`. -/
theorem card_singleEvenClass_le_goldenRatio {n : ℕ} {e : ℤ}
    (he : Even e) (he2 : 2 ≤ e) (hen : e ≤ (n : ℤ)) :
    ((singleEvenClass n e).card : ℝ) ≤ Real.goldenRatio ^ n := by
  have hcard : ((Finset.Icc 1 e).filter Odd).card = (e / 2).toNat :=
    card_filter_odd_Icc he he2
  have hprod := card_singleEvenClass_le_prod (n := n) he (by omega)
  obtain ⟨t, ht⟩ := he
  have hle : ∑ r ∈ (Finset.Icc 1 e).filter Odd, (((n : ℤ) - r) / e).toNat ≤
      ((n : ℤ) - e).toNat := by
    have h1 : ∑ r ∈ (Finset.Icc 1 e).filter Odd, (((n : ℤ) - r) / e).toNat ≤
        ∑ r ∈ Finset.Icc 1 e, (((n : ℤ) - r) / e).toNat :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ (Finset.Icc 1 e))
        fun r _ _ => Nat.zero_le _
    have h2 := sum_cls_card (n := n) (m := e) (by omega)
    exact h1.trans (le_of_eq h2)
  have hsum : ∑ r ∈ (Finset.Icc 1 e).filter Odd,
        ((((n : ℤ) - r) / e).toNat + 2) ≤ n := by
    rw [Finset.sum_add_distrib]
    have hconst : (∑ r ∈ (Finset.Icc 1 e).filter Odd, (2 : ℕ)) =
        ((Finset.Icc 1 e).filter Odd).card * 2 :=
      Finset.sum_const_nat fun _ _ => rfl
    rw [hconst, hcard]
    have h3 : ((n : ℤ) - e).toNat + (e / 2).toNat * 2 = n := by omega
    omega
  calc ((singleEvenClass n e).card : ℝ)
      ≤ ((∏ r ∈ (Finset.Icc 1 e).filter Odd,
            Nat.fib ((((n : ℤ) - r) / e).toNat + 3)) : ℕ) := by
        exact_mod_cast hprod
    _ = ∏ r ∈ (Finset.Icc 1 e).filter Odd,
          (Nat.fib ((((n : ℤ) - r) / e).toNat + 3) : ℝ) :=
        Nat.cast_prod _ _
    _ ≤ ∏ r ∈ (Finset.Icc 1 e).filter Odd,
          Real.goldenRatio ^ ((((n : ℤ) - r) / e).toNat + 2) := by
        apply Finset.prod_le_prod₀
        · intro r _
          exact Nat.cast_nonneg _
        · intro r _
          exact fib_le_goldenRatio_pow ((((n : ℤ) - r) / e).toNat + 2)
    _ = Real.goldenRatio ^
          (∑ r ∈ (Finset.Icc 1 e).filter Odd,
            ((((n : ℤ) - r) / e).toNat + 2)) := by
        rw [Finset.prod_pow_eq_pow_sum]
    _ ≤ Real.goldenRatio ^ n :=
        pow_le_pow_right₀ Real.one_lt_goldenRatio.le hsum

/-- Maximal sum-free subsets of `{1,…,n}` containing at least two even
elements. -/
def multiEvenPartSets (n : ℕ) : Finset (Finset ℤ) :=
  (maxSumFreeSets n).filter fun M => 2 ≤ (M.filter Even).card

theorem mem_multiEvenPartSets {n : ℕ} {M : Finset ℤ} :
    M ∈ multiEvenPartSets n ↔
      IsMaxSumFree n M ∧ 2 ≤ (M.filter Even).card := by
  rw [multiEvenPartSets, Finset.mem_filter, mem_maxSumFreeSets]

/-- **Single-even decomposition.**  A mixed maximal sum-free set either
has a unique even element `e` — necessarily `2 ≤ e ≤ n`, so it lies in
`singleEvenClass n e` — or has at least two even elements. -/
theorem mixedPartSets_subset_biUnion_union_multiEven (n : ℕ) :
    mixedPartSets n ⊆
      (Finset.Icc 2 (n : ℤ)).biUnion (singleEvenClass n) ∪
        multiEvenPartSets n := by
  intro M hM
  obtain ⟨hmax, ⟨e, heM, heE⟩, -⟩ := mem_mixedPartSets.mp hM
  have hpos : 0 < (M.filter Even).card :=
    Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨heM, heE⟩⟩
  rcases lt_or_ge (M.filter Even).card 2 with hlt | hge
  · have h1 : (M.filter Even).card = 1 := by omega
    obtain ⟨e', he'⟩ := Finset.card_eq_one.mp h1
    have he'M : e' ∈ M.filter Even := by
      rw [he']; exact Finset.mem_singleton_self e'
    obtain ⟨he'Mm, he'E⟩ := Finset.mem_filter.mp he'M
    obtain ⟨t, ht⟩ := he'E
    have he'I := Finset.mem_Icc.mp (hmax.1 he'Mm)
    apply Finset.mem_union.mpr
    apply Or.inl
    refine Finset.mem_biUnion.mpr
      ⟨e', Finset.mem_Icc.mpr ⟨by omega, he'I.2⟩, ?_⟩
    rw [mem_singleEvenClass]
    exact ⟨hmax, he'⟩
  · exact Finset.mem_union.mpr
      (Or.inr (mem_multiEvenPartSets.mpr ⟨hmax, hge⟩))

/-- **Full parity decomposition.**  Every maximal sum-free subset of
`{1,…,n}` is all-odd, all-even, a single-even set, or has at least two
even elements. -/
theorem maxSumFreeSets_subset_union_singleEven (n : ℕ) :
    maxSumFreeSets n ⊆ oddPartSets n ∪ evenPartSets n ∪
      ((Finset.Icc 2 (n : ℤ)).biUnion (singleEvenClass n) ∪
        multiEvenPartSets n) := by
  intro M hM
  have h := maxSumFreeSets_subset_union n hM
  rw [Finset.mem_union, Finset.mem_union] at h
  rcases h with (h | h) | h
  · exact Finset.mem_union.mpr
      (Or.inl (Finset.mem_union.mpr (Or.inl h)))
  · exact Finset.mem_union.mpr
      (Or.inl (Finset.mem_union.mpr (Or.inr h)))
  · exact Finset.mem_union.mpr
      (Or.inr (mixedPartSets_subset_biUnion_union_multiEven n h))

end JSP000728
