import JSPProblem.MinDecomp
import JSPProblem.NoConsec
import JSPProblem.Obstruction

/-!
# JSP-000728 — determination of `minClass n m` by its low trace

The Cameron–Erdős/Wolfovitz determination lemma: a maximal sum-free set
`M ⊆ {1, …, n}` with minimum `m` is **determined** by its trace
`M ∩ {1, …, n − m}`.  Indeed, for `x ∈ (n − m, n]` the only obstruction to
`x ∈ M` that maximality can produce is a sum `a + b = x`, whose summands
satisfy `a, b < x`; taking the least element of the symmetric difference of
two same-class sets transfers such a sum between them and yields a
contradiction with sum-freeness.

Consequences for the class count:

* `minClass_eq_of_trace_eq` — the determination lemma itself.
* `minClass_card_le_two_pow'` — `#minClass n m ≤ 2 ^ (n − m)` (the trace
  lands in `{1, …, n − m}`).
* `minClass_card_le_two_pow_determined` — the determination bound
  `#minClass n m ≤ 2 ^ (n − 2m + 1)` (the trace lands in `{m, …, n − m}`),
  an exponential improvement over the trivial `2 ^ (n + 1 − m)` of
  `minClass_card_le_two_pow`.
* `minClass_card_le_shiftFree_Icc` — `M ↦ (M ∩ {1,…,n−m}) ∖ {m}` injects
  into the `m`-shift-free subsets of `{m+1, …, n−m}`.
* `minClass_card_le_prod_fib` — the Fibonacci-factorisation refinement
  `#minClass n m ≤ ∏_{r=1}^{m} F_{L_r + 2}` with `L_r = ⌊(n−m−r)/m⌋`.
-/

namespace JSP000728

open scoped symmDiff

/-- One-sided step of the determination argument.  If `x` is the least
element of `A ∆ B` and `x ∈ A`, `x ∉ B`, `x > n − m`, then maximality of
`B` produces an obstruction at `x`: a sum `a + b = x` would transfer to `A`
(via leastness of `x`), contradicting sum-freeness of `A`; the translate
obstructions `a + x` / `x + a ∈ B` and `x + x ∈ B` are numerically
impossible because `a ≥ m` and `x > n − m`. -/
theorem minClass_symmDiff_min_absurd {n : ℕ} {m x : ℤ} {A B : Finset ℤ}
    (hA : IsMaxSumFree n A) (hB : IsMaxSumFree n B)
    (hAmin : ∀ y ∈ A, m ≤ y) (hBmin : ∀ y ∈ B, m ≤ y)
    (hxmin : ∀ y ∈ A ∆ B, x ≤ y)
    (hxA : x ∈ A) (hxB : x ∉ B) (hx : (n : ℤ) - m < x) : False := by
  have hxI : x ∈ interval n := hA.1 hxA
  have hxm : m ≤ x := hAmin x hxA
  rcases hB.exists_obstruction hxI hxB with hsum | hax | hxa | hxx
  · obtain ⟨a, ha, b, hb, hab⟩ := hsum
    have ha1 := Finset.mem_Icc.mp (hB.1 ha)
    have hb1 := Finset.mem_Icc.mp (hB.1 hb)
    -- `a, b < x` since `a, b ≥ 1`; hence `a, b ∉ A ∆ B` and both lie in `A`.
    have halt : a < x := by omega
    have hblt : b < x := by omega
    have haA : a ∈ A := by
      by_contra haA
      have hxa' := hxmin a (Finset.mem_symmDiff.mpr (Or.inr ⟨ha, haA⟩))
      omega
    have hbA : b ∈ A := by
      by_contra hbA
      have hxb' := hxmin b (Finset.mem_symmDiff.mpr (Or.inr ⟨hb, hbA⟩))
      omega
    exact hA.2.1 a haA b hbA (hab ▸ hxA)
  · obtain ⟨a, ha, hax⟩ := hax
    have hbnd := Finset.mem_Icc.mp (hB.1 hax)
    have ham := hBmin a ha
    omega
  · obtain ⟨a, ha, hxa⟩ := hxa
    have hbnd := Finset.mem_Icc.mp (hB.1 hxa)
    have ham := hBmin a ha
    omega
  · have hbnd := Finset.mem_Icc.mp (hB.1 hxx)
    omega

/-- **Determination lemma** (Cameron–Erdős/Wolfovitz).  Two members of
`minClass n m` with the same trace on `{1, …, n − m}` are equal: for
`x ∈ (n − m, n]`, membership in `M` is forced by the absence of a sum
`a + b = x` with `a, b ∈ M`, and such summands lie below `x`, so the least
element of a hypothetical symmetric difference cannot exist. -/
theorem minClass_eq_of_trace_eq {n : ℕ} {m : ℤ} {M₁ M₂ : Finset ℤ}
    (h₁ : M₁ ∈ minClass n m) (h₂ : M₂ ∈ minClass n m)
    (h : M₁ ∩ Finset.Icc 1 ((n : ℤ) - m) =
         M₂ ∩ Finset.Icc 1 ((n : ℤ) - m)) :
    M₁ = M₂ := by
  obtain ⟨hmax1, -, hmin1⟩ := mem_minClass.mp h₁
  obtain ⟨hmax2, -, hmin2⟩ := mem_minClass.mp h₂
  have hM1 : IsMaxSumFree n M₁ := mem_maxSumFreeSets.mp hmax1
  have hM2 : IsMaxSumFree n M₂ := mem_maxSumFreeSets.mp hmax2
  -- Elements at or below `n − m` transfer between the two sets.
  have hto2 : ∀ y : ℤ, y ≤ (n : ℤ) - m → y ∈ M₁ → y ∈ M₂ := by
    intro y hy hyM1
    have hyb := Finset.mem_Icc.mp (hM1.1 hyM1)
    exact (Finset.mem_inter.mp
      (h ▸ Finset.mem_inter.mpr ⟨hyM1, Finset.mem_Icc.mpr ⟨hyb.1, hy⟩⟩)).1
  have hto1 : ∀ y : ℤ, y ≤ (n : ℤ) - m → y ∈ M₂ → y ∈ M₁ := by
    intro y hy hyM2
    have hyb := Finset.mem_Icc.mp (hM2.1 hyM2)
    exact (Finset.mem_inter.mp
      (h.symm ▸ Finset.mem_inter.mpr ⟨hyM2, Finset.mem_Icc.mpr ⟨hyb.1, hy⟩⟩)).1
  by_contra hne
  have hD : (M₁ ∆ M₂).Nonempty := Finset.symmDiff_nonempty.mpr hne
  set x := (M₁ ∆ M₂).min' hD with hx_def
  have hxmem : x ∈ M₁ ∆ M₂ := Finset.min'_mem _ hD
  have hxmin : ∀ y ∈ M₁ ∆ M₂, x ≤ y := fun y hy => Finset.min'_le _ y hy
  -- The least disagreeing element lies above `n − m`.
  have hxgt : (n : ℤ) - m < x := by
    rcases Finset.mem_symmDiff.mp hxmem with ⟨hx1, hx2⟩ | ⟨hx1, hx2⟩
    · by_contra hle
      push Not at hle
      exact hx2 (hto2 x hle hx1)
    · by_contra hle
      push Not at hle
      exact hx2 (hto1 x hle hx1)
  rcases Finset.mem_symmDiff.mp hxmem with ⟨hxA, hxB⟩ | ⟨hxB, hxA⟩
  · exact minClass_symmDiff_min_absurd hM1 hM2 hmin1 hmin2 hxmin hxA hxB hxgt
  · have hxmin' : ∀ y ∈ M₂ ∆ M₁, x ≤ y := by
      intro y hy
      have hsym : M₂ ∆ M₁ = M₁ ∆ M₂ := symmDiff_comm M₂ M₁
      exact hxmin y (hsym ▸ hy)
    exact minClass_symmDiff_min_absurd hM2 hM1 hmin2 hmin1 hxmin' hxB hxA hxgt

/-- **Simplest determination bound.**  The trace `M ∩ {1,…,n−m}` injects
`minClass n m` into the powerset of `{1,…,n−m}`, giving
`#minClass n m ≤ 2 ^ (n − m)`. -/
theorem minClass_card_le_two_pow' {n : ℕ} {m : ℤ} :
    (minClass n m).card ≤ 2 ^ ((n : ℤ) - m).toNat := by
  have hcard : (Finset.Icc 1 ((n : ℤ) - m)).card = ((n : ℤ) - m).toNat := by
    rw [Int.card_Icc]
    congr 1
    ring
  rw [← hcard]
  calc (minClass n m).card
      ≤ ((Finset.Icc 1 ((n : ℤ) - m)).powerset).card := by
        refine Finset.card_le_card_of_injOn
          (fun M => M ∩ Finset.Icc 1 ((n : ℤ) - m)) ?_ ?_
        · intro M _
          exact Finset.mem_powerset.mpr Finset.inter_subset_right
        · intro M₁ hM₁ M₂ hM₂ h
          rw [Finset.mem_coe] at hM₁ hM₂
          exact minClass_eq_of_trace_eq hM₁ hM₂ h
    _ = 2 ^ (Finset.Icc 1 ((n : ℤ) - m)).card := Finset.card_powerset _

/-- **Cameron–Erdős/Wolfovitz determination bound.**  Since every element
of `M ∈ minClass n m` is at least `m`, the trace actually lands in
`{m,…,n−m}` of size `n − 2m + 1`, giving
`#minClass n m ≤ 2 ^ (n − 2m + 1)`. -/
theorem minClass_card_le_two_pow_determined {n : ℕ} {m : ℤ} :
    (minClass n m).card ≤ 2 ^ ((n : ℤ) - 2 * m + 1).toNat := by
  have hcard : (Finset.Icc m ((n : ℤ) - m)).card =
      ((n : ℤ) - 2 * m + 1).toNat := by
    rw [Int.card_Icc]
    congr 1
    ring
  rw [← hcard]
  calc (minClass n m).card
      ≤ ((Finset.Icc m ((n : ℤ) - m)).powerset).card := by
        refine Finset.card_le_card_of_injOn
          (fun M => M ∩ Finset.Icc 1 ((n : ℤ) - m)) ?_ ?_
        · intro M hM
          rw [Finset.mem_coe, mem_minClass] at hM
          obtain ⟨-, -, hmin⟩ := hM
          refine Finset.mem_powerset.mpr ?_
          intro x hx
          obtain ⟨hxM, hxI⟩ := Finset.mem_inter.mp hx
          obtain ⟨hx1, hx2⟩ := Finset.mem_Icc.mp hxI
          rw [Finset.mem_Icc]
          exact ⟨hmin x hxM, hx2⟩
        · intro M₁ hM₁ M₂ hM₂ h
          rw [Finset.mem_coe] at hM₁ hM₂
          exact minClass_eq_of_trace_eq hM₁ hM₂ h
    _ = 2 ^ (Finset.Icc m ((n : ℤ) - m)).card := Finset.card_powerset _

/-- Removing `m` from the trace injects `minClass n m` into the
`m`-shift-free subsets of `{m+1, …, n−m}`: `x, m ∈ M` forces `x + m ∉ M`
by sum-freeness.  Whether `m` itself lies in the trace depends only on the
threshold (`m ≤ n − m`), not on `M`, so the erased trace still determines
`M`. -/
theorem minClass_card_le_shiftFree_Icc {n : ℕ} {m : ℤ} :
    (minClass n m).card ≤
      ((Finset.Icc (m + 1) ((n : ℤ) - m)).powerset.filter
        (shiftFree m)).card := by
  -- The trace is recovered from its `m`-erasure and the `m`-indicator.
  have htm : ∀ M : Finset ℤ, m ∈ M →
      M ∩ Finset.Icc 1 ((n : ℤ) - m) =
        (M ∩ Finset.Icc 1 ((n : ℤ) - m)).erase m ∪
          (Finset.Icc 1 ((n : ℤ) - m)).filter (· = m) := by
    intro M hmM
    ext y
    simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_inter,
      Finset.mem_Icc, Finset.mem_filter]
    constructor
    · rintro ⟨hyM, hy1, hy2⟩
      by_cases hym : y = m
      · exact Or.inr ⟨⟨hy1, hy2⟩, hym⟩
      · exact Or.inl ⟨hym, hyM, hy1, hy2⟩
    · rintro (⟨hym, hyM, hy1, hy2⟩ | ⟨⟨hy1, hy2⟩, hym⟩)
      · exact ⟨hyM, hy1, hy2⟩
      · subst hym
        exact ⟨hmM, hy1, hy2⟩
  refine Finset.card_le_card_of_injOn
    (fun M => (M ∩ Finset.Icc 1 ((n : ℤ) - m)).erase m) ?_ ?_
  · intro M hM
    rw [Finset.mem_coe, mem_minClass] at hM
    obtain ⟨hmax, hmM, hmin⟩ := hM
    have hMmax : IsMaxSumFree n M := mem_maxSumFreeSets.mp hmax
    refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ?_, ?_⟩
    · intro x hx
      obtain ⟨hxne, hxmem⟩ := Finset.mem_erase.mp hx
      obtain ⟨hxM, hxI⟩ := Finset.mem_inter.mp hxmem
      obtain ⟨hx1, hx2⟩ := Finset.mem_Icc.mp hxI
      rw [Finset.mem_Icc]
      exact ⟨by have := hmin x hxM; omega, hx2⟩
    · intro x hx hxm
      exact not_mem_add_min_of_isMaxSumFree hMmax hmM
        (Finset.mem_inter.mp (Finset.mem_erase.mp hx).2).1
        (Finset.mem_inter.mp (Finset.mem_erase.mp hxm).2).1
  · intro M₁ hM₁ M₂ hM₂ he
    rw [Finset.mem_coe] at hM₁ hM₂
    dsimp only at he
    obtain ⟨-, hmM1, -⟩ := mem_minClass.mp hM₁
    obtain ⟨-, hmM2, -⟩ := mem_minClass.mp hM₂
    apply minClass_eq_of_trace_eq hM₁ hM₂
    rw [htm M₁ hmM1, htm M₂ hmM2, he]

/-- Residue-class cover of `{m+1, …, K}`: every `x` in the interval lies in
the progression `r + m, r + 2m, …` for `r = (x − 1) % m + 1 ∈ {1,…,m}`.
This is `Icc_subset_biUnion_cls` with the endpoint `n` replaced by an
arbitrary integer `K`. -/
theorem Icc_subset_biUnion_prog {m K : ℤ} (hm : 1 ≤ m) :
    Finset.Icc (m + 1) K ⊆ (Finset.Icc 1 m).biUnion
      (fun r => prog m (r + m) (((K - r) / m).toNat)) := by
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
  have hjle : j ≤ (K - r) / m := by
    rw [Int.le_ediv_iff_mul_le (by omega : 0 < m), mul_comm j m]
    omega
  rw [prog_eq_image, Finset.mem_image]
  refine ⟨(j - 1).toNat, ?_, ?_⟩
  · rw [Finset.mem_range, Int.lt_toNat]
    have hkj : ((j - 1).toNat : ℤ) = j - 1 := Int.toNat_of_nonneg (by omega)
    omega
  · have hkj : ((j - 1).toNat : ℤ) = j - 1 := Int.toNat_of_nonneg (by omega)
    rw [hkj]
    have hsub : m * (j - 1) = m * j - m := by ring
    rw [hsub]
    omega

/-- **Fibonacci product bound.**  Factoring the `m`-shift-free subsets of
`{m+1,…,n−m}` over the `m` residue classes gives
`#minClass n m ≤ ∏_{r=1}^{m} F_{L_r + 2}` with `L_r = ⌊(n−m−r)/m⌋`. -/
theorem minClass_card_le_prod_fib {n : ℕ} {m : ℤ} :
    (minClass n m).card ≤
      ∏ r ∈ Finset.Icc 1 m,
        Nat.fib ((((n : ℤ) - m - r) / m).toNat + 2) := by
  by_cases hm : 1 ≤ m
  · calc (minClass n m).card
        ≤ ((Finset.Icc (m + 1) ((n : ℤ) - m)).powerset.filter
            (shiftFree m)).card := minClass_card_le_shiftFree_Icc
      _ ≤ ∏ r ∈ Finset.Icc 1 m,
            ((prog m (r + m) ((((n : ℤ) - m - r) / m).toNat)).powerset.filter
              (shiftFree m)).card :=
          card_powerset_filter_shiftFree_le_prod (Finset.Icc 1 m)
            (fun r => prog m (r + m) ((((n : ℤ) - m - r) / m).toNat))
            (Finset.Icc (m + 1) ((n : ℤ) - m))
            (Icc_subset_biUnion_prog hm)
      _ = ∏ r ∈ Finset.Icc 1 m,
            Nat.fib ((((n : ℤ) - m - r) / m).toNat + 2) :=
          Finset.prod_congr rfl fun r _ =>
            card_powerset_filter_shiftFree_prog (by omega) (r + m) _
  · -- If `m < 1` the class is empty (`m ∈ M ⊆ {1,…,n}`).
    have hempty : minClass n m = ∅ := by
      ext M
      simp only [mem_minClass, Finset.notMem_empty, iff_false, not_and]
      rintro hmax hmM -
      have := Finset.mem_Icc.mp ((mem_maxSumFreeSets.mp hmax).1 hmM)
      omega
    rw [hempty, Finset.card_empty]
    exact Nat.zero_le _

end JSP000728
