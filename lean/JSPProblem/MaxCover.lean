import JSPProblem.MaxDecomp
import Mathlib.Tactic.Linarith

/-!
# JSP-000728 — covering of the top element

For an inclusion-maximal sum-free `M ⊆ {1,…,n}`, the top element `n` is
either itself a member of `M` — equivalently `max M = n` — or it is a sum
`a + b` of two elements of `M` (`maxSumFree_covers_top`).  Indeed,
`insert n M` fails to be sum-free, and the only obstruction that can
involve `n` is `n = a + b`: the sums `a + n`, `n + a`, `n + n` all exceed
`n`, while every member of `M` is at most `n`.

Consequences recorded here:

* `le_two_mul_max'_of_mem_maxSumFreeSets` — `n ≤ 2 · max M` for every
  maximal sum-free `M ⊆ {1,…,n}`;
* `maxClass_eq_empty_of_two_mul_lt` — the class `maxClass n t` is empty
  whenever `2t < n` (sharper than `maxClass_eq_empty_of_sq_lt`, which
  requires `(t + 1)² < 4(n − t)` — e.g. `t = 3`, `n = 7` is covered here
  but not there);
* `maxSumFreeCount_eq_sum_maxClass_of_ge` — the maximum decomposition
  `f n = ∑_{t=1}^{n} |maxClass n t|` therefore collapses to the upper
  range `2t ≥ n` (`maxSumFreeCount_eq_sum_maxClass_Icc` gives the
  `Icc ⌈n/2⌉ n` form);
* `exists_sum_eq_top_of_mem_maxClass_of_lt` — for `M ∈ maxClass n t`
  with `t < n`, the covering lemma specialised at `y = n` produces
  `a, b ∈ M` with `a + b = n`.
-/

namespace JSP000728

/-- **Top covering.**  For a maximal sum-free `M ⊆ {1,…,n}` with `n ≥ 1`,
either `n ∈ M` or `n` is a sum of two elements of `M`: the obstruction to
adjoining `n` cannot be `a + n ∈ M`, `n + a ∈ M` or `n + n ∈ M`, since all
of these exceed `n` while every member of `M` is at most `n`. -/
theorem maxSumFree_covers_top {n : ℕ} (hn : 1 ≤ n) {M : Finset ℤ}
    (hM : M ∈ maxSumFreeSets n) :
    (n : ℤ) ∈ M ∨ ∃ a ∈ M, ∃ b ∈ M, a + b = (n : ℤ) := by
  have hmax := mem_maxSumFreeSets.mp hM
  by_cases hnM : (n : ℤ) ∈ M
  · exact Or.inl hnM
  · have hnI : (n : ℤ) ∈ interval n :=
      Finset.mem_Icc.mpr ⟨by exact_mod_cast hn, le_refl _⟩
    rcases hmax.exists_obstruction hnI hnM with
        ⟨a, ha, b, hb, hab⟩ | ⟨a, ha, han⟩ | ⟨a, ha, hna⟩ | hnn
    · exact Or.inr ⟨a, ha, b, hb, hab⟩
    · have ha1 := interval_one_le (hmax.1 ha)
      have hle := interval_le (hmax.1 han)
      omega
    · have ha1 := interval_one_le (hmax.1 ha)
      have hle := interval_le (hmax.1 hna)
      omega
    · have hle := interval_le (hmax.1 hnn)
      have hn' : (1 : ℤ) ≤ n := by exact_mod_cast hn
      omega

/-- If `n ∈ M`, the maximum of `M` is exactly `n`. -/
theorem max'_eq_top_of_mem {n : ℕ} (hn : 1 ≤ n) {M : Finset ℤ}
    (hM : M ∈ maxSumFreeSets n) (hnM : (n : ℤ) ∈ M) :
    M.max' (nonempty_of_mem_maxSumFreeSets hn hM) = (n : ℤ) := by
  have hsub := (mem_maxSumFreeSets.mp hM).1
  exact le_antisymm (interval_le (hsub (Finset.max'_mem M _)))
    (Finset.le_max' M _ hnM)

/-- Disjunctive form of top covering: `max M = n` or `n = a + b` with
`a, b ∈ M`. -/
theorem max'_eq_top_or_sum_eq {n : ℕ} (hn : 1 ≤ n) {M : Finset ℤ}
    (hM : M ∈ maxSumFreeSets n) :
    M.max' (nonempty_of_mem_maxSumFreeSets hn hM) = (n : ℤ) ∨
      ∃ a ∈ M, ∃ b ∈ M, a + b = (n : ℤ) := by
  rcases maxSumFree_covers_top hn hM with h | h
  · exact Or.inl (max'_eq_top_of_mem hn hM h)
  · exact Or.inr h

/-- **The maximum is at least `n/2`.**  Every maximal sum-free
`M ⊆ {1,…,n}` satisfies `n ≤ 2 · max M`: if `n ∈ M` then `max M = n`, and
otherwise `n = a + b` with `a, b ≤ max M`. -/
theorem le_two_mul_max'_of_mem_maxSumFreeSets {n : ℕ} (hn : 1 ≤ n)
    {M : Finset ℤ} (hM : M ∈ maxSumFreeSets n) :
    (n : ℤ) ≤ 2 * M.max' (nonempty_of_mem_maxSumFreeSets hn hM) := by
  have hne := nonempty_of_mem_maxSumFreeSets hn hM
  have hsub := (mem_maxSumFreeSets.mp hM).1
  rcases maxSumFree_covers_top hn hM with hmem | ⟨a, ha, b, hb, hab⟩
  · have hle := Finset.le_max' M _ hmem
    have hpos := interval_one_le (hsub (Finset.max'_mem M hne))
    omega
  · have hae := Finset.le_max' M a ha
    have hbe := Finset.le_max' M b hb
    omega

/-- **Vanishing by covering.**  If `2t < n` then `maxClass n t` is empty:
the covering lemma would put `n ∈ (t, n]` into `M + M`, but every member
of `M + M` is at most `2t`.  This is strictly sharper than
`maxClass_eq_empty_of_sq_lt`, which needs `(t + 1)² < 4(n − t)`. -/
theorem maxClass_eq_empty_of_two_mul_lt {n : ℕ} {t : ℤ}
    (h : 2 * t < (n : ℤ)) : maxClass n t = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro M hM
  obtain ⟨hmax, htM, hle⟩ := mem_maxClass.mp hM
  have hsub := (mem_maxSumFreeSets.mp hmax).1
  have htI := Finset.mem_Icc.mp (hsub htM)
  have hnIoc : (n : ℤ) ∈ Finset.Ioc t (n : ℤ) :=
    Finset.mem_Ioc.mpr ⟨by omega, le_refl _⟩
  rcases Finset.mem_image.mp
      (ioc_subset_image_sum_of_mem_maxClass hM hnIoc) with ⟨⟨a, b⟩, hab, habeq⟩
  obtain ⟨hab1, hab2⟩ := Finset.mem_product.mp hab
  have ha := hle a hab1
  have hb := hle b hab2
  have habeq' : a + b = (n : ℤ) := habeq
  omega

/-- Specialising the covering lemma at `y = n`: if `M ∈ maxClass n t`
and `t < n`, then `n` is a sum of two elements of `M`. -/
theorem exists_sum_eq_top_of_mem_maxClass_of_lt {n : ℕ} {M : Finset ℤ}
    {t : ℤ} (hM : M ∈ maxClass n t) (htn : t < (n : ℤ)) :
    ∃ a ∈ M, ∃ b ∈ M, a + b = (n : ℤ) := by
  have hnIoc : (n : ℤ) ∈ Finset.Ioc t (n : ℤ) :=
    Finset.mem_Ioc.mpr ⟨htn, le_refl _⟩
  rcases Finset.mem_image.mp
      (ioc_subset_image_sum_of_mem_maxClass hM hnIoc) with ⟨⟨a, b⟩, hab, habeq⟩
  obtain ⟨hab1, hab2⟩ := Finset.mem_product.mp hab
  exact ⟨a, hab1, b, hab2, habeq⟩

/-- **Restricted maximum decomposition.**  Since `maxClass n t` is empty
for `2t < n`, the sum `f n = ∑_{t=1}^{n} |maxClass n t|` collapses to its
upper range `2t ≥ n`. -/
theorem maxSumFreeCount_eq_sum_maxClass_of_ge {n : ℕ} (hn : 1 ≤ n) :
    maxSumFreeCount n =
      ∑ t ∈ (Finset.Icc 1 (n : ℤ)).filter (fun t => (n : ℤ) ≤ 2 * t),
        (maxClass n t).card := by
  rw [maxSumFreeCount_eq_sum_maxClass hn]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro t htI htnot
  rw [Finset.mem_filter] at htnot
  have hlt : 2 * t < (n : ℤ) := by
    by_contra hcon
    exact htnot ⟨htI, le_of_not_gt hcon⟩
  rw [maxClass_eq_empty_of_two_mul_lt hlt, Finset.card_empty]

/-- `Icc` form of the restricted decomposition: `f n` is the sum of
`|maxClass n t|` over `t ∈ Icc ⌈n/2⌉ n`, where `⌈n/2⌉ = (n + 1)/2`. -/
theorem maxSumFreeCount_eq_sum_maxClass_Icc {n : ℕ} (hn : 1 ≤ n) :
    maxSumFreeCount n =
      ∑ t ∈ Finset.Icc (((n : ℤ) + 1) / 2) (n : ℤ), (maxClass n t).card := by
  rw [maxSumFreeCount_eq_sum_maxClass_of_ge hn]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext t
  simp only [Finset.mem_filter, Finset.mem_Icc]
  have hn' : (1 : ℤ) ≤ n := by exact_mod_cast hn
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    omega
  · rintro ⟨h1, h2⟩
    omega

end JSP000728
