import JSPProblem.Basic

namespace JSP000728

/-- `{m} ∪ {2m+2, …, 3m+1}`: a maximal sum-free subset of `{1, …, 3m+1}`
for `m ≥ 1`. -/
def singleSet (m : ℕ) : Finset ℤ :=
  insert (m : ℤ) (Finset.Icc (2 * (m : ℤ) + 2) (3 * (m : ℤ) + 1))

theorem mem_singleSet {m : ℕ} {x : ℤ} :
    x ∈ singleSet m ↔
      x = (m : ℤ) ∨ (2 * (m : ℤ) + 2 ≤ x ∧ x ≤ 3 * (m : ℤ) + 1) := by
  simp only [singleSet, Finset.mem_insert, Finset.mem_Icc]

/-- `{m} ∪ {2m+2, …, 3m+1}` is an inclusion-maximal sum-free subset of
`{1, …, 3m+1}` for `m ≥ 1`. -/
theorem singleSet_isMaxSumFree {m : ℕ} (hm : 1 ≤ m) :
    IsMaxSumFree (3 * m + 1) (singleSet m) := by
  have hm' : (1 : ℤ) ≤ m := by exact_mod_cast hm
  have hn : ((3 * m + 1 : ℕ) : ℤ) = 3 * (m : ℤ) + 1 := by omega
  refine ⟨fun y hy => ?_, fun a ha b hb hab => ?_, fun x hxn hxs hsf => ?_⟩
  · -- `singleSet m ⊆ interval (3m+1)`
    rcases mem_singleSet.mp hy with rfl | ⟨h1, h2⟩ <;>
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · -- `IsSumFree (singleSet m)`
    have ha' := mem_singleSet.mp ha
    have hb' := mem_singleSet.mp hb
    have hab' := mem_singleSet.mp hab
    rcases ha' with rfl | ⟨ha1, ha2⟩ <;>
      rcases hb' with rfl | ⟨hb1, hb2⟩ <;>
        rcases hab' with h | ⟨hc1, hc2⟩ <;> omega
  · -- maximality: each `x ∈ interval (3m+1) \ singleSet m` blocks
    have hxi := Finset.mem_Icc.mp hxn
    have hxne : x ≠ (m : ℤ) := by
      intro h
      exact hxs (mem_singleSet.mpr (Or.inl h))
    have hxle : x ≤ 2 * (m : ℤ) + 1 := by
      by_contra h
      exact hxs (mem_singleSet.mpr (Or.inr ⟨by omega, by omega⟩))
    rcases lt_or_ge x (m : ℤ) with hlt | hge
    · -- `1 ≤ x ≤ m - 1`: `x + (3m + 1 - x) = 3m + 1 ∈ s`
      have hb : 3 * (m : ℤ) + 1 - x ∈ singleSet m :=
        mem_singleSet.mpr (Or.inr ⟨by omega, by omega⟩)
      have hc : (3 * (m : ℤ) + 1) ∈ singleSet m :=
        mem_singleSet.mpr (Or.inr ⟨by omega, by omega⟩)
      have hsum : x + (3 * (m : ℤ) + 1 - x) ∈ insert x (singleSet m) := by
        have he : x + (3 * (m : ℤ) + 1 - x) = 3 * (m : ℤ) + 1 := by omega
        rw [he]
        exact Finset.mem_insert_of_mem hc
      exact hsf x (Finset.mem_insert_self x (singleSet m)) _
        (Finset.mem_insert_of_mem hb) hsum
    · -- `m + 1 ≤ x ≤ 2m + 1`
      have hxm : (m : ℤ) + 1 ≤ x := by omega
      rcases lt_or_ge x ((m : ℤ) + 2) with hlt2 | hge2
      · -- `x = m + 1`: `x + x = 2m + 2 ∈ s`
        have hc : x + x ∈ singleSet m :=
          mem_singleSet.mpr (Or.inr ⟨by omega, by omega⟩)
        exact hsf x (Finset.mem_insert_self x (singleSet m)) x
          (Finset.mem_insert_self x (singleSet m)) (Finset.mem_insert_of_mem hc)
      · -- `m + 2 ≤ x ≤ 2m + 1`: `x + m ∈ s`
        have hb : (m : ℤ) ∈ singleSet m :=
          mem_singleSet.mpr (Or.inl rfl)
        have hc : x + (m : ℤ) ∈ singleSet m :=
          mem_singleSet.mpr (Or.inr ⟨by omega, by omega⟩)
        exact hsf x (Finset.mem_insert_self x (singleSet m)) (m : ℤ)
          (Finset.mem_insert_of_mem hb) (Finset.mem_insert_of_mem hc)

end JSP000728
