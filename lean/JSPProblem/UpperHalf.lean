import JSPProblem.Basic

namespace JSP000728

/-- The "upper half" `{x ∈ [1,n] : x > n/2}` of the interval. -/
def upperHalf (n : ℕ) : Finset ℤ := (interval n).filter (fun x => (n : ℤ) < 2 * x)

theorem mem_upperHalf {n : ℕ} {x : ℤ} :
    x ∈ upperHalf n ↔ x ∈ interval n ∧ (n : ℤ) < 2 * x :=
  Finset.mem_filter

theorem upperHalf_isMaxSumFree (n : ℕ) : IsMaxSumFree n (upperHalf n) := by
  refine ⟨fun x hx => (mem_upperHalf.mp hx).1, ?_, ?_⟩
  · -- Sum-freeness: `x, y > n/2` forces `x + y > n`, so `x + y ∉ interval n`.
    intro x hx y hy hxy
    rw [mem_upperHalf] at hx hy hxy
    have hxy_le : x + y ≤ (n : ℤ) := (Finset.mem_Icc.mp hxy.1).2
    omega
  · -- Maximality: any `x ∈ interval n` with `x ∉ upperHalf n` satisfies `2x ≤ n`,
    -- and `x` participates in a sum inside `insert x (upperHalf n)`.
    intro x hxn hxs hsf
    have hxI : 1 ≤ x ∧ x ≤ (n : ℤ) := Finset.mem_Icc.mp hxn
    have hnx : ¬ (n : ℤ) < 2 * x := fun h => hxs (mem_upperHalf.mpr ⟨hxn, h⟩)
    have hnI : (n : ℤ) ∈ interval n :=
      Finset.mem_Icc.mpr ⟨by omega, le_refl _⟩
    have hnUH : (n : ℤ) ∈ upperHalf n := mem_upperHalf.mpr ⟨hnI, by omega⟩
    by_cases h2x : 2 * x = (n : ℤ)
    · -- Case `2x = n`: the sum `x + x = n` obstructs sum-freeness.
      apply hsf x (Finset.mem_insert_self x _) x (Finset.mem_insert_self x _)
      have : x + x = (n : ℤ) := by omega
      rw [this]
      exact Finset.mem_insert_of_mem hnUH
    · -- Case `2x < n`: the sum `x + (n - x) = n` obstructs sum-freeness.
      have hbI : (n : ℤ) - x ∈ interval n :=
        Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      have hbUH : (n : ℤ) - x ∈ upperHalf n := mem_upperHalf.mpr ⟨hbI, by omega⟩
      apply hsf x (Finset.mem_insert_self x _) ((n : ℤ) - x)
        (Finset.mem_insert_of_mem hbUH)
      have : x + ((n : ℤ) - x) = (n : ℤ) := by omega
      rw [this]
      exact Finset.mem_insert_of_mem hnUH

end JSP000728
