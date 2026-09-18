import JSPProblem.Basic

namespace JSP000728

/-- The odd numbers in `{1, …, n}`. -/
def odds (n : ℕ) : Finset ℤ := (interval n).filter (fun x => x % 2 = 1)

theorem mem_odds {n : ℕ} {x : ℤ} :
    x ∈ odds n ↔ x ∈ interval n ∧ x % 2 = 1 :=
  Finset.mem_filter

/-- The odd numbers form an inclusion-maximal sum-free subset of `{1, …, n}`:
two odds sum to an even, and any even `x ∈ {1, …, n}` satisfies
`x = 1 + (x - 1)` with both summands odd. -/
theorem odds_isMaxSumFree (n : ℕ) : IsMaxSumFree n (odds n) := by
  refine ⟨fun x hx => (mem_odds.mp hx).1, fun x hx y hy hxy => ?_,
    fun x hxn hxs hsf => ?_⟩
  · -- `x % 2 = 1` and `y % 2 = 1` force `(x + y) % 2 = 0`, contradicting
    -- `x + y ∈ odds n`.
    have hxx := (mem_odds.mp hx).2
    have hyy := (mem_odds.mp hy).2
    have hsum := (mem_odds.mp hxy).2
    omega
  · -- `x ∈ {1, …, n} \ odds n` is even and at least `2`; the witnesses
    -- `1` and `x - 1` lie in `odds n` and sum to `x`.
    have hxi := Finset.mem_Icc.mp hxn
    have hxpar : x % 2 ≠ 1 := fun h => hxs (mem_odds.mpr ⟨hxn, h⟩)
    have hxmod : x % 2 = 0 := by omega
    have hx2 : 2 ≤ x := by omega
    have hn1 : (1 : ℤ) ≤ n := by omega
    have h1 : (1 : ℤ) ∈ odds n := by
      refine mem_odds.mpr ⟨Finset.mem_Icc.mpr ⟨le_refl 1, hn1⟩, ?_⟩
      omega
    have h2 : (x - 1) ∈ odds n := by
      refine mem_odds.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
      omega
    have hmem : (1 : ℤ) + (x - 1) ∈ insert x (odds n) := by
      have hab : (1 : ℤ) + (x - 1) = x := by omega
      rw [hab]
      exact Finset.mem_insert_self x (odds n)
    exact hsf 1 (Finset.mem_insert_of_mem h1) (x - 1)
      (Finset.mem_insert_of_mem h2) hmem

end JSP000728
