import JSPProblem.Basic
import Mathlib.Tactic

namespace JSP000728

/-- `{m} ∪ {2m+1, …, 3m}`: a maximal sum-free subset of `{1, …, 3m}`. -/
def thirdSet (m : ℕ) : Finset ℤ :=
  insert (m : ℤ) (Finset.Icc (2 * (m : ℤ) + 1) (3 * (m : ℤ)))

theorem thirdSet_isMaxSumFree {m : ℕ} (hm : 1 ≤ m) :
    IsMaxSumFree (3 * m) (thirdSet m) := by
  have h3m : ((3 * m : ℕ) : ℤ) = 3 * (m : ℤ) := by push_cast; ring
  have hmem : ∀ x : ℤ, x ∈ thirdSet m ↔
      x = (m : ℤ) ∨ (2 * (m : ℤ) + 1 ≤ x ∧ x ≤ 3 * (m : ℤ)) := by
    intro x
    simp only [thirdSet, Finset.mem_insert, Finset.mem_Icc]
  refine ⟨?_, ?_, ?_⟩
  · -- `thirdSet m ⊆ interval (3 * m)`
    intro x hx
    rw [hmem] at hx
    simp only [interval, Finset.mem_Icc]
    rcases hx with rfl | ⟨h1, h2⟩ <;> omega
  · -- `IsSumFree (thirdSet m)`
    intro a ha b hb hab
    rw [hmem] at ha hb hab
    rcases ha with rfl | ⟨ha1, ha2⟩ <;>
      rcases hb with rfl | ⟨hb1, hb2⟩ <;>
        rcases hab with hab | ⟨hab1, hab2⟩ <;> omega
  · -- maximality: adjoining any `x ∈ interval (3m) \ thirdSet m` breaks sum-freeness
    intro x hxn hxs hsf
    simp only [interval, Finset.mem_Icc] at hxn
    rw [hmem] at hxs
    have hxne : x ≠ (m : ℤ) := fun h => hxs (Or.inl h)
    have hxIcc : ¬ (2 * (m : ℤ) + 1 ≤ x ∧ x ≤ 3 * (m : ℤ)) :=
      fun h => hxs (Or.inr h)
    have hx2 : x ≤ 2 * (m : ℤ) := by
      by_contra h
      exact hxIcc ⟨by omega, by omega⟩
    rcases lt_or_ge x (m : ℤ) with hlt | hge
    · -- `x < m`: witness `x + (3m - x) = 3m`
      have hb : 3 * (m : ℤ) - x ∈ insert x (thirdSet m) :=
        Finset.mem_insert_of_mem (by rw [hmem]; right; constructor <;> omega)
      have hab : x + (3 * (m : ℤ) - x) ∈ insert x (thirdSet m) := by
        have e : x + (3 * (m : ℤ) - x) = 3 * (m : ℤ) := by ring
        rw [e]
        exact Finset.mem_insert_of_mem
          (by rw [hmem]; right; constructor <;> omega)
      exact hsf x (Finset.mem_insert_self _ _) _ hb hab
    · -- `m < x ≤ 2m`: witness `x + m = x + m`
      have hgt : (m : ℤ) < x := lt_of_le_of_ne hge (Ne.symm hxne)
      have hb : (m : ℤ) ∈ insert x (thirdSet m) :=
        Finset.mem_insert_of_mem (by rw [hmem]; left; rfl)
      have hab : x + (m : ℤ) ∈ insert x (thirdSet m) :=
        Finset.mem_insert_of_mem (by rw [hmem]; right; constructor <;> omega)
      exact hsf x (Finset.mem_insert_self _ _) _ hb hab

end JSP000728
