import JSPProblem.Basic

namespace JSP000728

/-- `{m, m+1} ∪ {2m+3, …, 3m+2}`: a maximal sum-free subset of `{1, …, 3m+2}`
for `m ≥ 2`. -/
def pairSet (m : ℕ) : Finset ℤ :=
  insert (m : ℤ) (insert ((m : ℤ) + 1) (Finset.Icc (2 * (m : ℤ) + 3) (3 * (m : ℤ) + 2)))

theorem pairSet_isMaxSumFree {m : ℕ} (hm : 2 ≤ m) :
    IsMaxSumFree (3 * m + 2) (pairSet m) := by
  have hm' : (2 : ℤ) ≤ (m : ℤ) := by exact_mod_cast hm
  have hn : interval (3 * m + 2) = Finset.Icc (1 : ℤ) (3 * (m : ℤ) + 2) := by
    simp [interval]
  -- Membership helpers for the three layers of `pairSet m`.
  have hm_in : (m : ℤ) ∈ pairSet m := Finset.mem_insert_self _ _
  have hm1_in : (m : ℤ) + 1 ∈ pairSet m :=
    Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hIcc_in : ∀ z : ℤ, 2 * (m : ℤ) + 3 ≤ z → z ≤ 3 * (m : ℤ) + 2 →
      z ∈ pairSet m :=
    fun z h1 h2 =>
      Finset.mem_insert_of_mem
        (Finset.mem_insert_of_mem (Finset.mem_Icc.mpr ⟨h1, h2⟩))
  refine ⟨?_, ?_, ?_⟩
  · -- `pairSet m ⊆ interval (3 * m + 2)`.
    intro z hz
    rw [hn]
    simp only [pairSet, Finset.mem_insert, Finset.mem_Icc] at hz
    rcases hz with rfl | rfl | ⟨h1, h2⟩ <;>
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · -- `IsSumFree (pairSet m)`: case split on which layer `a`, `b`, `a + b`
    -- lie in; each of the 27 combinations is linearly impossible.
    intro a ha b hb hab
    simp only [pairSet, Finset.mem_insert, Finset.mem_Icc] at ha hb hab
    rcases ha with rfl | rfl | ⟨ha1, ha2⟩ <;>
      rcases hb with rfl | rfl | ⟨hb1, hb2⟩ <;>
        rcases hab with h | h | ⟨h1, h2⟩ <;> omega
  · -- Maximality: every `x ∈ interval (3m+2) \ pairSet m` creates a sum
    -- `a + b = c` inside `insert x (pairSet m)`.
    intro x hx hxs hsf
    rw [hn] at hx
    obtain ⟨hx1, hx2⟩ := Finset.mem_Icc.mp hx
    -- Any of the three membership alternatives contradicts `hxs`.
    have hcontra :
        x = (m : ℤ) ∨ x = (m : ℤ) + 1 ∨
          (2 * (m : ℤ) + 3 ≤ x ∧ x ≤ 3 * (m : ℤ) + 2) → False := by
      intro h
      rcases h with rfl | rfl | ⟨h1, h2⟩
      · exact hxs hm_in
      · exact hxs hm1_in
      · exact hxs (hIcc_in _ h1 h2)
    have hne_m : x ≠ (m : ℤ) := fun h => hcontra (Or.inl h)
    have hne_m1 : x ≠ (m : ℤ) + 1 := fun h => hcontra (Or.inr (Or.inl h))
    have hx_le : x ≤ 2 * (m : ℤ) + 2 := by
      by_contra hle
      exact hcontra (Or.inr (Or.inr ⟨by omega, hx2⟩))
    rcases lt_or_ge x (m : ℤ) with hxlt | hxge
    · -- `1 ≤ x ≤ m - 1`: use `x + (3m + 2 - x) = 3m + 2`.
      have hb : 3 * (m : ℤ) + 2 - x ∈ pairSet m := hIcc_in _ (by omega) (by omega)
      have hc : 3 * (m : ℤ) + 2 ∈ pairSet m := hIcc_in _ (by omega) (le_refl _)
      have hsum : x + (3 * (m : ℤ) + 2 - x) = 3 * (m : ℤ) + 2 := by omega
      have hmem : x + (3 * (m : ℤ) + 2 - x) ∈ insert x (pairSet m) := by
        rw [hsum]
        exact Finset.mem_insert_of_mem hc
      exact hsf x (Finset.mem_insert_self _ _) (3 * (m : ℤ) + 2 - x)
        (Finset.mem_insert_of_mem hb) hmem
    · rcases eq_or_ne x ((m : ℤ) + 2) with hxeq | hxne
      · -- `x = m + 2`: use `x + x = 2m + 4 ∈ pairSet m` (needs `m ≥ 2`).
        have hc : 2 * (m : ℤ) + 4 ∈ pairSet m := hIcc_in _ (by omega) (by omega)
        have hsum : x + x = 2 * (m : ℤ) + 4 := by omega
        have hmem : x + x ∈ insert x (pairSet m) := by
          rw [hsum]
          exact Finset.mem_insert_of_mem hc
        exact hsf x (Finset.mem_insert_self _ _) x
          (Finset.mem_insert_self _ _) hmem
      · -- `m + 3 ≤ x ≤ 2m + 2`: use `x + m ∈ pairSet m`.
        have hmem : x + (m : ℤ) ∈ insert x (pairSet m) :=
          Finset.mem_insert_of_mem (hIcc_in _ (by omega) (by omega))
        exact hsf x (Finset.mem_insert_self _ _) (m : ℤ)
          (Finset.mem_insert_of_mem hm_in) hmem

end JSP000728
