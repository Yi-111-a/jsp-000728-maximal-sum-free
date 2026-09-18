import JSPProblem.Basic

/-!
# The Balogh–Liu–Sharifzadeh–Treglown / Cameron–Erdős lower-bound family

For `k ≥ 1` write `I₂ = {3k+1, …, 4k}`.  For every `T ⊆ I₂` the set
`{k} ∪ T ∪ {x - k : x ∈ I₂ \ T}` is sum-free, and any sum-free set `M`
containing it satisfies `M ∩ I₂ = T`.  Hence distinct subsets `T` of `I₂`
yield distinct maximal sum-free sets — the BLST15 (arXiv:1409.5661)
counting argument for the Cameron–Erdős lower bound.
-/

namespace JSP000728

/-- The "free" interval `{3k+1,…,4k}` of the BLST construction. -/
def blstI2 (k : ℕ) : Finset ℤ := Finset.Icc (3 * (k : ℤ) + 1) (4 * (k : ℤ))

/-- The BLST/Cameron–Erdős family member: `{k} ∪ T ∪ {x - k : x ∈ I₂ \ T}`. -/
def blstSet (k : ℕ) (T : Finset ℤ) : Finset ℤ :=
  insert (k : ℤ) (T ∪ (blstI2 k \ T).image (· - (k : ℤ)))

theorem mem_blstI2 {k : ℕ} {x : ℤ} :
    x ∈ blstI2 k ↔ 3 * (k : ℤ) + 1 ≤ x ∧ x ≤ 4 * (k : ℤ) :=
  Finset.mem_Icc

theorem card_blstI2 {k : ℕ} : (blstI2 k).card = k := by
  rw [blstI2, Int.card_Icc]
  omega

theorem blstI2_subset_interval {n k : ℕ} (hk : 1 ≤ k) (hkn : 4 * k ≤ n) :
    blstI2 k ⊆ interval n := by
  have hk' : (1 : ℤ) ≤ (k : ℤ) := Int.ofNat_le.mpr hk
  have hkn' : 4 * (k : ℤ) ≤ (n : ℤ) := by
    have h := Int.ofNat_le.mpr hkn
    push_cast at h
    omega
  intro x hx
  rw [mem_blstI2] at hx
  simp only [interval, Finset.mem_Icc]
  omega

theorem blstSet_subset_interval {n k : ℕ} {T : Finset ℤ}
    (hk : 1 ≤ k) (hkn : 4 * k ≤ n) (hT : T ⊆ blstI2 k) :
    blstSet k T ⊆ interval n := by
  have hk' : (1 : ℤ) ≤ (k : ℤ) := Int.ofNat_le.mpr hk
  have hkn' : 4 * (k : ℤ) ≤ (n : ℤ) := by
    have h := Int.ofNat_le.mpr hkn
    push_cast at h
    omega
  intro x hx
  simp only [interval, Finset.mem_Icc]
  rw [blstSet, Finset.mem_insert] at hx
  rcases hx with rfl | hx
  · omega
  rw [Finset.mem_union] at hx
  rcases hx with hxT | hxim
  · obtain ⟨h1, h2⟩ := mem_blstI2.mp (hT hxT)
    omega
  · rw [Finset.mem_image] at hxim
    obtain ⟨y, hy, rfl⟩ := hxim
    rw [Finset.mem_sdiff] at hy
    obtain ⟨h1, h2⟩ := mem_blstI2.mp hy.1
    omega

/-- Membership in `blstSet k T` implies one of three value ranges. -/
theorem blstSet_mem_range {k : ℕ} {T : Finset ℤ} (hT : T ⊆ blstI2 k) {x : ℤ}
    (hx : x ∈ blstSet k T) :
    x = (k : ℤ) ∨ (2 * (k : ℤ) + 1 ≤ x ∧ x ≤ 3 * (k : ℤ)) ∨
      (3 * (k : ℤ) + 1 ≤ x ∧ x ≤ 4 * (k : ℤ) ∧ x ∈ T) := by
  rw [blstSet, Finset.mem_insert] at hx
  rcases hx with rfl | hx
  · exact Or.inl rfl
  rw [Finset.mem_union] at hx
  rcases hx with hxT | hxim
  · obtain ⟨h1, h2⟩ := mem_blstI2.mp (hT hxT)
    exact Or.inr (Or.inr ⟨h1, h2, hxT⟩)
  · rw [Finset.mem_image] at hxim
    obtain ⟨y, hy, rfl⟩ := hxim
    rw [Finset.mem_sdiff] at hy
    obtain ⟨h1, h2⟩ := mem_blstI2.mp hy.1
    exact Or.inr (Or.inl ⟨by omega, by omega⟩)

theorem isSumFree_blstSet {k : ℕ} {T : Finset ℤ} (hk : 1 ≤ k) (hT : T ⊆ blstI2 k) :
    IsSumFree (blstSet k T) := by
  have hk' : (1 : ℤ) ≤ (k : ℤ) := Int.ofNat_le.mpr hk
  intro a ha b hb hab
  -- Every element `x` of `blstSet k T` satisfies `k ≤ x`, and `x = k` or
  -- `2k + 1 ≤ x`.
  have hmem : ∀ x : ℤ, x ∈ blstSet k T →
      (k : ℤ) ≤ x ∧ (x = (k : ℤ) ∨ 2 * (k : ℤ) + 1 ≤ x) := by
    intro x hx
    rcases blstSet_mem_range hT hx with rfl | ⟨h1, h2⟩ | ⟨h1, h2, -⟩ <;>
      constructor <;> omega
  obtain ⟨ha_lo, ha_hi⟩ := hmem a ha
  obtain ⟨hb_lo, hb_hi⟩ := hmem b hb
  rcases blstSet_mem_range hT hab with habk | ⟨hab1, hab2⟩ | ⟨hab1, hab2, habT⟩
  · -- `a + b = k`: impossible since `a, b ≥ k ≥ 1` give `a + b ≥ 2k > k`.
    omega
  · -- `a + b ∈ {2k+1,…,3k}`: then `a = b = k`, so `a + b = 2k`, absurd.
    rcases ha_hi with rfl | ha_hi <;> rcases hb_hi with rfl | hb_hi <;> omega
  · -- `a + b ∈ T ⊆ {3k+1,…,4k}`: one of `a, b` must equal `k`
    -- (otherwise `a + b ≥ 4k + 2 > 4k`), and the other is then a partner
    -- `x - k` with `x = a + b ∈ I₂ \ T`, contradicting `a + b ∈ T`.
    have hkab : a = (k : ℤ) ∨ b = (k : ℤ) := by
      rcases ha_hi with h | h
      · exact Or.inl h
      · rcases hb_hi with h' | h'
        · exact Or.inr h'
        · omega
    rcases hkab with rfl | hbeq
    · -- `a = k`: then `b ∈ {2k+1,…,3k}` is a partner of `a + b`.
      have hb_ge : 2 * (k : ℤ) + 1 ≤ b := by omega
      have hb_ne : b ≠ (k : ℤ) := by omega
      have hb_nT : b ∉ T := by
        intro hbT
        have h1 := (mem_blstI2.mp (hT hbT)).1
        omega
      rw [blstSet, Finset.mem_insert] at hb
      rcases hb with hbeqk | hb
      · exact hb_ne hbeqk
      rw [Finset.mem_union] at hb
      rcases hb with hbT | hbim
      · exact hb_nT hbT
      rw [Finset.mem_image] at hbim
      obtain ⟨y, hy, hyeq⟩ := hbim
      rw [Finset.mem_sdiff] at hy
      -- `y ∈ I₂ \ T` with `y - k = b`, so `y = a + b ∈ T` — contradiction.
      have hy_eq : y = (k : ℤ) + b := by
        have h : y - (k : ℤ) = b := hyeq
        omega
      exact hy.2 (hy_eq ▸ habT)
    · -- `b = k`: symmetric, `a` is a partner of `a + b`.
      subst hbeq
      have ha_ge : 2 * (k : ℤ) + 1 ≤ a := by omega
      have ha_ne : a ≠ (k : ℤ) := by omega
      have ha_nT : a ∉ T := by
        intro haT
        have h1 := (mem_blstI2.mp (hT haT)).1
        omega
      rw [blstSet, Finset.mem_insert] at ha
      rcases ha with haeqk | ha
      · exact ha_ne haeqk
      rw [Finset.mem_union] at ha
      rcases ha with haT | haim
      · exact ha_nT haT
      rw [Finset.mem_image] at haim
      obtain ⟨y, hy, hyeq⟩ := haim
      rw [Finset.mem_sdiff] at hy
      have hy_eq : y = a + (k : ℤ) := by
        have h : y - (k : ℤ) = a := hyeq
        omega
      exact hy.2 (hy_eq ▸ habT)

set_option linter.unusedVariables false in
/-- Recovery: any sum-free `M` containing `blstSet k T` has `M ∩ I₂ = T`.
(`hk` is part of the spec'd interface; the argument itself does not use it.) -/
theorem blstSet_inter_eq {k : ℕ} {T M : Finset ℤ} (hk : 1 ≤ k) (hT : T ⊆ blstI2 k)
    (hM : IsSumFree M) (hsub : blstSet k T ⊆ M) :
    M ∩ blstI2 k = T := by
  ext x
  simp only [Finset.mem_inter]
  constructor
  · rintro ⟨hxM, hxI⟩
    by_contra hxT
    -- `x ∈ I₂ \ T`, so `x - k` and `k` both lie in `blstSet k T ⊆ M`,
    -- while `(x - k) + k = x ∈ M` — contradicting sum-freeness of `M`.
    have hxsd : x ∈ blstI2 k \ T := Finset.mem_sdiff.mpr ⟨hxI, hxT⟩
    have hxk : x - (k : ℤ) ∈ blstSet k T := by
      rw [blstSet, Finset.mem_insert]
      right
      rw [Finset.mem_union]
      right
      exact Finset.mem_image.mpr ⟨x, hxsd, rfl⟩
    have hxkM : x - (k : ℤ) ∈ M := hsub hxk
    have hkM : (k : ℤ) ∈ M := hsub (Finset.mem_insert_self _ _)
    have hcon := hM (x - (k : ℤ)) hxkM (k : ℤ) hkM
    have heq : x - (k : ℤ) + (k : ℤ) = x := by omega
    rw [heq] at hcon
    exact hcon hxM
  · intro hxT
    refine ⟨?_, hT hxT⟩
    apply hsub
    rw [blstSet, Finset.mem_insert]
    right
    rw [Finset.mem_union]
    exact Or.inl hxT

end JSP000728
