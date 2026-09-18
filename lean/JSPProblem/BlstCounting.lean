import JSPProblem.Basic
import JSPProblem.Extend
import JSPProblem.BlstFamily
import JSPProblem.UpperHalf
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# JSP-000728 — the Cameron–Erdős / BLST lower bound `f(n) ≥ 2^{⌊n/4⌋}`

Balogh–Liu–Sharifzadeh–Treglown (Proc. AMS 2015, arXiv:1409.5661) record the
Cameron–Erdős lower bound `f_max(n) ≥ 2^{⌊n/4⌋}` for the number of
inclusion-maximal sum-free subsets of `{1,…,n}`.

We formalize the cleaner of their two constructions.  For `k = ⌊n/4⌋ ≥ 1` and
`I₂ = {3k+1,…,4k}` (so `|I₂| = k`), every `T ⊆ I₂` yields the sum-free set
`blstSet k T = {k} ∪ T ∪ {x − k : x ∈ I₂ \ T}`.

Key observation (the paper's trick): we do **not** need `blstSet k T` itself to
be maximal.  Any maximal sum-free `M ⊇ blstSet k T` satisfies `M ∩ I₂ = T`
(`blstSet_inter_eq`), so the map `T ↦ M` is injective on `𝒫(I₂)`, and
`f(n) ≥ |𝒫(I₂)| = 2^{⌊n/4⌋}`.

Together with the trivial bound `f(n) ≤ 2^n` this gives the sharp exponent
`1/4` for the lower bound: `log₂ f(n) ≥ n/4 − 1` for all `n ≥ 4`.
-/

namespace JSP000728

private theorem four_mul_div_le (n : ℕ) : 4 * (n / 4) ≤ n := by
  simpa [Nat.mul_comm] using Nat.div_mul_le_self n 4

private theorem one_le_div_four {n : ℕ} (hn : 4 ≤ n) : 1 ≤ n / 4 := by
  omega

/-- The map `T ↦ maxExt n (blstSet k T)` sends `𝒫(I₂)` into
`maxSumFreeSets n` and is injective there, because any maximal extension `M`
satisfies `M ∩ I₂ = T`. -/
theorem maxSumFreeCount_ge_card_powerset_blstI2 {n k : ℕ} (hk : 1 ≤ k)
    (hkn : 4 * k ≤ n) :
    2 ^ k ≤ maxSumFreeCount n := by
  classical
  have key : ∀ T : Finset ℤ, T ⊆ blstI2 k →
      maxExt n (blstSet k T) ∩ blstI2 k = T := by
    intro T hT
    exact blstSet_inter_eq hk hT
      (maxExt_spec (blstSet_subset_interval hk hkn hT)
        (isSumFree_blstSet hk hT)).2.2.1
      (maxExt_spec (blstSet_subset_interval hk hkn hT)
        (isSumFree_blstSet hk hT)).1
  have hinj : Set.InjOn (fun T => maxExt n (blstSet k T))
      ((blstI2 k).powerset : Set (Finset ℤ)) := by
    intro T₁ hT₁ T₂ hT₂ h
    simp only [Finset.mem_coe, Finset.mem_powerset] at hT₁ hT₂
    have h' : maxExt n (blstSet k T₁) = maxExt n (blstSet k T₂) := h
    rw [← key T₁ hT₁, ← key T₂ hT₂, h']
  have himg : (blstI2 k).powerset.image (fun T => maxExt n (blstSet k T)) ⊆
      maxSumFreeSets n := by
    intro M hM
    rw [Finset.mem_image] at hM
    obtain ⟨T, hT, rfl⟩ := hM
    rw [Finset.mem_powerset] at hT
    exact maxExt_mem (blstSet_subset_interval hk hkn hT)
      (isSumFree_blstSet hk hT)
  calc 2 ^ k = ((blstI2 k).powerset.image
          (fun T => maxExt n (blstSet k T))).card := by
        rw [Finset.card_image_of_injOn hinj, Finset.card_powerset, card_blstI2]
    _ ≤ maxSumFreeCount n := Finset.card_le_card himg

/-- **Cameron–Erdős / BLST lower bound**: every interval `{1,…,n}` with
`n ≥ 4` has at least `2^{⌊n/4⌋}` inclusion-maximal sum-free subsets.  The
exponent constant `1/4` is sharp (BLST18 proves the matching upper bound). -/
theorem two_pow_quarter_le_maxSumFreeCount {n : ℕ} (hn : 4 ≤ n) :
    2 ^ (n / 4) ≤ maxSumFreeCount n :=
  maxSumFreeCount_ge_card_powerset_blstI2 (one_le_div_four hn)
    (four_mul_div_le n)

/-- The lower bound in fact holds for every `n`: for `n < 4` the right side
is `2^0 = 1`, and `f n ≥ 1` since `upperHalf n` is maximal sum-free. -/
theorem two_pow_quarter_le_maxSumFreeCount' (n : ℕ) :
    2 ^ (n / 4) ≤ maxSumFreeCount n := by
  by_cases hn : 4 ≤ n
  · exact two_pow_quarter_le_maxSumFreeCount hn
  · have h0 : n / 4 = 0 := Nat.div_eq_of_lt (Nat.lt_of_not_le hn)
    rw [h0, pow_zero]
    exact Finset.card_pos.mpr
      ⟨upperHalf n, mem_maxSumFreeSets.mpr (upperHalf_isMaxSumFree n)⟩

/-- `log₂` form of the lower bound: `log₂ f(n) ≥ ⌊n/4⌋ ≥ n/4 − 1`. -/
theorem logb_maxSumFreeCount_ge {n : ℕ} (hn : 4 ≤ n) :
    ((n / 4 : ℕ) : ℝ) ≤ Real.logb 2 (maxSumFreeCount n : ℝ) := by
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (n / 4 : ℕ) := by positivity
  have hle : (2 : ℝ) ^ (n / 4 : ℕ) ≤ (maxSumFreeCount n : ℝ) := by
    exact_mod_cast two_pow_quarter_le_maxSumFreeCount hn
  have h := Real.logb_le_logb_of_le (b := 2) (x := (2 : ℝ) ^ (n / 4 : ℕ))
    (y := maxSumFreeCount n) (by norm_num) hpos hle
  rwa [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one] at h

/-- In particular `log₂ f(n) / n ≥ 1/4 − 1/n` for `n ≥ 4`: the lower bound
matches the sharp constant `1/4` of BLST18. -/
theorem quarter_sub_one_le_logb_maxSumFreeCount {n : ℕ} (hn : 4 ≤ n) :
    (n : ℝ) / 4 - 1 ≤ Real.logb 2 (maxSumFreeCount n : ℝ) := by
  have h := logb_maxSumFreeCount_ge hn
  have hfloor : (n : ℝ) / 4 - 1 ≤ ((n / 4 : ℕ) : ℝ) := by
    have hmod : (n : ℝ) = 4 * ((n / 4 : ℕ) : ℝ) + ((n % 4 : ℕ) : ℝ) := by
      have := Nat.div_add_mod n 4
      have hc : (n : ℝ) = 4 * ((n / 4 : ℕ) : ℝ) + ((n % 4 : ℕ) : ℝ) := by
        exact_mod_cast this.symm
      exact hc
    have hlt : ((n % 4 : ℕ) : ℝ) < 4 := by
      exact_mod_cast Nat.mod_lt n (by norm_num : 0 < 4)
    linarith
  linarith

end JSP000728
