import JSPProblem.Basic
import JSPProblem.Odds
import Mathlib.Data.Finset.Max
import Mathlib.Data.Int.Interval

/-!
# JSP-000728 — the maximum size of a sum-free subset of `{1,…,n}`

The classical fact: every sum-free subset of `{1, …, n}` has at most
`⌈n/2⌉ = (n + 1) / 2` elements, and the odd numbers attain this bound.

* `two_mul_card_le_of_isSumFree` : `2 * s.card ≤ n + 1`, proved by reflecting
  `s \ {max s}` about `max s`: the sets `t` and `M - t` are disjoint subsets of
  `{1, …, M - 1}` (a common element would give a Schur triple `x + y = M`).
* `card_le_of_isSumFree` : the division form `s.card ≤ (n + 1) / 2`.
* `card_odds` : `(odds n).card = (n + 1) / 2` via the bijection `k ↦ 2k - 1`
  with `{1, …, (n + 1) / 2}`.
* `isMaxSumFree_max_card` : the odds attain the bound.
* `card_le_of_isMaxSumFree` : every member of `maxSumFreeSets n` has at most
  `(n + 1) / 2` elements.
-/

namespace JSP000728

/-- **Reflection about the maximum.** If `s ⊆ {1,…,n}` is sum-free, then
`2 * s.card ≤ n + 1`.

Write `M = max s` and `t = s \ {M}`.  Both `t` and its reflection
`x ↦ M - x` lie in `{1, …, M - 1}`, and they are disjoint: a common element
`y = M - x` with `x, y ∈ t ⊆ s` would give `x + y = M ∈ s`, contradicting
sum-freeness.  Hence `2 * (s.card - 1) = 2 * t.card ≤ M - 1 ≤ n - 1`. -/
theorem two_mul_card_le_of_isSumFree {n : ℕ} {s : Finset ℤ}
    (hsub : s ⊆ interval n) (hsf : IsSumFree s) :
    2 * s.card ≤ n + 1 := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · simp
  obtain ⟨M, hMmem, hMle⟩ : ∃ M ∈ s, ∀ x ∈ s, x ≤ M :=
    ⟨s.max' hne, s.max'_mem hne, fun x hx => s.le_max' x hx⟩
  have hMI : 1 ≤ M ∧ M ≤ (n : ℤ) := Finset.mem_Icc.mp (hsub hMmem)
  have hpos : 0 < s.card := Finset.card_pos.mpr hne
  have hcard_erase : (s.erase M).card = s.card - 1 :=
    Finset.card_erase_of_mem hMmem
  -- Every element of `s.erase M` lies in `{1, …, M - 1}`.
  have hsub1 : s.erase M ⊆ Finset.Icc 1 (M - 1) := by
    intro x hx
    obtain ⟨hxne, hxs⟩ := Finset.mem_erase.mp hx
    have hxI := Finset.mem_Icc.mp (hsub hxs)
    have hxlt : x < M := lt_of_le_of_ne (hMle x hxs) hxne
    exact Finset.mem_Icc.mpr ⟨hxI.1, by omega⟩
  -- So does the reflection `x ↦ M - x`.
  have hsub2 : (s.erase M).image (fun x => M - x) ⊆ Finset.Icc 1 (M - 1) := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨hxne, hxs⟩ := Finset.mem_erase.mp hx
    have hxI := Finset.mem_Icc.mp (hsub hxs)
    have hxlt : x < M := lt_of_le_of_ne (hMle x hxs) hxne
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  -- The two sets are disjoint: `y = M - x` with `x, y ∈ s` gives
  -- `x + y = M ∈ s`, a Schur triple.
  have hdisj : Disjoint (s.erase M) ((s.erase M).image (fun x => M - x)) := by
    rw [Finset.disjoint_left]
    intro y hy huy
    obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp huy
    obtain ⟨hxne, hxs⟩ := Finset.mem_erase.mp hx
    obtain ⟨hyne, hys⟩ := Finset.mem_erase.mp hy
    have hsum : x + y ∈ s := by
      have h : x + y = M := by omega
      rw [h]
      exact hMmem
    exact hsf x hxs y hys hsum
  -- The reflection is injective, so the image has the same cardinality.
  have himg : ((s.erase M).image (fun x => M - x)).card = (s.erase M).card :=
    Finset.card_image_of_injOn
      (fun a _ b _ h => by have h2 : M - a = M - b := h; omega)
  have hunion : s.erase M ∪ (s.erase M).image (fun x => M - x) ⊆
      Finset.Icc 1 (M - 1) :=
    Finset.union_subset hsub1 hsub2
  have hcard : 2 * (s.erase M).card ≤ (Finset.Icc (1 : ℤ) (M - 1)).card := by
    have h := Finset.card_le_card hunion
    rw [Finset.card_union_of_disjoint hdisj, himg] at h
    omega
  have hIcc : (Finset.Icc (1 : ℤ) (M - 1)).card = (M - 1).toNat := by
    rw [Int.card_Icc]
    omega
  omega

/-- Every sum-free subset of `{1,…,n}` has at most `⌈n/2⌉ = (n+1)/2`
elements. -/
theorem card_le_of_isSumFree {n : ℕ} {s : Finset ℤ}
    (hsub : s ⊆ interval n) (hsf : IsSumFree s) :
    s.card ≤ (n + 1) / 2 := by
  have h := two_mul_card_le_of_isSumFree hsub hsf
  omega

/-- The map `k ↦ 2k - 1` is a bijection between `{1, …, (n+1)/2}` and the odd
numbers of `{1, …, n}`, so `(odds n).card = (n + 1) / 2`. -/
theorem card_odds (n : ℕ) : (odds n).card = (n + 1) / 2 := by
  have himg : odds n =
      (Finset.Icc 1 (((n + 1) / 2 : ℕ) : ℤ)).image (fun k => 2 * k - 1) := by
    ext x
    constructor
    · intro hx
      obtain ⟨hxI, hodd⟩ := mem_odds.mp hx
      obtain ⟨h1, hn⟩ := Finset.mem_Icc.mp hxI
      refine Finset.mem_image.mpr
        ⟨(x + 1) / 2, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
      show 2 * ((x + 1) / 2) - 1 = x
      omega
    · intro hx
      obtain ⟨k, hk, hke⟩ := Finset.mem_image.mp hx
      obtain ⟨hk1, hkm⟩ := Finset.mem_Icc.mp hk
      have hke2 : 2 * k - 1 = x := hke
      exact mem_odds.mpr
        ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
  have hinj : Set.InjOn (fun k : ℤ => 2 * k - 1)
      ↑(Finset.Icc 1 (((n + 1) / 2 : ℕ) : ℤ)) :=
    fun a _ b _ h => by have h2 : 2 * a - 1 = 2 * b - 1 := h; omega
  rw [himg, Finset.card_image_of_injOn hinj, Int.card_Icc]
  omega

/-- The odd numbers are a sum-free subset of `{1,…,n}`. -/
theorem isSumFree_odds (n : ℕ) : IsSumFree (odds n) :=
  (odds_isMaxSumFree n).2.1

/-- The odd numbers are contained in `{1,…,n}`. -/
theorem odds_subset_interval (n : ℕ) : odds n ⊆ interval n :=
  (odds_isMaxSumFree n).1

/-- The bound `(n + 1) / 2` is attained: the odd numbers form a sum-free
(indeed inclusion-maximal sum-free) subset of `{1,…,n}` with exactly
`(n + 1) / 2` elements. -/
theorem isMaxSumFree_max_card (n : ℕ) :
    odds n ⊆ interval n ∧ IsSumFree (odds n) ∧
      (odds n).card = (n + 1) / 2 :=
  ⟨odds_subset_interval n, isSumFree_odds n, card_odds n⟩

/-- Every inclusion-maximal sum-free subset of `{1,…,n}` has at most
`(n + 1) / 2` elements. -/
theorem card_le_of_isMaxSumFree {n : ℕ} {M : Finset ℤ}
    (hM : M ∈ maxSumFreeSets n) : M.card ≤ (n + 1) / 2 :=
  card_le_of_isSumFree (mem_maxSumFreeSets.mp hM).1
    (mem_maxSumFreeSets.mp hM).2.1

end JSP000728
