import JSPProblem.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Int.Interval

/-!
# JSP-000728 — the "translate by the minimum" bound for sum-free sets

If `s ⊆ {1,…,n}` is sum-free and `m ∈ s` is its minimum, then the translate
by `m` of the "low" part `s ∩ [1, n−m]` is disjoint from `s` while still lying
inside `{1,…,n}`.  Hence `|s| + |s ∩ [1, n−m]| ≤ n`, and since the
complementary "high" part of `s` lives in `(n−m, n]`, an interval with only
`m` elements, we obtain `2·|s| ≤ n + m`.

This structural estimate underlies the Balogh–Liu–Sharifzadeh–Treglown
container method: a sum-free set with a small minimum is itself small, so
only sets with a large minimum need to be counted by container arguments.
-/

namespace JSP000728

/-- Translating a sum-free set by one of its own elements yields a disjoint
set: `x + m = y` with `x, y, m ∈ s` would be a Schur triple inside `s`. -/
theorem disjoint_image_add_min_of_isSumFree {s : Finset ℤ} (hsf : IsSumFree s)
    {m : ℤ} (hm : m ∈ s) : Disjoint s (s.image (· + m)) := by
  rw [Finset.disjoint_left]
  rintro x hxs hxim
  rcases Finset.mem_image.mp hxim with ⟨y, hy, hyx⟩
  rw [← hyx] at hxs
  exact hsf y hy m hm hxs

/-- **Translate-by-the-minimum bound.**  A sum-free `s ⊆ {1,…,n}` containing
`m` with `m ≤ x` for all `x ∈ s` (i.e. `m` is the minimum of `s`) satisfies
`2·|s| ≤ n + m`.

Proof: split `s` into the low part `t = s ∩ [1, n−m]` and the high part.
`t + m ⊆ {1,…,n}` is disjoint from `s` (Schur triples are forbidden), so
`|s| + |t| ≤ n`.  The high part lies in `(n−m, n]`, an interval of `m`
integers, giving `|s| − |t| ≤ m`.  (The minimality hypothesis `hmin` is in
fact not needed: the argument works for any `m ∈ s`.  It is kept so that the
statement matches the intended application to `s.min'`.) -/
theorem two_mul_card_le_of_min {n : ℕ} {s : Finset ℤ} (hsub : s ⊆ interval n)
    (hsf : IsSumFree s) {m : ℤ} (hm : m ∈ s) (_hmin : ∀ x ∈ s, m ≤ x) :
    2 * s.card ≤ n + m.toNat := by
  classical
  have hmI : m ∈ Finset.Icc (1 : ℤ) (n : ℤ) := hsub hm
  rw [Finset.mem_Icc] at hmI
  obtain ⟨hm1, hmn⟩ := hmI
  -- Split `s` into the low part `t` and the high part.
  set t : Finset ℤ := s.filter (· ≤ (n : ℤ) - m) with ht
  -- The translate `t + m` still lies inside `{1,…,n}`.
  have htsub : t.image (· + m) ⊆ interval n := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨x, hxt, rfl⟩
    obtain ⟨hxs, hxle⟩ := Finset.mem_filter.mp hxt
    have hxI : x ∈ Finset.Icc (1 : ℤ) (n : ℤ) := hsub hxs
    rw [Finset.mem_Icc] at hxI
    show x + m ∈ interval n
    rw [interval, Finset.mem_Icc]
    exact ⟨by omega, by omega⟩
  -- `s` and `t + m` are disjoint subsets of `{1,…,n}`.
  have hdisj : Disjoint s (t.image (· + m)) :=
    (disjoint_image_add_min_of_isSumFree hsf hm).mono_right
      (Finset.image_subset_image (Finset.filter_subset _ _))
  have hcardT : (t.image (· + m)).card = t.card :=
    Finset.card_image_of_injective t (add_left_injective m)
  have hlow : s.card + t.card ≤ n := by
    have hunion : s ∪ t.image (· + m) ⊆ interval n :=
      Finset.union_subset hsub htsub
    calc s.card + t.card
        = s.card + (t.image (· + m)).card := by rw [hcardT]
      _ = (s ∪ t.image (· + m)).card := (Finset.card_union_of_disjoint hdisj).symm
      _ ≤ (interval n).card := Finset.card_le_card hunion
      _ = n := by simp [interval, Int.card_Icc]
  -- The high part of `s` sits inside `(n − m, n]`, which has `m` elements.
  have hhigh : (s.filter fun x => ¬ x ≤ (n : ℤ) - m).card ≤ m.toNat := by
    have hss : s.filter (fun x => ¬ x ≤ (n : ℤ) - m) ⊆
        Finset.Icc ((n : ℤ) - m + 1) (n : ℤ) := by
      intro x hx
      obtain ⟨hxs, hxgt⟩ := Finset.mem_filter.mp hx
      have hxI : x ∈ Finset.Icc (1 : ℤ) (n : ℤ) := hsub hxs
      rw [Finset.mem_Icc] at hxI ⊢
      exact ⟨by omega, hxI.2⟩
    calc (s.filter fun x => ¬ x ≤ (n : ℤ) - m).card
        ≤ (Finset.Icc ((n : ℤ) - m + 1) (n : ℤ)).card := Finset.card_le_card hss
      _ = m.toNat := by
          rw [Int.card_Icc]
          congr 1
          omega
  -- `s` is the disjoint union of its low and high parts.
  have hsplit : t.card + (s.filter fun x => ¬ x ≤ (n : ℤ) - m).card = s.card :=
    Finset.card_filter_add_card_filter_not _
  omega

/-- `|s| ≤ (n + m)/2`, the division form of `two_mul_card_le_of_min`. -/
theorem card_le_n_add_min_div_two {n : ℕ} {s : Finset ℤ} (hsub : s ⊆ interval n)
    (hsf : IsSumFree s) {m : ℤ} (hm : m ∈ s) (hmin : ∀ x ∈ s, m ≤ x) :
    s.card ≤ (n + m.toNat) / 2 := by
  have h := two_mul_card_le_of_min hsub hsf hm hmin
  omega

/-- The translate-by-the-minimum bound specialised to the actual minimum
`M.min'` of an inclusion-maximal sum-free set `M ⊆ {1,…,n}`. -/
theorem two_mul_card_le_of_isMaxSumFree {n : ℕ} {M : Finset ℤ}
    (hM : M ∈ maxSumFreeSets n) (hne : M.Nonempty) :
    2 * M.card ≤ n + (M.min' hne).toNat := by
  obtain ⟨hsub, hsf, -⟩ := mem_maxSumFreeSets.mp hM
  exact two_mul_card_le_of_min hsub hsf (Finset.min'_mem M hne)
    (fun x hx => Finset.min'_le M x hx)

/-- `|M| ≤ (n + min M)/2` for a nonempty maximal sum-free `M ⊆ {1,…,n}`. -/
theorem card_le_div_two_of_isMaxSumFree {n : ℕ} {M : Finset ℤ}
    (hM : M ∈ maxSumFreeSets n) (hne : M.Nonempty) :
    M.card ≤ (n + (M.min' hne).toNat) / 2 := by
  have h := two_mul_card_le_of_isMaxSumFree hM hne
  omega

end JSP000728
