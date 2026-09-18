import JSPProblem.Basic
import Mathlib.Order.Preorder.Finite

/-!
# JSP-000728 — extending sum-free sets to maximal ones

Every sum-free subset of `interval n = {1, …, n}` can be extended to an
inclusion-maximal sum-free subset.  This is the finitary analogue of Zorn's
lemma: the finite set of admissible supersets has a maximal element
(`Set.Finite.exists_le_maximal`).

* `exists_maxSumFree_superset` : existence of a maximal sum-free extension.
* `maxExt` : a (noncomputable) choice of such an extension.
* `maxExt_spec`, `maxExt_mem` : the extension is indeed maximal sum-free,
  hence lies in `maxSumFreeSets n`.
-/

namespace JSP000728

/-- Every sum-free `s ⊆ interval n` is contained in an inclusion-maximal
sum-free subset of `interval n`. -/
theorem exists_maxSumFree_superset {n : ℕ} {s : Finset ℤ}
    (hs : s ⊆ interval n) (hsf : IsSumFree s) :
    ∃ M : Finset ℤ, s ⊆ M ∧ IsMaxSumFree n M := by
  -- The finite set of admissible supersets of `s`.
  let P : Set (Finset ℤ) := {t | s ⊆ t ∧ t ⊆ interval n ∧ IsSumFree t}
  have hPfin : P.Finite := by
    refine Set.Finite.subset (interval n).powerset.finite_toSet ?_
    intro t ht
    obtain ⟨-, htn, -⟩ := ht
    exact Finset.mem_coe.mpr (Finset.mem_powerset.mpr htn)
  obtain ⟨M, hsM, hM⟩ :=
    hPfin.exists_le_maximal (show s ∈ P from ⟨le_refl s, hs, hsf⟩)
  obtain ⟨hssM, hMn, hMsf⟩ := hM.prop
  refine ⟨M, hsM, isMaxSumFree_iff_isMaximalSumFree.mpr ⟨hMn, hMsf, ?_⟩⟩
  intro t ht htf hMt
  exact hM.le_of_ge (show t ∈ P from ⟨hssM.trans hMt, ht, htf⟩) hMt

/-- A (noncomputable) choice of an inclusion-maximal sum-free superset of `s`
inside `interval n`; returns `s` itself when `s` is not a sum-free subset of
`interval n`. -/
noncomputable def maxExt (n : ℕ) (s : Finset ℤ) : Finset ℤ :=
  if h : s ⊆ interval n ∧ IsSumFree s then
    Classical.choose (exists_maxSumFree_superset h.1 h.2)
  else s

/-- `maxExt n s` extends `s` and is an inclusion-maximal sum-free subset of
`interval n`, whenever `s` is sum-free and contained in `interval n`. -/
theorem maxExt_spec {n : ℕ} {s : Finset ℤ}
    (hs : s ⊆ interval n) (hsf : IsSumFree s) :
    s ⊆ maxExt n s ∧ IsMaxSumFree n (maxExt n s) := by
  unfold maxExt
  rw [dite_eq_left ⟨hs, hsf⟩]
  exact Classical.choose_spec (exists_maxSumFree_superset hs hsf)

/-- `maxExt n s` is one of the maximal sum-free subsets enumerated by
`maxSumFreeSets n`. -/
theorem maxExt_mem {n : ℕ} {s : Finset ℤ}
    (hs : s ⊆ interval n) (hsf : IsSumFree s) :
    maxExt n s ∈ maxSumFreeSets n :=
  mem_maxSumFreeSets.mpr (maxExt_spec hs hsf).2

end JSP000728
