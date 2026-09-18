import Mathlib.Data.Int.Interval
import Mathlib.Data.Finset.Powerset

/-!
# JSP-000728 — basic definitions

How many inclusion-maximal sum-free subsets does a finite integer interval have?

We work with the interval `{1, …, n}` realised as a `Finset ℤ`.
* `IsSumFree s` : `x + y ∉ s` for all `x, y ∈ s` (with `x = y` permitted).
* `IsMaxSumFree n s` : decidable, single-obstruction formulation of
  inclusion-maximality inside `{1, …, n}`.
* `IsMaximalSumFree n s` : order-theoretic formulation (equivalent, see
  `isMaxSumFree_iff_isMaximalSumFree`).
* `maxSumFreeCount n` : the number of inclusion-maximal sum-free subsets of
  `{1, …, n}` — the quantity the problem asks about.

The sharp answer is `maxSumFreeCount n = 2 ^ ((1/4 + o(1)) * n)`
(Balogh–Liu–Sharifzadeh–Treglown, JEMS 2018); this library currently
establishes the definitions and elementary lower bounds.
-/

namespace JSP000728

/-- The finite integer interval `{1, …, n}` realised as a `Finset ℤ`. -/
def interval (n : ℕ) : Finset ℤ := Finset.Icc 1 (n : ℤ)

/-- A finset `s` of integers is *sum-free* when `x + y ∉ s` for all `x, y ∈ s`
(`x` and `y` need not be distinct). -/
def IsSumFree (s : Finset ℤ) : Prop := ∀ x ∈ s, ∀ y ∈ s, x + y ∉ s

instance decidableIsSumFree (s : Finset ℤ) : Decidable (IsSumFree s) := by
  unfold IsSumFree; infer_instance

/-- `s` is an *inclusion-maximal sum-free subset* of `interval n`: it is
contained in `{1, …, n}`, sum-free, and adjoining any further element of
`{1, …, n}` destroys sum-freeness.  Decidable formulation. -/
def IsMaxSumFree (n : ℕ) (s : Finset ℤ) : Prop :=
  s ⊆ interval n ∧ IsSumFree s ∧
    ∀ x ∈ interval n, x ∉ s → ¬ IsSumFree (insert x s)

instance decidableIsMaxSumFree (n : ℕ) (s : Finset ℤ) :
    Decidable (IsMaxSumFree n s) := by
  unfold IsMaxSumFree; infer_instance

theorem IsSumFree.mono {s t : Finset ℤ} (hs : IsSumFree s) (hst : t ⊆ s) :
    IsSumFree t :=
  fun x hx y hy hxy => hs x (hst hx) y (hst hy) (hst hxy)

/-- Order-theoretic inclusion-maximality among sum-free subsets of
`interval n`. -/
def IsMaximalSumFree (n : ℕ) (s : Finset ℤ) : Prop :=
  s ⊆ interval n ∧ IsSumFree s ∧
    ∀ t : Finset ℤ, t ⊆ interval n → IsSumFree t → s ⊆ t → t ⊆ s

/-- The two formulations of inclusion-maximality agree. -/
theorem isMaxSumFree_iff_isMaximalSumFree {n : ℕ} {s : Finset ℤ} :
    IsMaxSumFree n s ↔ IsMaximalSumFree n s := by
  constructor
  · rintro ⟨hsub, hsf, hmax⟩
    refine ⟨hsub, hsf, fun t ht htf hst x hx => ?_⟩
    by_contra hxs
    have hins : insert x s ⊆ t := Finset.insert_subset hx hst
    exact hmax x (ht hx) hxs (htf.mono hins)
  · rintro ⟨hsub, hsf, hmax⟩
    refine ⟨hsub, hsf, fun x hxn hxs hsf' => ?_⟩
    have hins : insert x s ⊆ interval n := Finset.insert_subset hxn hsub
    have hxss := hmax (insert x s) hins hsf' (Finset.subset_insert x s)
    exact hxs (hxss (Finset.mem_insert_self x s))

/-- The finset of all inclusion-maximal sum-free subsets of `{1, …, n}`. -/
def maxSumFreeSets (n : ℕ) : Finset (Finset ℤ) :=
  (interval n).powerset.filter (IsMaxSumFree n)

/-- `f n`: the number of inclusion-maximal sum-free subsets of `{1, …, n}` —
the quantity JSP-000728 asks about. -/
def maxSumFreeCount (n : ℕ) : ℕ := (maxSumFreeSets n).card

theorem mem_maxSumFreeSets {n : ℕ} {s : Finset ℤ} :
    s ∈ maxSumFreeSets n ↔ IsMaxSumFree n s := by
  simp only [maxSumFreeSets, Finset.mem_filter, Finset.mem_powerset]
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨h.1, h⟩⟩

end JSP000728
