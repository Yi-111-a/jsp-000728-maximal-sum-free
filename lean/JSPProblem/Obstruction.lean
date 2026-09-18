import JSPProblem.Basic

/-!
# JSP-000728 — the maximality obstruction

If `s` is an inclusion-maximal sum-free subset of `{1, …, n}` and
`x ∈ {1, …, n}` does not lie in `s`, then `insert x s` fails to be sum-free,
which forces `x` to participate in a sum: either `x` is itself a sum
`a + b` of two elements of `s`, or `x` sums with an element of `s` into `s`
(`a + x ∈ s`, `x + a ∈ s`), or `x + x ∈ s`.

This "covering" statement is the basic engine behind every upper-bound
argument for the number of maximal sum-free sets.

* `IsSumFree.insert_iff` : sum-freeness of `insert x s` decomposes into the
  four possible obstruction types (for `x > 0` and `s` positive).
* `IsMaxSumFree.exists_obstruction` : every `x ∈ interval n ∖ s` has an
  obstruction.
* `IsMaxSumFree.mem_or_obstruction` : every `x ∈ interval n` is either in `s`
  or obstructed.
-/

namespace JSP000728

/-- Every member of `interval n` is at least `1`. -/
theorem interval_one_le {n : ℕ} {x : ℤ} (hx : x ∈ interval n) : 1 ≤ x :=
  (Finset.mem_Icc.mp hx).1

/-- Every member of `interval n` is positive. -/
theorem interval_pos {n : ℕ} {x : ℤ} (hx : x ∈ interval n) : 0 < x :=
  zero_lt_one.trans_le (interval_one_le hx)

/-- Every member of `interval n` is at most `n`. -/
theorem interval_le {n : ℕ} {x : ℤ} (hx : x ∈ interval n) : x ≤ (n : ℤ) :=
  (Finset.mem_Icc.mp hx).2

/-- Members of an inclusion-maximal sum-free set are positive. -/
theorem IsMaxSumFree.pos_of_mem {n : ℕ} {s : Finset ℤ} (h : IsMaxSumFree n s)
    {a : ℤ} (ha : a ∈ s) : 0 < a :=
  interval_pos (h.1 ha)

/-- Members of an inclusion-maximal sum-free set are at most `n`. -/
theorem IsMaxSumFree.le_of_mem {n : ℕ} {s : Finset ℤ} (h : IsMaxSumFree n s)
    {a : ℤ} (ha : a ∈ s) : a ≤ (n : ℤ) :=
  interval_le (h.1 ha)

/-- Adjoining a positive element `x` to a sum-free set `s` of positive
elements stays sum-free exactly when none of the four obstruction types
occurs:

1. `x` is a sum `a + b` of two elements of `s`;
2. `a + x ∈ s` for some `a ∈ s`;
3. `x + a ∈ s` for some `a ∈ s`;
4. `x + x ∈ s`.

Positivity rules out the degenerate hits `a + x = x` and `x + x = x`. -/
theorem IsSumFree.insert_iff {s : Finset ℤ} {x : ℤ} (hs : IsSumFree s)
    (hx : 0 < x) (hpos : ∀ a ∈ s, 0 < a) :
    IsSumFree (insert x s) ↔
      IsSumFree s ∧
      (∀ a ∈ s, ∀ b ∈ s, a + b ≠ x) ∧
      (∀ a ∈ s, a + x ∉ s) ∧
      (∀ a ∈ s, x + a ∉ s) ∧
      (x + x ∉ s) := by
  constructor
  · intro h
    refine ⟨hs, ?_, ?_, ?_, ?_⟩
    · -- If `a + b = x` then `a + b ∈ insert x s`, contradicting `h`.
      intro a ha b hb hab
      exact h a (Finset.mem_insert_of_mem ha) b (Finset.mem_insert_of_mem hb)
        (hab ▸ Finset.mem_insert_self x s)
    · intro a ha hax
      exact h a (Finset.mem_insert_of_mem ha) x (Finset.mem_insert_self x s)
        (Finset.mem_insert_of_mem hax)
    · intro a ha hxa
      exact h x (Finset.mem_insert_self x s) a (Finset.mem_insert_of_mem ha)
        (Finset.mem_insert_of_mem hxa)
    · intro hxx
      exact h x (Finset.mem_insert_self x s) x (Finset.mem_insert_self x s)
        (Finset.mem_insert_of_mem hxx)
  · rintro ⟨_, h2, h3, h4, h5⟩ u hu v hv huv
    rw [Finset.mem_insert] at hu hv huv
    rcases hu with rfl | hu <;> rcases hv with rfl | hv <;>
      rcases huv with huv | huv
    · -- `x + x = x` forces `x = 0`.
      omega
    · exact h5 huv
    · -- `x + v = x` forces `v = 0`, contradicting `0 < v`.
      have := hpos _ hv
      omega
    · exact h4 _ hv huv
    · -- `u + x = x` forces `u = 0`, contradicting `0 < u`.
      have := hpos _ hu
      omega
    · exact h3 _ hu huv
    · exact h2 _ hu _ hv huv
    · exact hs u hu v hv huv

/-- **Maximality obstruction**: if `s` is an inclusion-maximal sum-free
subset of `{1, …, n}` and `x ∈ {1, …, n}` lies outside `s`, then `x` is
obstructed in one of four ways. -/
theorem IsMaxSumFree.exists_obstruction {n : ℕ} {s : Finset ℤ}
    (h : IsMaxSumFree n s) {x : ℤ} (hxn : x ∈ interval n) (hxs : x ∉ s) :
    (∃ a ∈ s, ∃ b ∈ s, a + b = x) ∨ (∃ a ∈ s, a + x ∈ s) ∨
      (∃ a ∈ s, x + a ∈ s) ∨ (x + x ∈ s) := by
  have hnot : ¬ IsSumFree (insert x s) := h.2.2 x hxn hxs
  have hiff := h.2.1.insert_iff (interval_pos hxn) (fun a ha => h.pos_of_mem ha)
  -- The contrapositive of `insert_iff`: the conjunction of non-obstructions
  -- cannot hold.
  have hnot' : ¬ ((∀ a ∈ s, ∀ b ∈ s, a + b ≠ x) ∧ (∀ a ∈ s, a + x ∉ s) ∧
      (∀ a ∈ s, x + a ∉ s) ∧ (x + x ∉ s)) :=
    fun hb => hnot (hiff.mpr ⟨h.2.1, hb⟩)
  by_cases h2 : ∃ a ∈ s, ∃ b ∈ s, a + b = x
  · exact Or.inl h2
  by_cases h3 : ∃ a ∈ s, a + x ∈ s
  · exact Or.inr (Or.inl h3)
  by_cases h4 : ∃ a ∈ s, x + a ∈ s
  · exact Or.inr (Or.inr (Or.inl h4))
  refine Or.inr (Or.inr (Or.inr ?_))
  by_contra hxx
  exact hnot' ⟨fun a ha b hb hab => h2 ⟨a, ha, b, hb, hab⟩,
    fun a ha hax => h3 ⟨a, ha, hax⟩,
    fun a ha hxa => h4 ⟨a, ha, hxa⟩,
    hxx⟩

/-- **Covering form** of the maximality obstruction: every `x ∈ {1, …, n}`
either lies in `s` or is obstructed. -/
theorem IsMaxSumFree.mem_or_obstruction {n : ℕ} {s : Finset ℤ}
    (h : IsMaxSumFree n s) {x : ℤ} (hxn : x ∈ interval n) :
    x ∈ s ∨ (∃ a ∈ s, ∃ b ∈ s, a + b = x) ∨ (∃ a ∈ s, a + x ∈ s) ∨
      (∃ a ∈ s, x + a ∈ s) ∨ (x + x ∈ s) := by
  by_cases hxs : x ∈ s
  · exact Or.inl hxs
  · exact Or.inr (h.exists_obstruction hxn hxs)

/-- A sum of two elements of `s` that lands inside `{1, …, n}` is blocked:
it cannot itself belong to `s`. -/
theorem IsMaxSumFree.sum_not_mem {n : ℕ} {s : Finset ℤ} (h : IsMaxSumFree n s)
    {a b : ℤ} (ha : a ∈ s) (hb : b ∈ s) (hab : a + b ∈ interval n) :
    a + b ∉ s :=
  h.2.1 a ha b hb

/-- The double of an element of `s` cannot belong to `s` (when it lands in
the interval). -/
theorem IsMaxSumFree.two_mul_not_mem {n : ℕ} {s : Finset ℤ}
    (h : IsMaxSumFree n s) {a : ℤ} (ha : a ∈ s) (h2a : 2 * a ∈ interval n) :
    2 * a ∉ s := by
  rw [two_mul]
  exact h.2.1 a ha a ha

end JSP000728
