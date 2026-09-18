import JSPProblem.PairBound
import JSPProblem.SumFreeCount

/-!
# JSP-000728 — counting sum-free subsets of a general integer interval

`sumFreeSetsIn u` / `sumFreeCountIn u` generalise `sumFreeSets` /
`sumFreeCount` from `interval n = {1,…,n}` to an arbitrary finset `u` of
integers — in particular to `Finset.Icc a b`.  This is needed to bound the
"minimum element" classes: a sum-free `M` with `min M = m` lives inside
`Finset.Icc m n`.

## Main results

* `sumFreeCountIn_le_two_pow` — `sumFreeCountIn u ≤ 2 ^ u.card`.
* `sumFreeCountIn_interval` — specialising to `interval n` recovers
  `sumFreeCount n` (by definition).
* `sumFreeCountIn_mono` — monotonicity in the ambient finset.
* `sumFreeCountIn_Icc_le_two_pow` — `sumFreeCountIn (Icc a b) ≤ 2^(b+1−a)`.
* `sumFreeCountIn_Icc_le_of_one_le` — for `1 ≤ a`,
  `sumFreeCountIn (Icc a b) ≤ 2·3^(⌊b/2⌋)` via `Icc a b ⊆ Icc 1 b` and the
  pairing bound `sumFreeCount_le_two_mul_three_pow` of `PairBound`.
* `card_sumFreeSetsIn_Icc_mem_le` — the minimum-element class bound:
  sum-free `s ⊆ Icc a b` containing `a` number at most `2^(b−a)`.

## Why no `3^(L/2)` bound in terms of the length

A bound purely in terms of the *length* `L = b − a + 1` that is better than
`2^L` cannot hold for general integer intervals: when `2a > b` the whole
interval `[a,b]` is itself sum-free (every sum of two elements exceeds
`b`), so `sumFreeCountIn (Icc a b) = 2^L`.  For example `Icc 3 5`
contributes all `8` subsets, already exceeding `2·3^1 = 6`.  The pairing
bound therefore has to be phrased in terms of the *top* endpoint `b`
(through `Icc a b ⊆ Icc 1 b = interval b.toNat`); translation invariance is
false since `x ↦ x + c` does not preserve `IsSumFree`.
-/

namespace JSP000728

/-- The finset of all sum-free subsets of an arbitrary finset `u`. -/
def sumFreeSetsIn (u : Finset ℤ) : Finset (Finset ℤ) :=
  u.powerset.filter IsSumFree

/-- The number of sum-free subsets of `u`. -/
def sumFreeCountIn (u : Finset ℤ) : ℕ := (sumFreeSetsIn u).card

theorem mem_sumFreeSetsIn {u s : Finset ℤ} :
    s ∈ sumFreeSetsIn u ↔ s ⊆ u ∧ IsSumFree s := by
  simp only [sumFreeSetsIn, Finset.mem_filter, Finset.mem_powerset]

/-- Trivial bound: `u` has at most `2^|u|` subsets at all. -/
theorem sumFreeCountIn_le_two_pow (u : Finset ℤ) :
    sumFreeCountIn u ≤ 2 ^ u.card := by
  calc sumFreeCountIn u
      ≤ (u.powerset).card := Finset.card_le_card (Finset.filter_subset _ _)
    _ = 2 ^ u.card := Finset.card_powerset _

/-- Specialising to `interval n` recovers `sumFreeCount n`. -/
theorem sumFreeCountIn_interval (n : ℕ) :
    sumFreeCountIn (interval n) = sumFreeCount n := rfl

/-- `sumFreeCountIn` is monotone in the ambient finset: `s ⊆ u ⊆ v` gives
`s ⊆ v`. -/
theorem sumFreeCountIn_mono {u v : Finset ℤ} (h : u ⊆ v) :
    sumFreeCountIn u ≤ sumFreeCountIn v := by
  apply Finset.card_le_card
  intro s hs
  rw [mem_sumFreeSetsIn] at hs
  exact mem_sumFreeSetsIn.mpr ⟨hs.1.trans h, hs.2⟩

/-! ### Sanity checks -/

/-- The empty finset has exactly one sum-free subset (`∅`). -/
theorem sumFreeCountIn_empty : sumFreeCountIn (∅ : Finset ℤ) = 1 := by decide

/-- `{0}` has only the empty sum-free subset, since `0 + 0 = 0`. -/
theorem sumFreeCountIn_singleton_zero :
    sumFreeCountIn ({0} : Finset ℤ) = 1 := by decide

/-- `{1}` has two sum-free subsets. -/
theorem sumFreeCountIn_singleton_one :
    sumFreeCountIn ({1} : Finset ℤ) = 2 := by decide

/-- A singleton `{a}` with `a ≠ 0` is sum-free. -/
theorem isSumFree_singleton {a : ℤ} (ha : a ≠ 0) :
    IsSumFree ({a} : Finset ℤ) := by
  intro x hx y hy hxy
  rw [Finset.mem_singleton] at hx hy hxy
  omega

/-- Hence any nonzero singleton contributes two sum-free subsets. -/
theorem sumFreeCountIn_singleton (a : ℤ) (ha : a ≠ 0) :
    sumFreeCountIn ({a} : Finset ℤ) = 2 := by
  have hset : sumFreeSetsIn {a} = {∅, {a}} := by
    ext s
    rw [mem_sumFreeSetsIn]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro ⟨hsub, hsf⟩
      rcases Finset.eq_empty_or_nonempty s with rfl | ⟨x, hx⟩
      · exact Or.inl rfl
      · have hxa : x = a := Finset.mem_singleton.mp (hsub hx)
        subst hxa
        exact Or.inr
          (Finset.Subset.antisymm hsub (Finset.singleton_subset_iff.mpr hx))
    · rintro (rfl | rfl)
      · exact ⟨Finset.empty_subset _,
          fun x hx => absurd hx (Finset.notMem_empty x)⟩
      · exact ⟨Finset.Subset.refl _, isSumFree_singleton ha⟩
  rw [sumFreeCountIn, hset]
  have hne : (∅ : Finset ℤ) ∉ ({{a}} : Finset (Finset ℤ)) := by
    rw [Finset.mem_singleton]
    intro h
    exact Finset.singleton_ne_empty a h.symm
  rw [Finset.card_insert_of_notMem hne, Finset.card_singleton]

/-! ### Removing `0` -/

/-- A sum-free set never contains `0` (since `0 + 0 = 0`). -/
theorem IsSumFree.not_mem_zero {s : Finset ℤ} (hs : IsSumFree s) :
    (0 : ℤ) ∉ s :=
  fun h => hs 0 h 0 h (by rwa [add_zero])

/-- Erasing `0` from the ambient finset does not change its sum-free
subsets. -/
theorem sumFreeSetsIn_erase_zero (u : Finset ℤ) :
    sumFreeSetsIn u = sumFreeSetsIn (u.erase 0) := by
  ext s
  simp only [mem_sumFreeSetsIn]
  constructor
  · rintro ⟨hsub, hsf⟩
    exact ⟨Finset.subset_erase.mpr ⟨hsub, hsf.not_mem_zero⟩, hsf⟩
  · rintro ⟨hsub, hsf⟩
    exact ⟨hsub.trans (Finset.erase_subset _ _), hsf⟩

/-- Consequently the sum-free subsets of `Icc 0 b` and `Icc 1 b` coincide. -/
theorem sumFreeSetsIn_Icc_zero (b : ℤ) :
    sumFreeSetsIn (Finset.Icc (0 : ℤ) b) =
      sumFreeSetsIn (Finset.Icc (1 : ℤ) b) := by
  ext s
  simp only [mem_sumFreeSetsIn]
  constructor
  · rintro ⟨hsub, hsf⟩
    refine ⟨fun x hx => ?_, hsf⟩
    have hxI := hsub hx
    rw [Finset.mem_Icc] at hxI ⊢
    have hx0 : x ≠ 0 := fun h => hsf.not_mem_zero (h ▸ hx)
    omega
  · rintro ⟨hsub, hsf⟩
    exact ⟨hsub.trans (Finset.Icc_subset_Icc (by norm_num) le_rfl), hsf⟩

/-! ### Integer intervals -/

/-- `Icc 1 b` is `interval b.toNat`; when `b ≤ 0` both sides are empty. -/
theorem Icc_one_eq_interval (b : ℤ) :
    Finset.Icc (1 : ℤ) b = interval b.toNat := by
  show Finset.Icc (1 : ℤ) b = Finset.Icc (1 : ℤ) ((b.toNat : ℕ) : ℤ)
  by_cases hb : 1 ≤ b
  · rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ b by omega)]
  · have ht : b.toNat = 0 := by omega
    rw [ht]
    rw [Finset.Icc_eq_empty (show ¬ (1 : ℤ) ≤ b from hb)]
    rw [Finset.Icc_eq_empty (show ¬ (1 : ℤ) ≤ ((0 : ℕ) : ℤ) by norm_num)]

/-- Length bound for an arbitrary integer interval:
`sumFreeCountIn (Icc a b) ≤ 2^(b+1−a)`.  This is sharp for intervals of
large integers (when `2a > b` the whole interval is sum-free). -/
theorem sumFreeCountIn_Icc_le_two_pow (a b : ℤ) :
    sumFreeCountIn (Finset.Icc a b) ≤ 2 ^ (b + 1 - a).toNat := by
  rw [← Int.card_Icc]
  exact sumFreeCountIn_le_two_pow _

/-- Alias in the requested form. -/
theorem sumFreeCountIn_Icc_le (a b : ℤ) :
    sumFreeCountIn (Finset.Icc a b) ≤ 2 ^ (b + 1 - a).toNat :=
  sumFreeCountIn_Icc_le_two_pow a b

/-- For the record (`m n : ℕ`): the min-class ambient interval `Icc m n`
has at most `2^(n+1−m)` sum-free subsets. -/
theorem sumFreeCountIn_Icc_le_two_pow_nat (m n : ℕ) :
    sumFreeCountIn (Finset.Icc (m : ℤ) (n : ℤ)) ≤ 2 ^ (n + 1 - m) := by
  have h := sumFreeCountIn_Icc_le_two_pow (m : ℤ) (n : ℤ)
  have hcast : ((n : ℤ) + 1 - (m : ℤ)).toNat = n + 1 - m := by omega
  rwa [hcast] at h

/-- For `1 ≤ a`, monotonicity plus the pairing bound give
`sumFreeCountIn (Icc a b) ≤ 2·3^(⌊b/2⌋)`. -/
theorem sumFreeCountIn_Icc_le_of_one_le {a b : ℤ} (ha : 1 ≤ a) :
    sumFreeCountIn (Finset.Icc a b) ≤ 2 * 3 ^ (b.toNat / 2) := by
  calc sumFreeCountIn (Finset.Icc a b)
      ≤ sumFreeCountIn (Finset.Icc 1 b) :=
        sumFreeCountIn_mono (Finset.Icc_subset_Icc ha le_rfl)
    _ = sumFreeCount b.toNat := by
        rw [Icc_one_eq_interval, sumFreeCountIn_interval]
    _ ≤ 2 * 3 ^ (b.toNat / 2) := sumFreeCount_le_two_mul_three_pow _

/-- The two bounds combined. -/
theorem sumFreeCountIn_Icc_le_min {a b : ℤ} (ha : 1 ≤ a) :
    sumFreeCountIn (Finset.Icc a b) ≤
      2 ^ (b + 1 - a).toNat ⊓ 2 * 3 ^ (b.toNat / 2) :=
  le_inf (sumFreeCountIn_Icc_le_two_pow a b)
    (sumFreeCountIn_Icc_le_of_one_le ha)

/-- The pairing bound for `ℕ`-valued intervals `Icc m n` with `1 ≤ m`. -/
theorem sumFreeCountIn_Icc_le_two_mul_three_pow {m n : ℕ} (hm : 1 ≤ m) :
    sumFreeCountIn (Finset.Icc (m : ℤ) (n : ℤ)) ≤ 2 * 3 ^ (n / 2) := by
  have h := sumFreeCountIn_Icc_le_of_one_le (a := (m : ℤ)) (b := (n : ℤ))
    (by exact_mod_cast hm)
  rwa [Int.toNat_natCast] at h

/-- The pairing bound for `ℕ`-valued intervals `Icc m n`, any `m`
(for `m = 0` the element `0` is never in a sum-free set). -/
theorem sumFreeCountIn_Icc_le_two_mul_three_pow' (m n : ℕ) :
    sumFreeCountIn (Finset.Icc (m : ℤ) (n : ℤ)) ≤ 2 * 3 ^ (n / 2) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [Nat.cast_zero]
    have h0 : sumFreeCountIn (Finset.Icc (0 : ℤ) (n : ℤ)) =
        sumFreeCountIn (Finset.Icc (1 : ℤ) (n : ℤ)) := by
      unfold sumFreeCountIn
      rw [sumFreeSetsIn_Icc_zero]
    rw [h0, Icc_one_eq_interval, sumFreeCountIn_interval, Int.toNat_natCast]
    exact sumFreeCount_le_two_mul_three_pow n
  · exact sumFreeCountIn_Icc_le_two_mul_three_pow hm

/-- The minimum-element class bound: sum-free `s ⊆ Icc a b` that contain
`a` (i.e. whose minimum is `a`) number at most `2^(b−a)` — the erasure map
`s ↦ s \ {a}` lands injectively in the powerset of `Icc (a+1) b`. -/
theorem card_sumFreeSetsIn_Icc_mem_le (a b : ℤ) :
    ((sumFreeSetsIn (Finset.Icc a b)).filter fun s => a ∈ s).card
      ≤ 2 ^ (b - a).toNat := by
  classical
  have hmem : ∀ s ∈ (sumFreeSetsIn (Finset.Icc a b)).filter (fun s => a ∈ s),
      s.erase a ∈ (Finset.Icc (a + 1) b).powerset := by
    intro s hs
    rw [Finset.mem_filter, mem_sumFreeSetsIn] at hs
    rw [Finset.mem_powerset]
    intro x hx
    have hxs := hs.1.1 (Finset.mem_of_mem_erase hx)
    rw [Finset.mem_Icc] at hxs ⊢
    have hne : x ≠ a := fun h => Finset.notMem_erase x s (h ▸ hx)
    omega
  have hinj : Set.InjOn (fun s : Finset ℤ => s.erase a)
      ((sumFreeSetsIn (Finset.Icc a b)).filter fun s => a ∈ s) := by
    intro s₁ h₁ s₂ h₂ hst
    rw [Finset.mem_coe, Finset.mem_filter] at h₁ h₂
    have hst' : s₁.erase a = s₂.erase a := hst
    rw [← Finset.insert_erase h₁.2, ← Finset.insert_erase h₂.2, hst']
  calc ((sumFreeSetsIn (Finset.Icc a b)).filter fun s => a ∈ s).card
      ≤ ((Finset.Icc (a + 1) b).powerset).card :=
        Finset.card_le_card_of_injOn _ hmem hinj
    _ = 2 ^ (b - a).toNat := by
        rw [Finset.card_powerset, Int.card_Icc]
        congr 1
        omega

end JSP000728
