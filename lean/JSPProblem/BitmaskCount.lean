import JSPProblem.Basic
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Nat.BitIndices
import Mathlib.Data.List.Nodup
import Mathlib.Order.Interval.Finset.Nat

/-!
# JSP-000728 — exact counts for `n = 13, 14, 15` via a bitmask bridge

Plain kernel `decide` on `maxSumFreeCount n` exhausts memory for `n ≥ 13`:
evaluating `(interval n).powerset` materialises `2^n` finsets of integers.
This file instead counts *bitmasks*: a natural number `k < 2^n` codes the set
`maskSet k = {i + 1 : bit i of k is set}`.

* `maskSet k` : the `Finset ℤ` coded by the bitmask `k`.
* `maskSumFree n k` / `maskMaxSumFree n k` : `Bool`-valued checks, proved
  equivalent to `IsSumFree (maskSet k)` / `IsMaxSumFree n (maskSet k)`.
* `maskCount n` : the number of masks `< 2^n` coding a maximal sum-free set,
  shown equal to `maxSumFreeCount n` via the bijection
  `Finset.equivBitIndices : ℕ ≃ Finset ℕ`.

Since only `Nat` testBit/lor/list operations remain, `decide` evaluates
`maskCount 13`, `maskCount 14` and `maskCount 15` comfortably in the kernel.

The verified values are:

| `n`  | `maxSumFreeCount n` |
|------|---------------------|
| 13   | 51                  |
| 14   | 66                  |
| 15   | 86                  |

continuing the sequence from `ExactCounts.lean`.
-/

namespace JSP000728

/-! ### The bitmask coding -/

/-- The finset of integers coded by a bitmask: bit `i` of `k` codes `i + 1`. -/
def maskSet (k : ℕ) : Finset ℤ :=
  (Finset.equivBitIndices k).image fun i : ℕ => (i : ℤ) + 1

theorem mem_maskSet {k : ℕ} {x : ℤ} :
    x ∈ maskSet k ↔ ∃ i : ℕ, k.testBit i = true ∧ (i : ℤ) + 1 = x := by
  simp only [maskSet, Finset.mem_image, Finset.equivBitIndices_apply,
    List.mem_toFinset, Nat.mem_bitIndices]

/-- Bits `< n` that are set in `k`, as a sorted list. -/
def maskBits (n k : ℕ) : List ℕ := (List.range n).filter fun i => k.testBit i

theorem mem_maskBits {n k i : ℕ} :
    i ∈ maskBits n k ↔ i < n ∧ k.testBit i = true := by
  simp only [maskBits, List.mem_filter, List.mem_range]

theorem testBit_lt_of_lt_two_pow {n k i : ℕ} (hk : k < 2 ^ n)
    (hi : k.testBit i = true) : i < n := by
  by_contra h
  have hle : 2 ^ n ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (Nat.not_lt.mp h)
  have hbit := Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hk hle)
  rw [hi] at hbit
  simp at hbit

theorem maskSet_injective : Function.Injective maskSet := by
  intro a b h
  have hinj : Function.Injective fun i : ℕ => (i : ℤ) + 1 := fun x y hxy => by
    have h2 : (x : ℤ) + 1 = (y : ℤ) + 1 := hxy
    omega
  simp only [maskSet] at h
  apply Finset.equivBitIndices.injective
  exact Finset.image_injective hinj h

theorem maskSet_subset_interval {n k : ℕ} (hk : k < 2 ^ n) :
    maskSet k ⊆ interval n := by
  intro x hx
  rw [mem_maskSet] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  have hi' := testBit_lt_of_lt_two_pow hk hi
  simp only [interval, Finset.mem_Icc]
  constructor <;> omega

/-- A bitmask `k < 2^n` is sum-free iff no two set bits sum to a set bit. -/
theorem isSumFree_maskSet_iff {n k : ℕ} (hk : k < 2 ^ n) :
    IsSumFree (maskSet k) ↔
      ∀ i ∈ maskBits n k, ∀ j ∈ maskBits n k, k.testBit (i + j + 1) = false := by
  unfold IsSumFree
  constructor
  · intro h i hi j hj
    rw [mem_maskBits] at hi hj
    have hxi : (i : ℤ) + 1 ∈ maskSet k := mem_maskSet.mpr ⟨i, hi.2, rfl⟩
    have hyj : (j : ℤ) + 1 ∈ maskSet k := mem_maskSet.mpr ⟨j, hj.2, rfl⟩
    have hxy := h _ hxi _ hyj
    by_contra hc
    rw [Bool.not_eq_false] at hc
    apply hxy
    rw [mem_maskSet]
    exact ⟨i + j + 1, hc, by omega⟩
  · intro h x hx y hy hxy
    rw [mem_maskSet] at hx hy
    obtain ⟨i, hi, rfl⟩ := hx
    obtain ⟨j, hj, rfl⟩ := hy
    rw [mem_maskSet] at hxy
    obtain ⟨l, hl, hll⟩ := hxy
    have hl_eq : l = i + j + 1 := by omega
    have hi' := testBit_lt_of_lt_two_pow hk hi
    have hj' := testBit_lt_of_lt_two_pow hk hj
    have hbad := h i (mem_maskBits.mpr ⟨hi', hi⟩) j (mem_maskBits.mpr ⟨hj', hj⟩)
    rw [hl_eq] at hl
    rw [hl] at hbad
    simp at hbad

/-- `maskSet` of `k` with bit `i` forced on is `maskSet k` with `i + 1` inserted. -/
theorem maskSet_or_two_pow (k i : ℕ) :
    maskSet (k ||| 2 ^ i) = insert ((i : ℤ) + 1) (maskSet k) := by
  have hset : Finset.equivBitIndices (k ||| 2 ^ i) =
      insert i (Finset.equivBitIndices k) := by
    ext j
    simp only [Finset.equivBitIndices_apply, List.mem_toFinset, Nat.mem_bitIndices,
      Nat.testBit_or, Finset.mem_insert]
    by_cases hji : j = i
    · subst hji
      simp [Nat.testBit_two_pow_self]
    · simp [Nat.testBit_two_pow_of_ne (show i ≠ j by omega), hji]
  simp only [maskSet, hset, Finset.image_insert]

/-- Every subset of `interval n` is `maskSet k` for some `k < 2^n`. -/
theorem maskSet_surjective {n : ℕ} {s : Finset ℤ} (hs : s ⊆ interval n) :
    ∃ k : ℕ, k < 2 ^ n ∧ maskSet k = s := by
  classical
  set u : Finset ℕ := s.image fun x : ℤ => (x - 1).toNat with hu
  have hu_lt : ∀ i ∈ u, i < n := by
    intro i hi
    simp only [hu, Finset.mem_image] at hi
    obtain ⟨x, hx, rfl⟩ := hi
    have hxn := hs hx
    simp only [interval, Finset.mem_Icc] at hxn
    have hx1 : ((x - 1).toNat : ℤ) = x - 1 := Int.toNat_of_nonneg (by omega)
    omega
  refine ⟨Finset.equivBitIndices.symm u, ?_, ?_⟩
  · by_contra hge
    have hge' : 2 ^ n ≤ Finset.equivBitIndices.symm u := Nat.not_lt.mp hge
    obtain ⟨j, hj, hbj⟩ := Nat.exists_ge_and_testBit_of_ge_two_pow hge'
    have hj_mem : j ∈ u := by
      have h2 : j ∈ Finset.equivBitIndices (Finset.equivBitIndices.symm u) := by
        simp only [Finset.equivBitIndices_apply, List.mem_toFinset,
          Nat.mem_bitIndices]
        exact hbj
      rwa [Finset.equivBitIndices.apply_symm_apply] at h2
    exact absurd (hu_lt j hj_mem) (by omega)
  · simp only [maskSet, Finset.equivBitIndices.apply_symm_apply, hu,
      Finset.image_image]
    ext y
    simp only [Finset.mem_image, Function.comp_apply]
    constructor
    · rintro ⟨x, hx, hxy⟩
      have hxn := hs hx
      simp only [interval, Finset.mem_Icc] at hxn
      have e : ((x - 1).toNat : ℤ) + 1 = x := by
        rw [Int.toNat_of_nonneg (by omega)]
        omega
      rw [e] at hxy
      exact hxy ▸ hx
    · intro hy
      have hyn := hs hy
      simp only [interval, Finset.mem_Icc] at hyn
      refine ⟨y, hy, ?_⟩
      rw [Int.toNat_of_nonneg (by omega)]
      omega

/-! ### Decidable predicates on masks -/

/-- `Bool` check: the integer set coded by mask `k` (viewed below `n`) is
sum-free. -/
def maskSumFree (n k : ℕ) : Bool :=
  let bits := maskBits n k
  bits.all fun i => bits.all fun j => !k.testBit (i + j + 1)

theorem maskSumFree_eq_true_iff {n k : ℕ} (hk : k < 2 ^ n) :
    maskSumFree n k = true ↔ IsSumFree (maskSet k) := by
  rw [isSumFree_maskSet_iff hk]
  simp only [maskSumFree, List.all_eq_true, Bool.not_eq_true']

/-- `Bool` check: the integer set coded by mask `k` is an inclusion-maximal
sum-free subset of `{1, …, n}`. -/
def maskMaxSumFree (n k : ℕ) : Bool :=
  maskSumFree n k && (List.range n).all fun i =>
    k.testBit i || !maskSumFree n (k ||| 2 ^ i)

theorem lor_two_pow_lt_two_pow {n k i : ℕ} (hk : k < 2 ^ n) (hi : i < n) :
    k ||| 2 ^ i < 2 ^ n :=
  Nat.or_lt_two_pow hk ((Nat.pow_lt_pow_iff_right (by decide)).mpr hi)

theorem maskMaxSumFree_eq_true_iff {n k : ℕ} (hk : k < 2 ^ n) :
    maskMaxSumFree n k = true ↔ IsMaxSumFree n (maskSet k) := by
  unfold maskMaxSumFree IsMaxSumFree
  rw [Bool.and_eq_true_iff, maskSumFree_eq_true_iff hk]
  simp only [List.all_eq_true, List.mem_range]
  constructor
  · rintro ⟨hsf, hall⟩
    refine ⟨maskSet_subset_interval hk, hsf, fun x hxn hxs => ?_⟩
    simp only [interval, Finset.mem_Icc] at hxn
    set i := (x - 1).toNat with hi_def
    have hxi : (i : ℤ) + 1 = x := by
      rw [hi_def, Int.toNat_of_nonneg (by omega)]
      omega
    have hi_lt : i < n := by
      have e : ((x - 1).toNat : ℤ) = x - 1 := Int.toNat_of_nonneg (by omega)
      omega
    have hbit : k.testBit i = false := by
      by_contra hb
      rw [Bool.not_eq_false] at hb
      have hmem : (i : ℤ) + 1 ∈ maskSet k := mem_maskSet.mpr ⟨i, hb, rfl⟩
      rw [hxi] at hmem
      exact hxs hmem
    have hclause := hall i hi_lt
    rw [hbit, Bool.false_or, Bool.not_eq_true'] at hclause
    have hlt' := lor_two_pow_lt_two_pow hk hi_lt
    have hnsf : ¬ IsSumFree (maskSet (k ||| 2 ^ i)) := fun hsf' =>
      Bool.false_ne_true (hclause ▸ (maskSumFree_eq_true_iff hlt').mpr hsf')
    rwa [maskSet_or_two_pow, hxi] at hnsf
  · rintro ⟨hsub, hsf, hmax⟩
    refine ⟨hsf, fun i hi_lt => ?_⟩
    by_cases hbit : k.testBit i = true
    · rw [hbit]
      rfl
    · rw [Bool.not_eq_true] at hbit
      rw [hbit, Bool.false_or, Bool.not_eq_true']
      have hlt' := lor_two_pow_lt_two_pow hk hi_lt
      have hx_mem : (i : ℤ) + 1 ∈ interval n := by
        simp only [interval, Finset.mem_Icc]
        omega
      have hx_nmem : (i : ℤ) + 1 ∉ maskSet k := by
        intro hm
        rw [mem_maskSet] at hm
        obtain ⟨l, hl, hll⟩ := hm
        have hli : l = i := by omega
        subst hli
        rw [hbit] at hl
        simp at hl
      have hnsf := hmax _ hx_mem hx_nmem
      rw [← maskSet_or_two_pow] at hnsf
      by_contra hc
      rw [Bool.not_eq_false] at hc
      exact hnsf ((maskSumFree_eq_true_iff hlt').mp hc)

/-! ### The count -/

/-- The number of masks `< 2^n` coding an inclusion-maximal sum-free subset
of `{1, …, n}`.  Computable by the kernel through `Nat` operations only. -/
def maskCount (n : ℕ) : ℕ :=
  ((List.range (2 ^ n)).filter fun k => maskMaxSumFree n k).length

theorem card_range_filter (m : ℕ) (p : ℕ → Bool) :
    ((Finset.range m).filter fun k => p k = true).card =
      ((List.range m).filter p).length := by
  rw [← List.toFinset_range, ← List.toFinset_filter]
  exact List.toFinset_card_of_nodup (List.nodup_range.filter p)

/-- `maskSet` identifies the masks below `2^n` satisfying `maskMaxSumFree`
with the inclusion-maximal sum-free subsets of `{1, …, n}`. -/
theorem maxSumFreeCount_eq_maskCount (n : ℕ) :
    maxSumFreeCount n = maskCount n := by
  classical
  have hset : maxSumFreeSets n =
      ((Finset.range (2 ^ n)).filter fun k => maskMaxSumFree n k = true).image
        maskSet := by
    ext s
    simp only [maxSumFreeSets, Finset.mem_filter, Finset.mem_powerset,
      Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨hsub, hmax⟩
      obtain ⟨k, hk, rfl⟩ := maskSet_surjective hsub
      exact ⟨k, ⟨hk, (maskMaxSumFree_eq_true_iff hk).mpr hmax⟩, rfl⟩
    · rintro ⟨k, ⟨hk, hmk⟩, rfl⟩
      exact ⟨maskSet_subset_interval hk, (maskMaxSumFree_eq_true_iff hk).mp hmk⟩
  rw [maxSumFreeCount, hset, Finset.card_image_of_injective _ maskSet_injective]
  exact card_range_filter (2 ^ n) (maskMaxSumFree n)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem count_thirteen : maxSumFreeCount 13 = 51 := by
  rw [maxSumFreeCount_eq_maskCount]
  decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem count_fourteen : maxSumFreeCount 14 = 66 := by
  rw [maxSumFreeCount_eq_maskCount]
  decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem count_fifteen : maxSumFreeCount 15 = 86 := by
  rw [maxSumFreeCount_eq_maskCount]
  decide

end JSP000728
