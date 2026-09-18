import JSPProblem.SumFreeCount
import JSPProblem.UpperBound
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sigma

/-!
# JSP-000728 — container-method vocabulary

Statement-level vocabulary for the *container method* behind the upper bound
`f(n) ≤ 2 ^ ((1/4 + o(1)) · n)` (Balogh–Liu–Sharifzadeh–Treglown, JEMS 2018,
building on Green and on Balogh–Morris–Samotij).

The BLST18 container lemma asserts, roughly, that for every `n` there is a
family `F` of "containers" — subsets of `{1,…,n}` — such that

* every sum-free `s ⊆ {1,…,n}` sits inside some `C ∈ F`;
* `F` is exponentially small: `F.card ≤ 2 ^ (o(n))`;
* every `C ∈ F` is "almost sum-free": it contains only `o(n²)` Schur triples
  and becomes sum-free after deleting `o(n)` elements — in particular
  `C.card ≤ n/2 + o(n)` once the supersaturation structure is exploited.

The genuinely hard mathematical content is the *existence* of such a family;
the present file only fixes the vocabulary (`schurTriples`, `IsContainerFamily`,
`IsGoodContainerFamily`) and proves the easy counting consequences: a
container family `F` whose members all have at most `K` elements yields
`f(n) ≤ F.card * 2 ^ K`, since each of the `F.card` containers houses at most
`2 ^ K` sum-free subsets.

## Contents

* `schurTriples`, `schurTripleCount` — Schur triples `(x, y, z)` with
  `x + y = z`, and the bounds `schurTripleCount s ≤ s.card ^ 3` and
  `schurTripleCount s = 0 ↔ IsSumFree s`.
* `IsContainerFamily`, `IsGoodContainerFamily` — the covering property and a
  size-capped strengthening, with
  `sumFreeCount_le_containerFamily : sumFreeCount n ≤ F.card * 2 ^ n` and
  `sumFreeCount_le_of_good : sumFreeCount n ≤ F.card * 2 ^ K`
  (plus the `maxSumFreeCount` corollaries).
* `schurTripleCount_interval_ge` — the interval `{1,…,n}` itself has at least
  `n·(n-1)/2` Schur triples `(a, b, a+b)` with `a, b ≥ 1`, `a + b ≤ n`.
-/

namespace JSP000728

/-! ## Schur triples -/

/-- The Schur triples of `s`: ordered triples `(x, y, z) ∈ s × s × s` with
`x + y = z`. -/
def schurTriples (s : Finset ℤ) : Finset (ℤ × ℤ × ℤ) :=
  (s ×ˢ (s ×ˢ s)).filter fun t => t.1 + t.2.1 = t.2.2

/-- The number of Schur triples of `s`. -/
def schurTripleCount (s : Finset ℤ) : ℕ := (schurTriples s).card

/-- Trivial bound: at most `|s|³` Schur triples. -/
theorem schurTripleCount_le_card_cubed (s : Finset ℤ) :
    schurTripleCount s ≤ s.card ^ 3 := by
  unfold schurTripleCount schurTriples
  calc ((s ×ˢ (s ×ˢ s)).filter fun t => t.1 + t.2.1 = t.2.2).card
      ≤ (s ×ˢ (s ×ˢ s)).card := Finset.card_filter_le _ _
    _ = s.card * (s.card * s.card) := by
        rw [Finset.card_product, Finset.card_product]
    _ = s.card ^ 3 := by ring

/-- `s` has no Schur triple iff it is sum-free. -/
theorem schurTripleCount_eq_zero_iff (s : Finset ℤ) :
    schurTripleCount s = 0 ↔ IsSumFree s := by
  rw [schurTripleCount, Finset.card_eq_zero]
  constructor
  · intro h x hx y hy hxy
    have hmem : ⟨x, y, x + y⟩ ∈ schurTriples s := by
      rw [schurTriples, Finset.mem_filter]
      exact ⟨Finset.mem_product.mpr
        ⟨hx, Finset.mem_product.mpr ⟨hy, hxy⟩⟩, rfl⟩
    rw [h] at hmem
    exact Finset.notMem_empty _ hmem
  · intro hsf
    apply Finset.eq_empty_of_forall_notMem
    rintro ⟨a, b, c⟩ ht
    rw [schurTriples, Finset.mem_filter, Finset.mem_product,
      Finset.mem_product] at ht
    obtain ⟨⟨ha, hb, hc⟩, heq⟩ := ht
    exact hsf a ha b hb (by rw [heq]; exact hc)

/-! ## Container families -/

/-- `F` is a *container family* for `interval n` when every `C ∈ F` is a
subset of `{1,…,n}` and every sum-free subset of `{1,…,n}` is contained in
some `C ∈ F`. -/
def IsContainerFamily (n : ℕ) (F : Finset (Finset ℤ)) : Prop :=
  (∀ C ∈ F, C ⊆ interval n) ∧
    ∀ s : Finset ℤ, s ⊆ interval n → IsSumFree s → ∃ C ∈ F, s ⊆ C

/-- The one-element family `{interval n}` is trivially a container family. -/
theorem isContainerFamily_singleton (n : ℕ) :
    IsContainerFamily n {interval n} := by
  refine ⟨fun C hC => ?_, fun s hs _ => ⟨interval n, ?_, hs⟩⟩
  · rw [Finset.mem_singleton] at hC
    subst hC
    exact fun _ hx => hx
  · exact Finset.mem_singleton_self _

/-- A container family of size `|F|` covers every sum-free set by the powerset
of some member, giving `sumFreeCount n ≤ |F| · 2 ^ n`. -/
theorem sumFreeCount_le_containerFamily {n : ℕ} {F : Finset (Finset ℤ)}
    (hF : IsContainerFamily n F) : sumFreeCount n ≤ F.card * 2 ^ n := by
  have hsub : sumFreeSets n ⊆ F.biUnion fun C => C.powerset := by
    intro s hs
    rw [mem_sumFreeSets] at hs
    obtain ⟨C, hCF, hsC⟩ := hF.2 s hs.1 hs.2
    rw [Finset.mem_biUnion]
    exact ⟨C, hCF, Finset.mem_powerset.mpr hsC⟩
  calc sumFreeCount n
      ≤ (F.biUnion fun C => C.powerset).card := Finset.card_le_card hsub
    _ ≤ ∑ C ∈ F, C.powerset.card := Finset.card_biUnion_le
    _ = ∑ C ∈ F, 2 ^ C.card :=
        Finset.sum_congr rfl fun C _ => Finset.card_powerset C
    _ ≤ ∑ _C ∈ F, 2 ^ n := by
        apply Finset.sum_le_sum
        intro C hC
        have hcard : C.card ≤ n := by
          have h := Finset.card_le_card (hF.1 C hC)
          rwa [card_interval] at h
        exact Nat.pow_le_pow_right (by norm_num) hcard
    _ = F.card * 2 ^ n := by rw [Finset.sum_const, smul_eq_mul]

/-- The `maxSumFreeCount` corollary: `f n ≤ |F| · 2 ^ n`. -/
theorem maxSumFreeCount_le_containerFamily {n : ℕ} {F : Finset (Finset ℤ)}
    (hF : IsContainerFamily n F) : maxSumFreeCount n ≤ F.card * 2 ^ n :=
  (maxSumFreeCount_le_sumFreeCount n).trans
    (sumFreeCount_le_containerFamily hF)

/-! ## Size-capped container families -/

/-- A *good* container family additionally caps the cardinality of every
container at `K`.  This is the shape the actual container lemma delivers
(with `K ≈ n / 2`). -/
def IsGoodContainerFamily (n : ℕ) (F : Finset (Finset ℤ)) (K : ℕ) : Prop :=
  IsContainerFamily n F ∧ ∀ C ∈ F, C.card ≤ K

/-- Sharper count: a good container family gives
`sumFreeCount n ≤ |F| · 2 ^ K`. -/
theorem sumFreeCount_le_of_good {n : ℕ} {F : Finset (Finset ℤ)} {K : ℕ}
    (hF : IsGoodContainerFamily n F K) : sumFreeCount n ≤ F.card * 2 ^ K := by
  obtain ⟨hF, hK⟩ := hF
  have hsub : sumFreeSets n ⊆ F.biUnion fun C => C.powerset := by
    intro s hs
    rw [mem_sumFreeSets] at hs
    obtain ⟨C, hCF, hsC⟩ := hF.2 s hs.1 hs.2
    rw [Finset.mem_biUnion]
    exact ⟨C, hCF, Finset.mem_powerset.mpr hsC⟩
  calc sumFreeCount n
      ≤ (F.biUnion fun C => C.powerset).card := Finset.card_le_card hsub
    _ ≤ ∑ C ∈ F, C.powerset.card := Finset.card_biUnion_le
    _ = ∑ C ∈ F, 2 ^ C.card :=
        Finset.sum_congr rfl fun C _ => Finset.card_powerset C
    _ ≤ ∑ _C ∈ F, 2 ^ K :=
        Finset.sum_le_sum fun C hC =>
          Nat.pow_le_pow_right (by norm_num) (hK C hC)
    _ = F.card * 2 ^ K := by rw [Finset.sum_const, smul_eq_mul]

/-- The `maxSumFreeCount` corollary of the sharpened bound. -/
theorem maxSumFreeCount_le_of_good {n : ℕ} {F : Finset (Finset ℤ)} {K : ℕ}
    (hF : IsGoodContainerFamily n F K) :
    maxSumFreeCount n ≤ F.card * 2 ^ K :=
  (maxSumFreeCount_le_sumFreeCount n).trans (sumFreeCount_le_of_good hF)

/-! ## A lower bound on the number of Schur triples of `interval n` -/

/-- The interval `{1,…,n}` itself has at least `n·(n-1)/2` Schur triples:
the map `(i, j) ↦ (i+1, j+1, i+j+2)` injects
`{(i,j) : i < n-1, j < n-1-i}` — which has `n·(n-1)/2` elements — into the
Schur triples `(a, b, a+b)` with `a, b ≥ 1` and `a + b ≤ n`. -/
theorem schurTripleCount_interval_ge (n : ℕ) :
    n * (n - 1) / 2 ≤ schurTripleCount (interval n) := by
  rcases n with _ | m
  · simp
  classical
  show (m + 1) * m / 2 ≤ schurTripleCount (interval (m + 1))
  set D : Finset (Σ _ : ℕ, ℕ) :=
    (Finset.range m).sigma fun i => Finset.range (m - i) with hD
  set g : (Σ _ : ℕ, ℕ) → ℤ × ℤ × ℤ :=
    fun p => ((p.1 : ℤ) + 1, (p.2 : ℤ) + 1, (p.1 : ℤ) + (p.2 : ℤ) + 2) with hg
  have hsub : D.card ≤ schurTripleCount (interval (m + 1)) := by
    unfold schurTripleCount
    refine Finset.card_le_card_of_injOn g ?_ ?_
    · rintro ⟨i, j⟩ hp
      rw [hD, Finset.mem_coe, Finset.mem_sigma] at hp
      simp only [Finset.mem_range] at hp
      obtain ⟨hi, hj⟩ := hp
      simp only [Finset.mem_coe, schurTriples, Finset.mem_filter,
        Finset.mem_product, interval, Finset.mem_Icc, hg]
      omega
    · rintro ⟨i, j⟩ - ⟨i', j'⟩ - h
      simp only [hg, Prod.mk.injEq] at h
      obtain ⟨h1, h2, -⟩ := h
      have e1 : i = i' := by omega
      have e2 : j = j' := by omega
      subst e1; subst e2; rfl
  have hcard : D.card = ∑ i ∈ Finset.range m, (m - i) := by
    rw [hD, Finset.card_sigma]
    exact Finset.sum_congr rfl fun i _ => by rw [Finset.card_range]
  have htwo : 2 * D.card = (m + 1) * m := by
    rw [hcard]
    have step1 : (∑ i ∈ Finset.range m, (m - i))
        = ∑ i ∈ Finset.range m, (i + 1) := by
      have h := Finset.sum_range_reflect (fun i => i + 1) m
      rw [← h]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mem_range] at hi
      omega
    have e : (∑ i ∈ Finset.range m, (m - i))
        + (∑ i ∈ Finset.range m, (i + 1)) = (m + 1) * m := by
      rw [← Finset.sum_add_distrib]
      have hsum : (∑ i ∈ Finset.range m, (m - i + (i + 1)))
          = ∑ _i ∈ Finset.range m, (m + 1) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mem_range] at hi
        omega
      rw [hsum, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_comm]
    calc 2 * ∑ i ∈ Finset.range m, (m - i)
        = (∑ i ∈ Finset.range m, (m - i))
          + ∑ i ∈ Finset.range m, (i + 1) := by
          rw [two_mul]
          exact congrArg _ step1
      _ = (m + 1) * m := e
  have hle : (m + 1) * m / 2 ≤ D.card := by omega
  exact hle.trans hsub

end JSP000728
