import JSPProblem.TwoMin
import JSPProblem.FibBound
import Mathlib.NumberTheory.Real.GoldenRatio

/-!
# JSP-000728 — `secondMinClass` bounds without the ladder analysis

The injection `secondMinClass_card_le_shiftFree2` already accounts for the
optional `{m, s}` elements (deleting `m` and `s` is injective on the class),
so **no extra factor of `4` is needed**: every bound below is a pure power
`card ≤ φ^e`.

Two regimes are treated, neither of which needs the gap-≥3 ("ladder")
analysis of `shiftFree2`:

* **All `s` — a single shift suffices.**  Dropping the `s`-translate
  constraint, `M \ {m, s} ⊆ Icc (s+1) n` is merely `m`-shift-free.
  Translating by `m - s` identifies `Icc (s+1) n` with
  `Icc (m+1) (n-s+m)` (`image_add_Icc`,
  `card_powerset_filter_shiftFree_image_add`), where the residue-class
  factorisation of `NoConsec` applies.  Each residue class of length `L`
  contributes `fib (L+2) ≤ φ^(L+1)`, but *only when it is nonempty* —
  empty classes contribute `fib 2 = 1`, not `φ`
  (`fib_add_two_le_goldenRatio_pow`, `filter_Icc_nonempty_cls`).
  Since the lengths sum to `n - s` and the nonempty classes are
  `r ∈ Icc 1 (min m (n-s))`, this yields

    `(secondMinClass n m s).card ≤ φ^((n-s).toNat + (min m (n-s)).toNat)`

  (`secondMinClass_card_le_goldenRatio`), with the coarser but cleaner
  `≤ φ^((n-s) + m)` recorded as `secondMinClass_card_le_goldenRatio_add`.

* **`2s > n` — the `s`-shift is vacuous.**  For `x ∈ Icc (s+1) n` one has
  `x + s ≥ 2s + 1 > n`, so `shiftFree2 m s ↔ shiftFree m` there
  (`shiftFree2_iff_shiftFree_of_vacuous`,
  `powerset_filter_shiftFree2_eq_of_vacuous`,
  `secondMinClass_card_le_shiftFree_of_vacuous`): in this regime the
  single-shift count is *exact*, not an over-estimate.  The exponent can
  nevertheless not be lowered to `n - s` alone: for `m > n - s` all
  `2^(n-s)` subsets of the interval are `m`-shift-free, and `2 > φ`.
-/

namespace JSP000728

/-- **Vacuous `s`-shift.**  When `2s > n`, every `x ∈ Icc (s+1) n` satisfies
`x + s ≥ 2s + 1 > n`, so the `s`-translate constraint is vacuous on subsets
of the interval and `shiftFree2 m s` collapses to `shiftFree m`. -/
theorem shiftFree2_iff_shiftFree_of_vacuous {n : ℕ} {m s : ℤ}
    (hns : (n : ℤ) < 2 * s) {t : Finset ℤ}
    (ht : t ⊆ Finset.Icc (s + 1) (n : ℤ)) :
    shiftFree2 m s t ↔ shiftFree m t := by
  refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
  intro x hx hC
  have h1 := Finset.mem_Icc.mp (ht hx)
  have h2 := Finset.mem_Icc.mp (ht hC)
  omega

/-- In the vacuous regime `2s > n` the two filtered powersets over
`Icc (s+1) n` coincide. -/
theorem powerset_filter_shiftFree2_eq_of_vacuous {n : ℕ} {m s : ℤ}
    (hns : (n : ℤ) < 2 * s) :
    (Finset.Icc (s + 1) (n : ℤ)).powerset.filter (shiftFree2 m s) =
      (Finset.Icc (s + 1) (n : ℤ)).powerset.filter (shiftFree m) := by
  apply Finset.filter_congr
  intro t ht
  exact shiftFree2_iff_shiftFree_of_vacuous hns (Finset.mem_powerset.mp ht)

/-- Translating an integer interval shifts both endpoints. -/
theorem image_add_Icc (a b c : ℤ) :
    (Finset.Icc a b).image (· + c) = Finset.Icc (a + c) (b + c) := by
  ext x
  simp only [Finset.mem_image, Finset.mem_Icc]
  constructor
  · rintro ⟨y, ⟨h1, h2⟩, rfl⟩
    exact ⟨by omega, by omega⟩
  · rintro ⟨h1, h2⟩
    exact ⟨x - c, ⟨by omega, by omega⟩, by ring⟩

/-- **Translation invariance of the shift-free count.**  `x ↦ x + c`
commutes with `x ↦ x + m`, so it transports shift-free subsets of `T`
bijectively onto shift-free subsets of `T.image (· + c)`. -/
theorem powerset_filter_shiftFree_image_add (m c : ℤ) (T : Finset ℤ) :
    (T.image (· + c)).powerset.filter (shiftFree m) =
      (T.powerset.filter (shiftFree m)).image fun t => t.image (· + c) := by
  ext u
  rw [Finset.mem_filter, Finset.mem_powerset, Finset.mem_image]
  constructor
  · rintro ⟨hu, hsf⟩
    refine ⟨u.image (· - c), ?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_powerset]
      refine ⟨?_, ?_⟩
      · intro x hx
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
        obtain ⟨z, hz, hzy⟩ := Finset.mem_image.mp (hu hy)
        rw [← hzy]
        simpa using hz
      · intro x hx hC
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
        obtain ⟨w, hw, hwy⟩ := Finset.mem_image.mp hC
        have hweq : w = y + m := by omega
        exact hsf y hy (hweq ▸ hw)
    · ext x
      simp only [Finset.mem_image]
      constructor
      · rintro ⟨y, hy, rfl⟩
        obtain ⟨z, hz, rfl⟩ := hy
        simpa using hz
      · intro hx
        exact ⟨x - c, ⟨x, hx, rfl⟩, by ring⟩
  · rintro ⟨t, ht, rfl⟩
    rw [Finset.mem_filter, Finset.mem_powerset] at ht
    refine ⟨Finset.image_subset_image ht.1, ?_⟩
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    rw [show y + c + m = (y + m) + c from by ring]
    intro hC
    obtain ⟨z, hz, hzy⟩ := Finset.mem_image.mp hC
    have hzeq : z = y + m := by omega
    exact ht.2 y hy (hzeq ▸ hz)

/-- The shift-free subset count of a finset is translation-invariant. -/
theorem card_powerset_filter_shiftFree_image_add (m c : ℤ) (T : Finset ℤ) :
    ((T.image (· + c)).powerset.filter (shiftFree m)).card =
      (T.powerset.filter (shiftFree m)).card := by
  rw [powerset_filter_shiftFree_image_add]
  exact Finset.card_image_of_injective _
    (Finset.image_injective
      (show Function.Injective (fun x : ℤ => x + c) from
        fun a b h => by have h' : a + c = b + c := h; omega))

/-- **Single-shift product bound on `Icc (s+1) n`.**  Translating by
`m - s` sends `Icc (s+1) n` to `Icc (m+1) (n-s+m)`, where the residue-class
factorisation applies; the product over classes gives Fibonacci factors. -/
theorem card_powerset_filter_shiftFree_Icc_le {n : ℕ} {m s : ℤ}
    (hm : 1 ≤ m) (hsn : s ≤ (n : ℤ)) :
    ((Finset.Icc (s + 1) (n : ℤ)).powerset.filter (shiftFree m)).card ≤
      ∏ r ∈ Finset.Icc 1 m,
        Nat.fib (((((n : ℤ) - s + m) - r) / m).toNat + 2) := by
  have hNz : ((((n : ℤ) - s + m).toNat : ℕ) : ℤ) = (n : ℤ) - s + m :=
    Int.toNat_of_nonneg (by omega)
  have hshift : (Finset.Icc (s + 1) (n : ℤ)).image (· + (m - s)) =
      Finset.Icc (m + 1) (((n : ℤ) - s + m).toNat : ℤ) := by
    rw [image_add_Icc, hNz]
    congr 1 <;> omega
  calc ((Finset.Icc (s + 1) (n : ℤ)).powerset.filter (shiftFree m)).card
      = (((Finset.Icc (s + 1) (n : ℤ)).image (· + (m - s))).powerset.filter
          (shiftFree m)).card :=
        (card_powerset_filter_shiftFree_image_add m (m - s) _).symm
    _ = ((Finset.Icc (m + 1) (((n : ℤ) - s + m).toNat : ℤ)).powerset.filter
          (shiftFree m)).card := by
        rw [hshift]
    _ ≤ ∏ r ∈ Finset.Icc 1 m,
          ((cls ((n : ℤ) - s + m).toNat m r).powerset.filter
            (shiftFree m)).card :=
        card_powerset_filter_shiftFree_le_prod (Finset.Icc 1 m)
          (cls ((n : ℤ) - s + m).toNat m)
          (Finset.Icc (m + 1) (((n : ℤ) - s + m).toNat : ℤ))
          (Icc_subset_biUnion_cls hm)
    _ = ∏ r ∈ Finset.Icc 1 m,
          Nat.fib (((((n : ℤ) - s + m) - r) / m).toNat + 2) := by
        apply Finset.prod_congr rfl
        intro r _
        rw [card_powerset_filter_shiftFree_cls hm, hNz]

/-- `secondMinClass n m s` is bounded by the Fibonacci product over the
residue classes of the translated interval — a single shift (`m`)
suffices, since `shiftFree2 m s` implies `shiftFree m`. -/
theorem secondMinClass_card_le_prod_fib {n : ℕ} {m s : ℤ}
    (hm : 1 ≤ m) (hsn : s ≤ (n : ℤ)) :
    (secondMinClass n m s).card ≤
      ∏ r ∈ Finset.Icc 1 m,
        Nat.fib (((((n : ℤ) - s + m) - r) / m).toNat + 2) := by
  have hmono :
      (Finset.Icc (s + 1) (n : ℤ)).powerset.filter (shiftFree2 m s) ⊆
        (Finset.Icc (s + 1) (n : ℤ)).powerset.filter (shiftFree m) := by
    intro t ht
    rw [Finset.mem_filter] at ht ⊢
    exact ⟨ht.1, ht.2.1⟩
  exact (secondMinClass_card_le_shiftFree2.trans
    (Finset.card_le_card hmono)).trans
      (card_powerset_filter_shiftFree_Icc_le hm hsn)

/-- Per-class bound with no slack for empty progressions:
`fib (L+2) ≤ φ^(L + (1 if L > 0 else 0))`, since `fib 2 = 1 = φ⁰`. -/
theorem fib_add_two_le_goldenRatio_pow (L : ℕ) :
    (Nat.fib (L + 2) : ℝ) ≤
      Real.goldenRatio ^ (L + (if 0 < L then 1 else 0)) := by
  rcases Nat.eq_zero_or_pos L with rfl | hL
  · simp [Nat.fib_two]
  · have hite : L + (if 0 < L then (1 : ℕ) else 0) = L + 1 := by simp [hL]
    rw [hite]
    exact fib_le_goldenRatio_pow (L + 1)

/-- The residue classes that are actually nonempty inside the translated
interval `Icc (m+1) (n-s+m)` are exactly `r ∈ Icc 1 (min m (n-s))`:
class `r` contains an element iff `r + m ≤ n - s + m`, i.e. `r ≤ n - s`. -/
theorem filter_Icc_nonempty_cls {n : ℕ} {m s : ℤ} (hm : 1 ≤ m) :
    (Finset.Icc 1 m).filter
        (fun r => 0 < ((((n : ℤ) - s + m) - r) / m).toNat) =
      Finset.Icc 1 (min m ((n : ℤ) - s)) := by
  ext r
  simp only [Finset.mem_filter, Finset.mem_Icc, le_min_iff]
  have key : (0 < ((((n : ℤ) - s + m) - r) / m).toNat) ↔
      r ≤ (n : ℤ) - s := by
    rw [← Int.pos_iff_toNat_pos]
    constructor
    · intro h
      have h1 : (1 : ℤ) ≤ (((n : ℤ) - s + m) - r) / m := by omega
      have h2 := (Int.le_ediv_iff_mul_le (by omega : 0 < m)).mp h1
      omega
    · intro h
      have h1 : (1 : ℤ) ≤ (((n : ℤ) - s + m) - r) / m := by
        rw [Int.le_ediv_iff_mul_le (by omega : 0 < m)]
        omega
      omega
  rw [key]
  tauto

/-- **Main bound (all `s`).**  For `1 ≤ m`,

  `(secondMinClass n m s).card ≤ φ^((n-s).toNat + (min m (n-s)).toNat)`

as a real inequality.  The exponent is `(n-s) + #(nonempty classes)`.
When `s > n` the interval `Icc (s+1) n` is empty and the class has at most
one member, while `φ^e ≥ 1`. -/
theorem secondMinClass_card_le_goldenRatio {n : ℕ} {m s : ℤ} (hm : 1 ≤ m) :
    ((secondMinClass n m s).card : ℝ) ≤
      Real.goldenRatio ^
        (((n : ℤ) - s).toNat + (min m ((n : ℤ) - s)).toNat) := by
  rcases lt_or_ge (n : ℤ) s with hlt | hsn
  · have hempty : Finset.Icc (s + 1) (n : ℤ) = ∅ :=
      Finset.Icc_eq_empty_of_lt (show (n : ℤ) < s + 1 by omega)
    have hcard : (secondMinClass n m s).card ≤ 1 := by
      refine secondMinClass_card_le_shiftFree2.trans ?_
      rw [hempty]
      calc ((∅ : Finset ℤ).powerset.filter (shiftFree2 m s)).card
          ≤ (Finset.powerset (∅ : Finset ℤ)).card :=
            Finset.card_le_card (Finset.filter_subset _ _)
        _ = 1 := by rw [Finset.powerset_empty, Finset.card_singleton]
    calc ((secondMinClass n m s).card : ℝ)
        ≤ 1 := by exact_mod_cast hcard
      _ ≤ Real.goldenRatio ^
            (((n : ℤ) - s).toNat + (min m ((n : ℤ) - s)).toNat) :=
          one_le_pow₀ Real.one_lt_goldenRatio.le
  · have hC := secondMinClass_card_le_prod_fib hm hsn
    have hsum : ∑ r ∈ Finset.Icc 1 m,
          ((((n : ℤ) - s + m) - r) / m).toNat = ((n : ℤ) - s).toNat := by
      have hNz : ((((n : ℤ) - s + m).toNat : ℕ) : ℤ) = (n : ℤ) - s + m :=
        Int.toNat_of_nonneg (by omega)
      have h := sum_cls_card (n := ((n : ℤ) - s + m).toNat) hm
      rw [hNz, show (n : ℤ) - s + m - m = (n : ℤ) - s from by ring] at h
      exact h
    have hne : (Finset.Icc 1 m).filter
          (fun r => 0 < ((((n : ℤ) - s + m) - r) / m).toNat) =
        Finset.Icc 1 (min m ((n : ℤ) - s)) :=
      filter_Icc_nonempty_cls hm
    have hcard : (Finset.Icc 1 (min m ((n : ℤ) - s))).card =
        (min m ((n : ℤ) - s)).toNat := by
      rw [Int.card_Icc]
      congr 1
      omega
    calc ((secondMinClass n m s).card : ℝ)
        ≤ ∏ r ∈ Finset.Icc 1 m,
            (Nat.fib (((((n : ℤ) - s + m) - r) / m).toNat + 2) : ℝ) := by
          exact_mod_cast hC
      _ ≤ ∏ r ∈ Finset.Icc 1 m,
            Real.goldenRatio ^
              (((((n : ℤ) - s + m) - r) / m).toNat +
                (if 0 < ((((n : ℤ) - s + m) - r) / m).toNat then 1 else 0)) := by
          apply Finset.prod_le_prod₀
          · intro r _
            exact Nat.cast_nonneg _
          · intro r _
            exact fib_add_two_le_goldenRatio_pow _
      _ = Real.goldenRatio ^
            (((n : ℤ) - s).toNat + (min m ((n : ℤ) - s)).toNat) := by
          rw [Finset.prod_pow_eq_pow_sum]
          congr 1
          rw [Finset.sum_add_distrib, ← Finset.card_filter, hsum, hne, hcard]

/-- Coarser but cleaner form of the main bound: since
`min m (n-s) ≤ m`, one always has
`(secondMinClass n m s).card ≤ φ^((n-s) + m)`. -/
theorem secondMinClass_card_le_goldenRatio_add {n : ℕ} {m s : ℤ}
    (hm : 1 ≤ m) :
    ((secondMinClass n m s).card : ℝ) ≤
      Real.goldenRatio ^ (((n : ℤ) - s).toNat + m.toNat) := by
  refine (secondMinClass_card_le_goldenRatio hm).trans ?_
  apply pow_le_pow_right₀ Real.one_lt_goldenRatio.le
  have h : (min m ((n : ℤ) - s)).toNat ≤ m.toNat :=
    Int.toNat_le_toNat (min_le_left m _)
  omega

/-- **Regime `2s > n`.**  The `s`-shift constraint is vacuous, so the class
injects into the `m`-shift-free subsets of `Icc (s+1) n` *exactly* (no
`shiftFree2 → shiftFree` loss in the first step). -/
theorem secondMinClass_card_le_shiftFree_of_vacuous {n : ℕ} {m s : ℤ}
    (hns : (n : ℤ) < 2 * s) :
    (secondMinClass n m s).card ≤
      ((Finset.Icc (s + 1) (n : ℤ)).powerset.filter (shiftFree m)).card := by
  rw [← powerset_filter_shiftFree2_eq_of_vacuous hns]
  exact secondMinClass_card_le_shiftFree2

/-- **Summary bound per regime.**  For `2s > n` the same sharp exponent
applies — `(n-s) + min(m, n-s)` — while the intermediate family bound is
exact (`shiftFree2 = shiftFree` on the interval).  As noted in the module
docstring, `φ^(n-s)` alone cannot bound the class in this regime
(`2^(n-s) > φ^(n-s)` admissible subsets when `m > n-s`), so this is the
best exponent provable from the residue-class factorisation. -/
theorem secondMinClass_card_le_goldenRatio_of_vacuous {n : ℕ} {m s : ℤ}
    (hm : 1 ≤ m) (_hns : (n : ℤ) < 2 * s) :
    ((secondMinClass n m s).card : ℝ) ≤
      Real.goldenRatio ^
        (((n : ℤ) - s).toNat + (min m ((n : ℤ) - s)).toNat) :=
  secondMinClass_card_le_goldenRatio hm

end JSP000728
