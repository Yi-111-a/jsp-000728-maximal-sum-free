import JSPProblem.StairMatchSharp
import JSPProblem.NearDiagBound
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# JSP-000728 — the sharp ℝ-form of the near-diagonal staircase bound

`StairMatchSharp.lean` records the staircase-matching bound in two
flavours: the integer form
`card ≤ 4^{|B|}·5^{Σ_B (L_r-1)}·2^{Σ_Λ (L_ρ+1)}`
(`card_powerset_filter_shiftFree2_Icc_le_stairMatchSharp`) and the
multiplied rate-`5/2` form
`card·2^{Σ_B (L_r-1)} ≤ 4^{|B|}·5^{Σ_B (L_r-1)}·2^{Σ_Λ (L_ρ+1)}`
(`card_powerset_filter_shiftFree2_Icc_mul_two_pow_le_stairMatch`).
This module divides out the `2`-power and carries the bookkeeping
through to *explicit* exponents over ℝ:

* `card_powerset_filter_shiftFree2_Icc_le_stairMatchReal` — the sharp
  bound with the honest per-pair rate `5/2` charged to *half* the total
  rail budget:
  `card ≤ 4^{|B|}·(5/2)^{((n-m)₊+|B|)/2}·2^{|Λ|·(((n-m+k-1)/m)₊+1)}`.
  The `5/2`-exponent is `sum_L_bases_le_div_two`
  (`Σ_B L ≤ ((n-m)₊ + |B|)/2`); the `|Λ|` leftover rails, each of length
  at most `((n-m+k-1)/m)₊` (`sum_L_leftover_le_card_mul`), carry the
  `2`-rate.
* `card_powerset_filter_shiftFree2_Icc_le_stairMatchRealClosed` — the
  fully explicit closed form
  `card ≤ 4^{(m-k)₊}·(5/2)^{((n-m)₊+(m-k)₊)/2}·2^{k₊·((n/m)₊+1)}`
  (i.e. a `√(5/2)` rate on the `≈ n` matched elements times a `2`-rate
  on the `≈ k·n/m` leftover elements).
* `secondMinClass_card_le_stairMatchReal` /
  `secondMinClass_card_le_stairMatchRealClosed` — the per-cell
  corollaries via `secondMinClass_card_le_stairProd_conditional`.
* `stairCellRate m k = √(5/2)·2^{k/m}` and
  `secondMinClass_card_le_stairCellRate_pow` — the `C·ρⁿ` packaging for
  `m ≤ n`: `(secondMinClass n m (m+k)).card ≤
  4^{(m-k)₊}·2^{k₊}·(stairCellRate m k)ⁿ`, with
  `stairCellRate m k ≤ √10` (`stairCellRate_le_sqrt_ten`) and
  `log₂(stairCellRate m k) = k/m + log₂(5/2)/2 ≈ 0.66 + k/m`.
-/

namespace JSP000728

/-- **The sharp near-diagonal bound over ℝ (set-exponent form).**
Dividing the multiplied bound
`card·2^{Σ_B(L_r-1)} ≤ 4^{|B|}·5^{Σ_B(L_r-1)}·2^{Σ_Λ(L_ρ+1)}` by
`2^{Σ_B(L_r-1)}` gives the honest per-pair rate `5/2`; substituting
`Σ_B (L_r-1) ≤ Σ_B L ≤ ((n-m)₊ + |B|)/2` (`sum_L_bases_le_div_two`) and
`Σ_Λ (L_ρ+1) ≤ |Λ|·(((n-m+k-1)/m)₊ + 1)` (`sum_L_leftover_le_card_mul`):

  `card ≤ 4^{|B|}·(5/2)^{((n-m)₊+|B|)/2}·2^{|Λ|·(((n-m+k-1)/m)₊+1)}` —

i.e. the `5/2`-rate is charged to only *half* the `Icc (m+1) n`
elements, the rest paying the `4`-per-pair and `2`-per-leftover-rail
overheads. -/
theorem card_powerset_filter_shiftFree2_Icc_le_stairMatchReal {n : ℕ}
    {m k : ℤ} (hm : 1 ≤ m) (hk : 1 ≤ k) (hkm : k < m) :
    (((Finset.Icc (m + 1) (n : ℤ)).powerset.filter
        (shiftFree2 m (m + k))).card : ℝ) ≤
      (4 : ℝ) ^ (stairBases m k).card *
        (5 / 2 : ℝ) ^
          ((((n : ℤ) - m).toNat + (stairBases m k).card) / 2) *
        (2 : ℝ) ^ ((stairLeftover m k).card *
          ((((n : ℤ) - (m - k + 1)) / m).toNat + 1)) := by
  have hprod := card_powerset_filter_shiftFree2_Icc_le_stairMatchProd
    (n := n) hm hk hkm
  have hA : (∏ r ∈ stairBases m k,
          ((stairSets (((n : ℤ) - r) / m).toNat).card : ℝ)) ≤
      ∏ r ∈ stairBases m k,
        4 * (5 / 2 : ℝ) ^ ((((n : ℤ) - r) / m).toNat - 1) := by
    apply Finset.prod_le_prod₀
    · intro r _
      exact Nat.cast_nonneg _
    · intro r _
      exact stairSets_card_le_four_mul_five_div_two_pow _
  have hB : (∏ ρ ∈ stairLeftover m k,
          (Nat.fib ((((n : ℤ) - ρ) / m).toNat + 2) : ℝ)) ≤
      ∏ ρ ∈ stairLeftover m k,
        (2 : ℝ) ^ ((((n : ℤ) - ρ) / m).toNat + 1) := by
    apply Finset.prod_le_prod₀
    · intro ρ _
      exact Nat.cast_nonneg _
    · intro ρ _
      exact_mod_cast fib_add_two_le_two_pow' _
  have hAeq : (∏ r ∈ stairBases m k,
          4 * (5 / 2 : ℝ) ^ ((((n : ℤ) - r) / m).toNat - 1)) =
      (4 : ℝ) ^ (stairBases m k).card *
        (5 / 2 : ℝ) ^ (∑ r ∈ stairBases m k,
          ((((n : ℤ) - r) / m).toNat - 1)) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const,
      Finset.prod_pow_eq_pow_sum]
  have hBeq : (∏ ρ ∈ stairLeftover m k,
          (2 : ℝ) ^ ((((n : ℤ) - ρ) / m).toNat + 1)) =
      (2 : ℝ) ^ (∑ ρ ∈ stairLeftover m k,
        ((((n : ℤ) - ρ) / m).toNat + 1)) :=
    Finset.prod_pow_eq_pow_sum _ _ _
  -- exponent bookkeeping
  have hE : (∑ r ∈ stairBases m k, ((((n : ℤ) - r) / m).toNat - 1)) ≤
      (((n : ℤ) - m).toNat + (stairBases m k).card) / 2 :=
    (Finset.sum_le_sum fun r _ => Nat.sub_le _ _).trans
      (sum_L_bases_le_div_two (n := n) hm hk (le_of_lt hkm))
  have hG : (∑ ρ ∈ stairLeftover m k,
        ((((n : ℤ) - ρ) / m).toNat + 1)) ≤
      (stairLeftover m k).card *
        ((((n : ℤ) - (m - k + 1)) / m).toNat + 1) := by
    have hsum := sum_L_leftover_le_card_mul (n := n) (m := m) (k := k) hm
    calc (∑ ρ ∈ stairLeftover m k, ((((n : ℤ) - ρ) / m).toNat + 1))
        = (∑ ρ ∈ stairLeftover m k, (((n : ℤ) - ρ) / m).toNat) +
            (stairLeftover m k).card := by
          rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul,
            mul_one]
      _ ≤ (stairLeftover m k).card *
              (((n : ℤ) - (m - k + 1)) / m).toNat +
            (stairLeftover m k).card := by omega
      _ = (stairLeftover m k).card *
            ((((n : ℤ) - (m - k + 1)) / m).toNat + 1) := by ring
  calc (((Finset.Icc (m + 1) (n : ℤ)).powerset.filter
          (shiftFree2 m (m + k))).card : ℝ)
      ≤ (∏ r ∈ stairBases m k,
            ((stairSets (((n : ℤ) - r) / m).toNat).card : ℝ)) *
          ∏ ρ ∈ stairLeftover m k,
            (Nat.fib ((((n : ℤ) - ρ) / m).toNat + 2) : ℝ) := by
        exact_mod_cast hprod
    _ ≤ (∏ r ∈ stairBases m k,
            4 * (5 / 2 : ℝ) ^ ((((n : ℤ) - r) / m).toNat - 1)) *
          ∏ ρ ∈ stairLeftover m k,
            (2 : ℝ) ^ ((((n : ℤ) - ρ) / m).toNat + 1) :=
        mul_le_mul hA hB
          (Finset.prod_nonneg fun ρ _ => Nat.cast_nonneg _)
          (Finset.prod_nonneg fun r _ =>
            mul_nonneg (by norm_num) (pow_nonneg (by norm_num) _))
    _ = (4 : ℝ) ^ (stairBases m k).card *
          (5 / 2 : ℝ) ^ (∑ r ∈ stairBases m k,
            ((((n : ℤ) - r) / m).toNat - 1)) *
          (2 : ℝ) ^ (∑ ρ ∈ stairLeftover m k,
            ((((n : ℤ) - ρ) / m).toNat + 1)) := by
        rw [hAeq, hBeq]
    _ ≤ (4 : ℝ) ^ (stairBases m k).card *
          (5 / 2 : ℝ) ^
            ((((n : ℤ) - m).toNat + (stairBases m k).card) / 2) *
          (2 : ℝ) ^ ((stairLeftover m k).card *
            ((((n : ℤ) - (m - k + 1)) / m).toNat + 1)) :=
        mul_le_mul
          (mul_le_mul (le_refl _)
            (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 5 / 2) hE)
            (pow_nonneg (by norm_num : (0 : ℝ) ≤ 5 / 2) _)
            (pow_nonneg (by norm_num : (0 : ℝ) ≤ 4) _))
          (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hG)
          (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
          (mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 4) _)
            (pow_nonneg (by norm_num : (0 : ℝ) ≤ 5 / 2) _))

/-- **The sharp near-diagonal bound over ℝ (closed form).**
Substituting the cardinality bounds `|B| ≤ (m-k)₊`
(`stairBases_card_le`), `|Λ| ≤ k₊` (`stairLeftover_card_le`) and the
uniform leftover-rail length `((n-m+k-1)/m)₊ ≤ (n/m)₊` into
`card_powerset_filter_shiftFree2_Icc_le_stairMatchReal`:

  `card ≤ 4^{(m-k)₊}·(5/2)^{((n-m)₊+(m-k)₊)/2}·2^{k₊·((n/m)₊+1)}` —

a `√(5/2)` per-element rate on the matched bulk plus a `2`-rate on the
`≈ k·n/m` leftover elements. -/
theorem card_powerset_filter_shiftFree2_Icc_le_stairMatchRealClosed
    {n : ℕ} {m k : ℤ} (hm : 1 ≤ m) (hk : 1 ≤ k) (hkm : k < m) :
    (((Finset.Icc (m + 1) (n : ℤ)).powerset.filter
        (shiftFree2 m (m + k))).card : ℝ) ≤
      (4 : ℝ) ^ (m - k).toNat *
        (5 / 2 : ℝ) ^
          ((((n : ℤ) - m).toNat + (m - k).toNat) / 2) *
        (2 : ℝ) ^ (k.toNat * (((n : ℤ) / m).toNat + 1)) := by
  have hmain := card_powerset_filter_shiftFree2_Icc_le_stairMatchReal
    (n := n) hm hk hkm
  have hB : (stairBases m k).card ≤ (m - k).toNat := stairBases_card_le
  have hL : (stairLeftover m k).card ≤ k.toNat := stairLeftover_card_le
  have hX : (((n : ℤ) - (m - k + 1)) / m).toNat ≤ ((n : ℤ) / m).toNat :=
    Int.toNat_le_toNat (Int.ediv_le_ediv (by omega) (by omega))
  have hG2 : (stairLeftover m k).card *
        ((((n : ℤ) - (m - k + 1)) / m).toNat + 1) ≤
      k.toNat * (((n : ℤ) / m).toNat + 1) :=
    Nat.mul_le_mul hL (by omega)
  have hE2 : (((n : ℤ) - m).toNat + (stairBases m k).card) / 2 ≤
      (((n : ℤ) - m).toNat + (m - k).toNat) / 2 := by omega
  exact hmain.trans
    (mul_le_mul
      (mul_le_mul
        (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) hB)
        (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 5 / 2) hE2)
        (pow_nonneg (by norm_num : (0 : ℝ) ≤ 5 / 2) _)
        (pow_nonneg (by norm_num : (0 : ℝ) ≤ 4) _))
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hG2)
      (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
      (mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 4) _)
        (pow_nonneg (by norm_num : (0 : ℝ) ≤ 5 / 2) _)))

/-- **Per-cell corollary over ℝ.**  `secondMinClass n m (m+k)` injects
into the double-shift-free subsets of `Icc (m+1) n`
(`secondMinClass_card_le_stairProd_conditional`), so the sharp
`5/2`-rate bound applies per cell:
`(secondMinClass n m (m+k)).card ≤
4^{|B|}·(5/2)^{((n-m)₊+|B|)/2}·2^{|Λ|·(((n-m+k-1)/m)₊+1)}`. -/
theorem secondMinClass_card_le_stairMatchReal {n : ℕ} {m k : ℤ}
    (hm : 1 ≤ m) (hk : 1 ≤ k) (hkm : k < m) :
    ((secondMinClass n m (m + k)).card : ℝ) ≤
      (4 : ℝ) ^ (stairBases m k).card *
        (5 / 2 : ℝ) ^
          ((((n : ℤ) - m).toNat + (stairBases m k).card) / 2) *
        (2 : ℝ) ^ ((stairLeftover m k).card *
          ((((n : ℤ) - (m - k + 1)) / m).toNat + 1)) := by
  have hle := secondMinClass_card_le_stairProd_conditional
    (n := n) (m := m) (s := m + k) (by omega)
    (le_refl ((Finset.Icc (m + 1) (n : ℤ)).powerset.filter
      (shiftFree2 m (m + k))).card)
  exact (Nat.cast_le.mpr hle).trans
    (card_powerset_filter_shiftFree2_Icc_le_stairMatchReal
      (n := n) hm hk hkm)

/-- **Per-cell corollary, closed form.**  The explicit bound
`4^{(m-k)₊}·(5/2)^{((n-m)₊+(m-k)₊)/2}·2^{k₊·((n/m)₊+1)}` transported to
`secondMinClass n m (m+k)` via the closed ℝ bound. -/
theorem secondMinClass_card_le_stairMatchRealClosed {n : ℕ} {m k : ℤ}
    (hm : 1 ≤ m) (hk : 1 ≤ k) (hkm : k < m) :
    ((secondMinClass n m (m + k)).card : ℝ) ≤
      (4 : ℝ) ^ (m - k).toNat *
        (5 / 2 : ℝ) ^
          ((((n : ℤ) - m).toNat + (m - k).toNat) / 2) *
        (2 : ℝ) ^ (k.toNat * (((n : ℤ) / m).toNat + 1)) := by
  have hle := secondMinClass_card_le_stairProd_conditional
    (n := n) (m := m) (s := m + k) (by omega)
    (le_refl ((Finset.Icc (m + 1) (n : ℤ)).powerset.filter
      (shiftFree2 m (m + k))).card)
  exact (Nat.cast_le.mpr hle).trans
    (card_powerset_filter_shiftFree2_Icc_le_stairMatchRealClosed
      (n := n) hm hk hkm)

/-! ### The `C·ρⁿ` packaging -/

/-- **The per-element rate of the near-diagonal cell `s = m + k`.**
`stairCellRate m k = √(5/2)·2^{k/m}`: the matched bulk of
`Icc (m+1) n` pays the per-element rate `√(5/2)` (the `5/2`-rate on
half the elements) and the `|Λ| ≤ k` leftover rails of length `≤ n/m`
contribute `2^{k·n/m} = (2^{k/m})ⁿ`.  For `0 < k < m` the rate lies in
`(√(5/2), √10)`, i.e.
`log₂(stairCellRate) = k/m + log₂(5/2)/2 ≈ 0.66 + k/m`. -/
noncomputable def stairCellRate (m k : ℤ) : ℝ :=
  Real.sqrt (5 / 2) * (2 : ℝ) ^ ((k : ℝ) / m)

/-- The cell rate is at most `√10 ≈ 3.162`: for `k ≤ m` the `2^{k/m}`
factor is at most `2`. -/
theorem stairCellRate_le_sqrt_ten {m k : ℤ} (hm : 1 ≤ m) (hkm : k ≤ m) :
    stairCellRate m k ≤ Real.sqrt 10 := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hdiv : (k : ℝ) / m ≤ 1 := by
    rw [div_le_one hmR]
    exact_mod_cast hkm
  have h2 : (2 : ℝ) ^ ((k : ℝ) / m) ≤ 2 := by
    calc (2 : ℝ) ^ ((k : ℝ) / m) ≤ (2 : ℝ) ^ (1 : ℝ) :=
          (Real.rpow_le_rpow_left_iff (by norm_num)).mpr hdiv
      _ = 2 := Real.rpow_one 2
  have hsqrt : Real.sqrt (5 / 2) * 2 = Real.sqrt 10 := by
    have h4 : Real.sqrt 4 = 2 := by
      rw [show (4 : ℝ) = 2 * 2 by norm_num,
        Real.sqrt_mul_self (by norm_num)]
    have h10 : Real.sqrt 10 = Real.sqrt (5 / 2) * Real.sqrt 4 := by
      rw [show (10 : ℝ) = 5 / 2 * 4 by norm_num,
        Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 5 / 2)]
    rw [h10, h4]
  calc stairCellRate m k
      = Real.sqrt (5 / 2) * (2 : ℝ) ^ ((k : ℝ) / m) := rfl
    _ ≤ Real.sqrt (5 / 2) * 2 :=
        mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg _)
    _ = Real.sqrt 10 := hsqrt

/-- **The `C·ρⁿ` per-cell bound.**  For `m ≤ n` the closed bound
`4^{(m-k)₊}·(5/2)^{((n-m)₊+(m-k)₊)/2}·2^{k₊·((n/m)₊+1)}` collapses to a
pure exponential: `(5/2)^{((n-k)₊)/2} ≤ (√(5/2))ⁿ` and
`2^{k₊·((n/m)₊+1)} ≤ 2^{k₊}·(2^{k/m})ⁿ`, giving

  `(secondMinClass n m (m+k)).card ≤
    4^{(m-k)₊}·2^{k₊}·(stairCellRate m k)ⁿ`. -/
theorem secondMinClass_card_le_stairCellRate_pow {n : ℕ} {m k : ℤ}
    (hm : 1 ≤ m) (hk : 1 ≤ k) (hkm : k < m) (hmn : m ≤ (n : ℤ)) :
    ((secondMinClass n m (m + k)).card : ℝ) ≤
      (4 : ℝ) ^ (m - k).toNat * (2 : ℝ) ^ k.toNat *
        stairCellRate m k ^ n := by
  have hclosed :=
    card_powerset_filter_shiftFree2_Icc_le_stairMatchRealClosed
      (n := n) hm hk hkm
  have hle := secondMinClass_card_le_stairProd_conditional
    (n := n) (m := m) (s := m + k) (by omega)
    (le_refl ((Finset.Icc (m + 1) (n : ℤ)).powerset.filter
      (shiftFree2 m (m + k))).card)
  -- exponent casts
  have htoNat : ∀ x : ℤ, 0 ≤ x → ((x.toNat : ℕ) : ℝ) = (x : ℝ) := by
    intro x hx
    exact_mod_cast Int.toNat_of_nonneg hx
  have hkR : ((k.toNat : ℕ) : ℝ) = (k : ℝ) :=
    htoNat k (by omega)
  have hk0 : (0 : ℝ) ≤ k := by exact_mod_cast (by omega : 0 ≤ k)
  have hAn : ((((n : ℤ) - m).toNat + (m - k).toNat : ℕ) : ℝ) ≤
      (n : ℝ) := by
    rw [Nat.cast_add, htoNat _ (by omega), htoNat _ (by omega)]
    push_cast
    linarith
  have hE3 : (((((n : ℤ) - m).toNat + (m - k).toNat) / 2 : ℕ) : ℝ) ≤
      (n : ℝ) / 2 :=
    Nat.cast_div_le.trans (by linarith)
  have hq0 : (0 : ℤ) ≤ (n : ℤ) / m :=
    Int.ediv_nonneg (Nat.cast_nonneg n) (by omega)
  have hqR : ((((n : ℤ) / m).toNat : ℕ) : ℝ) ≤ (n : ℝ) / m := by
    rw [htoNat _ hq0, le_div_iff₀ (by exact_mod_cast hm : (0 : ℝ) < m)]
    have h2 : (n : ℤ) / m * m ≤ (n : ℤ) :=
      Int.ediv_mul_le (n : ℤ) (by omega : m ≠ 0)
    exact_mod_cast h2
  have hE4 : ((k.toNat * (((n : ℤ) / m).toNat + 1) : ℕ) : ℝ) ≤
      (k : ℝ) * ((n : ℝ) / m + 1) := by
    rw [Nat.cast_mul, hkR]
    have h1 : ((((n : ℤ) / m).toNat + 1 : ℕ) : ℝ) ≤ (n : ℝ) / m + 1 := by
      rw [Nat.cast_add, Nat.cast_one]
      linarith
    exact mul_le_mul_of_nonneg_left h1 hk0
  -- the two power bounds
  have hsqrt5 : (5 / 2 : ℝ) ^ ((n : ℝ) / 2) =
      Real.sqrt (5 / 2) ^ n := by
    have e1 : (n : ℝ) / 2 = (1 / 2 : ℝ) * n := by ring
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, e1,
      Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 5 / 2)]
  have hpow5 : (5 / 2 : ℝ) ^
        ((((n : ℤ) - m).toNat + (m - k).toNat) / 2) ≤
      Real.sqrt (5 / 2) ^ n := by
    calc (5 / 2 : ℝ) ^ ((((n : ℤ) - m).toNat + (m - k).toNat) / 2)
        = (5 / 2 : ℝ) ^
            (((((n : ℤ) - m).toNat + (m - k).toNat) / 2 : ℕ) : ℝ) :=
          (Real.rpow_natCast _ _).symm
      _ ≤ (5 / 2 : ℝ) ^ ((n : ℝ) / 2) :=
          (Real.rpow_le_rpow_left_iff
            (by norm_num : (1 : ℝ) < 5 / 2)).mpr hE3
      _ = Real.sqrt (5 / 2) ^ n := hsqrt5
  have hfac : (2 : ℝ) ^ ((k : ℝ) / m * n) =
      ((2 : ℝ) ^ ((k : ℝ) / m)) ^ n := by
    rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
  have hk2 : (2 : ℝ) ^ (k : ℝ) = (2 : ℝ) ^ k.toNat := by
    rw [← hkR, Real.rpow_natCast]
  have hpow2 : (2 : ℝ) ^ (k.toNat * (((n : ℤ) / m).toNat + 1)) ≤
      ((2 : ℝ) ^ ((k : ℝ) / m)) ^ n * (2 : ℝ) ^ k.toNat := by
    calc (2 : ℝ) ^ (k.toNat * (((n : ℤ) / m).toNat + 1))
        = (2 : ℝ) ^
            ((k.toNat * (((n : ℤ) / m).toNat + 1) : ℕ) : ℝ) :=
          (Real.rpow_natCast _ _).symm
      _ ≤ (2 : ℝ) ^ ((k : ℝ) * ((n : ℝ) / m + 1)) :=
          (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mpr
            hE4
      _ = (2 : ℝ) ^ ((k : ℝ) / m * n + k) := by
          congr 1
          ring
      _ = (2 : ℝ) ^ ((k : ℝ) / m * n) * (2 : ℝ) ^ (k : ℝ) :=
          Real.rpow_add (by norm_num) _ _
      _ = ((2 : ℝ) ^ ((k : ℝ) / m)) ^ n * (2 : ℝ) ^ k.toNat := by
          rw [hfac, hk2]
  calc ((secondMinClass n m (m + k)).card : ℝ)
      ≤ (((Finset.Icc (m + 1) (n : ℤ)).powerset.filter
          (shiftFree2 m (m + k))).card : ℝ) := by
        exact_mod_cast hle
    _ ≤ (4 : ℝ) ^ (m - k).toNat *
          (5 / 2 : ℝ) ^
            ((((n : ℤ) - m).toNat + (m - k).toNat) / 2) *
          (2 : ℝ) ^ (k.toNat * (((n : ℤ) / m).toNat + 1)) := hclosed
    _ ≤ (4 : ℝ) ^ (m - k).toNat * Real.sqrt (5 / 2) ^ n *
          (((2 : ℝ) ^ ((k : ℝ) / m)) ^ n * (2 : ℝ) ^ k.toNat) :=
        mul_le_mul
          (mul_le_mul (le_refl _) hpow5
            (pow_nonneg (by norm_num : (0 : ℝ) ≤ 5 / 2) _)
            (pow_nonneg (by norm_num : (0 : ℝ) ≤ 4) _))
          hpow2
          (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
          (mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 4) _)
            (pow_nonneg (Real.sqrt_nonneg _) _))
    _ = (4 : ℝ) ^ (m - k).toNat * (2 : ℝ) ^ k.toNat *
          stairCellRate m k ^ n := by
        unfold stairCellRate
        rw [mul_pow]
        ring

end JSP000728
