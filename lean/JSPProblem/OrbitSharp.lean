import JSPProblem.CellAssembly
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

/-!
# JSP-000728 — sharpened orbit/stair constants and the `111/160` assembly

This file sharpens the two engines of `CellAssembly.lean` and reassembles
the small-minimum frontier at the strictly smaller exponent
`111/160 = 0.69375 < 347/500 = 0.694`.

* `secondMinClass_card_le_orbit_sharp` — the orbit-strip bound with the
  exact worst-case coefficient `1777/2700` (attained by `c = 3` orbits)
  in place of the rounded `33/50`:

    `card ≤ C · 2^{s/6 + (1777/2700)·(n+s)}`

  where `C = (5/4)²·(1+√2)²⁴·φ³⁵` as before.  The `(n+s)` charging is
  genuine for this method: `Σ_O (L_O + 1) ≤ (n+s)/c` per orbit of length
  `c`, matching the uniform `(L+1)·g` bound almost exactly, so the
  improvement here comes from the bookkeeping `(32/25)·⌊c/2⌋·g +
  (25/36)·(c%2)·g ≤ (1777/2700)·s` instead of `≤ (33/50)·s`.

* `secondMinClass_card_le_stair_sharp` — the staircase-matching bound
  with the wider regime `40·k ≤ m` (was `50·k ≤ m`):

    `card ≤ (25/4) · 2^{(111/160)·n}`

  via `2|B| + (4/3)E_B + E_Λ ≤ 2n/3 + (n+k)/40 ≤ (2/3 + 161/6400)n`.

* `secondMinClass_card_le_cell_111_160` — the uniform per-cell bound
  `card ≤ cellSharpConst · 2^{(111/160)·n}` over the frontier `4m < n`:

  - `s = m`: the subsingleton `{m}`;
  - `s = 2m`: void (`m + m = 2m`);
  - `40k ≤ m` (k = s−m): the `D = 40` staircase bound;
  - `m < 40k` and `1000k < n`: `s < 41k < 41n/1000`, and the orbit bound
    gives `s/6 + (1777/2700)(n+s) ≤ (41/6000 + 1777·1041/2700000)n
    < (111/160)n`;
  - `m < 40k` and `1000k ≥ n`: the golden-ratio bound `φ^{n−k}` with
    `(25/36)·(999/1000) = 111/160` exactly.

* `smallMinBound_111_160`, `eventualRatioUpper_111_160` — the packaged
  `SmallMinBound (111/160)` and the headline
  `EventualRatioUpper (max (111/160) (1/2))`.
-/

namespace JSP000728

/-! ### Sharpened orbit bound -/

/-- **Sharpened closed orbit bound.**  For `1 ≤ m < s` the second-minimum
class is bounded by

  `card ≤ C · 2^{s/6 + (1777/2700)·(n+s)}`

with `C = (5/4)²·(1+√2)²⁴·φ³⁵`.  Same proof skeleton as
`secondMinClass_card_le_orbit_closed` but with the exact worst-case
bookkeeping: for even `c` the rate is `16/25` and for odd `c ≥ 3` it is
`16/25 + 49/(900·c) ≤ 1777/2700` (attained at `c = 3`, `g = s/3`). -/
theorem secondMinClass_card_le_orbit_sharp {n : ℕ} {m s : ℤ}
    (hm : 1 ≤ m) (hms : m < s) :
    ((secondMinClass n m s).card : ℝ) ≤
      ((5 / 4 : ℝ) ^ 2 * (1 + Real.sqrt 2) ^ 24 * Real.goldenRatio ^ 35) *
        (2 : ℝ) ^ ((1 / 6 : ℝ) * s + (1777 / 2700 : ℝ) * ((n : ℝ) + s)) := by
  have hs1 : (1 : ℤ) ≤ s := le_trans hm hms.le
  have hspos : (0 : ℤ) < s := by omega
  set L := (((n : ℤ) - 1) / s).toNat with hLdef
  set c := orbitLen m s with hcdef
  set g := Int.gcd s m with hgdef
  -- The orbit bound.
  have hcard0 : ((secondMinClass n m s).card : ℝ) ≤
      (((Finset.Icc (s + 1) (n : ℤ)).powerset.filter (shiftFree2 m s)).card : ℝ) := by
    exact_mod_cast secondMinClass_card_le_shiftFree2
  have hcard := hcard0.trans
    (card_powerset_filter_shiftFree2_Icc_le_orbitPhi (n := n) hm hms)
  rw [← hLdef, ← hcdef, ← hgdef] at hcard
  -- Factor the powers.
  have hfac : (5 / 4 * (1 + Real.sqrt 2) ^ (L + 1)) ^ (c / 2 * g) *
        (Real.goldenRatio ^ (L + 1)) ^ (c % 2 * g) =
      (5 / 4 : ℝ) ^ (c / 2 * g) *
        (1 + Real.sqrt 2) ^ ((L + 1) * (c / 2 * g)) *
        Real.goldenRatio ^ ((L + 1) * (c % 2 * g)) := by
    rw [mul_pow, ← pow_mul (1 + Real.sqrt 2) (L + 1) (c / 2 * g),
        ← pow_mul Real.goldenRatio (L + 1) (c % 2 * g)]
  -- Bound the three factors.
  have hA := five_four_pow_le_two_rpow (c / 2 * g)
  have hB := pell_pow_le_two_rpow ((L + 1) * (c / 2 * g))
  have hC := goldenRatio_pow_le_two_rpow ((L + 1) * (c % 2 * g))
  -- gcd–orbitLen bookkeeping in ℕ.
  have hcg : c * g = s.toNat := by
    have h' := gcd_mul_orbitLen (m := m) hs1
    rw [← hcdef, ← hgdef] at h'
    have h3 : ((g : ℤ) * (c : ℤ)) = (s.toNat : ℤ) := by
      rw [h', Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ s)]
    rw [Nat.mul_comm c g]
    exact_mod_cast h3
  have hg_le : g ≤ m.toNat := by
    have hdvd : (Int.gcd s m : ℤ) ∣ m := Int.gcd_dvd_right s m
    obtain ⟨t, ht⟩ := hdvd
    rw [← hgdef] at ht
    have hgm : g * t.natAbs = m.natAbs := by
      have e := congrArg Int.natAbs ht
      rw [Int.natAbs_mul, Int.natAbs_natCast] at e
      exact e.symm
    have htm : m.toNat = m.natAbs := by
      have e1 : ((m.toNat : ℤ)) = m := Int.toNat_of_nonneg (by omega)
      have e2 : ((m.natAbs : ℤ)) = m := Int.natAbs_of_nonneg (by omega)
      exact_mod_cast e1.trans e2.symm
    rw [htm, ← hgm]
    apply Nat.le_mul_of_pos_right
    rcases Nat.eq_zero_or_pos t.natAbs with h0 | hpos
    · have ht0 : t = 0 := Int.natAbs_eq_zero.mp h0
      rw [ht0] at ht
      simp at ht
      omega
    · exact hpos
  have hst : m.toNat < s.toNat := by
    have e1 : ((m.toNat : ℤ)) = m := Int.toNat_of_nonneg (by omega)
    have e2 : ((s.toNat : ℤ)) = s := Int.toNat_of_nonneg (by omega)
    omega
  -- `2·(c/2·g) ≤ c·g = s`, i.e. `P ≤ s/2`.
  have hP : 2 * (c / 2 * g) ≤ s.toNat := by
    have h : (2 * (c / 2)) * g ≤ c * g :=
      Nat.mul_le_mul_right g (by omega : 2 * (c / 2) ≤ c)
    rw [hcg] at h
    have h2 : 2 * (c / 2 * g) = (2 * (c / 2)) * g := by ring
    omega
  -- `c ≥ 2` since `c = 1` would force `s | m`.
  have hc2 : 2 ≤ c := by
    have hc1 : 1 ≤ c := orbitLen_pos hm hs1
    rcases Nat.lt_or_ge c 2 with hlt | hge
    · interval_cases c
      omega
    · exact hge
  -- If `c` is odd then `c ≥ 3` and `2·(c/2·g) = s - g`.
  have hc_odd : c % 2 = 1 → 3 ≤ c ∧ 2 * (c / 2 * g) = s.toNat - g := by
    intro hmod
    refine ⟨by omega, ?_⟩
    have h1 : 2 * (c / 2 * g) = (2 * (c / 2)) * g := by ring
    have h2 : 2 * (c / 2) = c - 1 := by omega
    rw [h1, h2, Nat.sub_mul, one_mul, hcg]
  -- `(L+1)·s ≤ n+s` as a real inequality.
  have hLs' : (((L : ℕ) : ℤ) + 1) * s ≤ (n : ℤ) + s := by
    by_cases hdiv : (0 : ℤ) ≤ ((n : ℤ) - 1) / s
    · have hL_eq : ((L : ℤ)) = ((n : ℤ) - 1) / s := by
        rw [hLdef]; exact Int.toNat_of_nonneg hdiv
      have hmul : ((n : ℤ) - 1) / s * s ≤ (n : ℤ) - 1 :=
        Int.ediv_mul_le _ (by omega : s ≠ 0)
      rw [← hL_eq] at hmul
      nlinarith
    · have hn1 : (n : ℤ) - 1 < 0 := by
        by_contra hge
        push Not at hge
        exact hdiv (Int.ediv_nonneg hge hspos.le)
      have hL0 : L = 0 := by
        rw [hLdef]
        apply Int.toNat_eq_zero.mpr
        have hle : ((n : ℤ) - 1) / s ≤ 0 / s :=
          Int.ediv_le_ediv hspos (by omega)
        rwa [Int.zero_ediv] at hle
      rw [hL0]
      push_cast
      nlinarith [Int.natCast_nonneg n]
  have hLs : ((L : ℝ) + 1) * (s : ℝ) ≤ (n : ℝ) + (s : ℝ) := by
    exact_mod_cast hLs'
  -- Exponent bound: `P/3 + (32/25)·(L+1)·P + (25/36)·(L+1)·G`
  --   `≤ s/6 + (1777/2700)·(L+1)·s`.
  have hE : ((c / 2 * g : ℕ) : ℝ) / 3 +
        (32 / 25 : ℝ) * ((L : ℝ) + 1) * (c / 2 * g : ℕ) +
        (25 / 36 : ℝ) * ((L : ℝ) + 1) * (c % 2 * g : ℕ) ≤
      (1 / 6 : ℝ) * s + (1777 / 2700 : ℝ) * ((L : ℝ) + 1) * (s : ℝ) := by
    have hsr : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hspos
    have hL1 : (0 : ℝ) ≤ (L : ℝ) + 1 := by positivity
    have hsr_eq : ((s.toNat : ℕ) : ℝ) = (s : ℝ) := by
      exact_mod_cast (Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ s))
    have hPr : ((c / 2 * g : ℕ) : ℝ) ≤ (s : ℝ) / 2 := by
      have e : ((2 * (c / 2 * g) : ℕ) : ℝ) ≤ (s.toNat : ℝ) := by
        exact_mod_cast hP
      rw [hsr_eq] at e
      push_cast at e
      rw [← Nat.cast_mul] at e
      linarith
    rcases Nat.mod_two_eq_zero_or_one c with hmod | hmod
    · have hG0 : ((c % 2 * g : ℕ) : ℝ) = 0 := by
        rw [hmod]; simp
      rw [hG0, mul_zero, add_zero]
      have hLP := mul_le_mul_of_nonneg_left hPr hL1
      have hLs0 := mul_nonneg hL1 hsr.le
      linarith
    · obtain ⟨hc3, hP2⟩ := hc_odd hmod
      have hGs : ((c % 2 * g : ℕ) : ℝ) = (g : ℝ) := by
        rw [hmod]; simp
      have hgr : (g : ℝ) ≤ (s : ℝ) / 3 := by
        have h3 : 3 * g ≤ s.toNat := by
          have := Nat.mul_le_mul_right g hc3
          omega
        have e : ((3 * g : ℕ) : ℝ) ≤ (s.toNat : ℝ) := by exact_mod_cast h3
        rw [hsr_eq] at e
        push_cast at e
        linarith
      have hPre : ((c / 2 * g : ℕ) : ℝ) = ((s : ℝ) - g) / 2 := by
        have hgs : g ≤ s.toNat := by
          have := Nat.le_mul_of_pos_left g (by omega : 0 < c)
          omega
        have e : ((2 * (c / 2 * g) : ℕ) : ℝ) =
            ((s.toNat - g : ℕ) : ℝ) := by exact_mod_cast hP2
        rw [Nat.cast_sub hgs] at e
        push_cast at e
        rw [hsr_eq, ← Nat.cast_mul] at e
        linarith
      rw [hGs]
      have hg0 : (0 : ℝ) ≤ (g : ℝ) := Nat.cast_nonneg _
      have hLP : ((L : ℝ) + 1) * ((c / 2 * g : ℕ) : ℝ) =
          ((L : ℝ) + 1) * (((s : ℝ) - (g : ℝ)) / 2) := by rw [hPre]
      -- The core inequality: `(16/25)(L+1)(s-g) + (25/36)(L+1)g`
      --   `≤ (1777/2700)(L+1)s`, since `g ≤ s/3` and
      --   `49/900 · (s/3) = 49/2700 · s`.
      have hX : (16 / 25 : ℝ) * ((L : ℝ) + 1) * ((s : ℝ) - (g : ℝ)) +
            (25 / 36 : ℝ) * ((L : ℝ) + 1) * (g : ℝ) ≤
          (1777 / 2700 : ℝ) * ((L : ℝ) + 1) * (s : ℝ) := by
        have e : (16 / 25 : ℝ) * ((L : ℝ) + 1) * ((s : ℝ) - (g : ℝ)) +
              (25 / 36 : ℝ) * ((L : ℝ) + 1) * (g : ℝ) =
            (16 / 25 : ℝ) * ((L : ℝ) + 1) * (s : ℝ) +
              (49 / 900 : ℝ) * ((L : ℝ) + 1) * (g : ℝ) := by ring
        rw [e]
        have h2 : (49 / 900 : ℝ) * ((L : ℝ) + 1) * (g : ℝ) ≤
            (49 / 900 : ℝ) * ((L : ℝ) + 1) * ((s : ℝ) / 3) :=
          mul_le_mul_of_nonneg_left hgr
            (by positivity : (0 : ℝ) ≤ (49 / 900) * ((L : ℝ) + 1))
        linarith [h2]
      linarith [hX, hLP, hPre, hg0]
  -- Combine.
  have hK : (0 : ℝ) ≤ (5 / 4) ^ 2 * (1 + Real.sqrt 2) ^ 24 *
      Real.goldenRatio ^ 35 := by positivity
  calc ((secondMinClass n m s).card : ℝ)
      ≤ (5 / 4 : ℝ) ^ (c / 2 * g) *
          (1 + Real.sqrt 2) ^ ((L + 1) * (c / 2 * g)) *
          Real.goldenRatio ^ ((L + 1) * (c % 2 * g)) :=
        hfac ▸ hcard
    _ ≤ ((5 / 4) ^ 2 *
            (2 : ℝ) ^ ((1 / 3 : ℝ) * ((c / 2 * g : ℕ) : ℝ))) *
          ((1 + Real.sqrt 2) ^ 24 *
            (2 : ℝ) ^ ((32 / 25 : ℝ) *
              (((L + 1) * (c / 2 * g) : ℕ) : ℝ))) *
          (Real.goldenRatio ^ 35 *
            (2 : ℝ) ^ ((25 / 36 : ℝ) *
              (((L + 1) * (c % 2 * g) : ℕ) : ℝ))) :=
        mul_le_mul (mul_le_mul hA hB
          (pow_nonneg (add_nonneg zero_le_one (Real.sqrt_nonneg 2)) _)
          (by positivity)) hC (pow_nonneg Real.goldenRatio_pos.le _)
          (by positivity)
    _ = ((5 / 4) ^ 2 * (1 + Real.sqrt 2) ^ 24 * Real.goldenRatio ^ 35) *
          ((2 : ℝ) ^ ((1 / 3 : ℝ) * ((c / 2 * g : ℕ) : ℝ)) *
            (2 : ℝ) ^ ((32 / 25 : ℝ) *
              (((L + 1) * (c / 2 * g) : ℕ) : ℝ)) *
            (2 : ℝ) ^ ((25 / 36 : ℝ) *
              (((L + 1) * (c % 2 * g) : ℕ) : ℝ))) := by ring
    _ = ((5 / 4) ^ 2 * (1 + Real.sqrt 2) ^ 24 * Real.goldenRatio ^ 35) *
          (2 : ℝ) ^ ((1 / 3 : ℝ) * ((c / 2 * g : ℕ) : ℝ) +
              (32 / 25 : ℝ) * (((L + 1) * (c / 2 * g) : ℕ) : ℝ) +
              (25 / 36 : ℝ) * (((L + 1) * (c % 2 * g) : ℕ) : ℝ)) := by
        rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2),
            ← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
    _ ≤ (5 / 4) ^ 2 * (1 + Real.sqrt 2) ^ 24 * Real.goldenRatio ^ 35 *
          (2 : ℝ) ^ ((1 / 6 : ℝ) * s + (1777 / 2700 : ℝ) * ((n : ℝ) + s)) := by
        apply mul_le_mul_of_nonneg_left _ hK
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
        have e1 : (((L + 1) * (c / 2 * g) : ℕ) : ℝ) =
            ((L : ℝ) + 1) * ((c / 2 * g : ℕ) : ℝ) := by
          rw [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
        have e2 : (((L + 1) * (c % 2 * g) : ℕ) : ℝ) =
            ((L : ℝ) + 1) * ((c % 2 * g : ℕ) : ℝ) := by
          rw [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
        rw [e1, e2]
        have hmono : (1777 / 2700 : ℝ) * ((L : ℝ) + 1) * (s : ℝ) ≤
            (1777 / 2700 : ℝ) * ((n : ℝ) + s) := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left hLs (by norm_num)
        linarith [hE, hmono]

/-! ### Sharpened staircase bound (`40·k ≤ m`) -/

/-- **Closed staircase bound, `D = 40`.**  For `s = m+k` with `1 ≤ k < m`
and `40·k ≤ m`, the sharp staircase-matching bound gives

  `card ≤ (25/4) · 2^{(111/160)·n}`.

The bookkeeping is `2·E_B + |B| ≤ (n−m)₊` for the base sum (charging the
`5`-power at the rate `5/2`) and `E_Λ' ≤ k·(n+k)/m ≤ (n+k)/40 ≤
161n/6400`, so the exponent is `2n/3 + 161n/6400 = (13283/19200)n <
(111/160)n`. -/
theorem secondMinClass_card_le_stair_sharp {n : ℕ} {m k : ℤ}
    (hm : 1 ≤ m) (hk : 1 ≤ k) (hkm : k < m) (hn : 4 * m < (n : ℤ))
    (hk40 : k * 40 ≤ m) :
    ((secondMinClass n m (m + k)).card : ℝ) ≤
      (25 / 4 : ℝ) * (2 : ℝ) ^ ((111 / 160 : ℝ) * (n : ℝ)) := by
  set B := stairBases m k with hBdef
  set Λ := stairLeftover m k with hΛdef
  set EB := ∑ r ∈ stairBases m k, ((((n : ℤ) - r) / m).toNat - 1) with hEBdef
  set EΛ := ∑ ρ ∈ stairLeftover m k,
      ((((n : ℤ) - ρ) / m).toNat + 1) with hEΛdef
  -- The multiplied bound, transported to the class.
  have hmul := card_powerset_filter_shiftFree2_Icc_mul_two_pow_le_stairMatch
    (n := n) hm hk hkm
  have hle : ((secondMinClass n m (m + k)).card : ℝ) ≤
      (((Finset.Icc (m + 1) (n : ℤ)).powerset.filter
        (shiftFree2 m (m + k))).card : ℝ) := by
    exact_mod_cast secondMinClass_card_le_stairProd_conditional
      (show m ≤ m + k by omega) (le_refl _)
  rw [← hBdef, ← hEBdef, ← hEΛdef] at hmul
  have hclass : ((secondMinClass n m (m + k)).card : ℝ) *
        (2 : ℝ) ^ (EB : ℕ) ≤
      ((4 ^ B.card * 5 ^ EB * 2 ^ EΛ : ℕ) : ℝ) := by
    have h2 : (0 : ℝ) ≤ (2 : ℝ) ^ (EB : ℕ) := by positivity
    refine (mul_le_mul_of_nonneg_right hle h2).trans ?_
    exact_mod_cast hmul
  -- Divide through by `2^{E_B}`:  `card ≤ 4^{|B|}·(5/2)^{E_B}·2^{E_Λ'}`.
  have hX : ((4 ^ B.card * 5 ^ EB * 2 ^ EΛ : ℕ) : ℝ) =
      ((4 : ℝ) ^ B.card * (5 / 2 : ℝ) ^ EB * (2 : ℝ) ^ EΛ) *
        (2 : ℝ) ^ EB := by
    have h52 : (5 / 2 : ℝ) ^ EB * (2 : ℝ) ^ EB = (5 : ℝ) ^ EB := by
      rw [← mul_pow]; norm_num
    push_cast
    rw [← h52]
    ring
  have hdiv : ((secondMinClass n m (m + k)).card : ℝ) ≤
      (4 : ℝ) ^ B.card * (5 / 2 : ℝ) ^ EB * (2 : ℝ) ^ EΛ := by
    have hpos : (0 : ℝ) < (2 : ℝ) ^ (EB : ℕ) := by positivity
    have h := (le_div_iff₀ hpos).mpr hclass
    rw [hX, mul_div_cancel_right₀ _ (ne_of_gt hpos)] at h
    exact h
  -- `(5/2)^{E_B} ≤ (5/2)²·2^{(4/3)·E_B}` and `4^{|B|} = 2^{2|B|}`.
  have h52b := five_two_pow_le_two_rpow EB
  have h4 : (4 : ℝ) ^ B.card = (2 : ℝ) ^ (2 * (B.card : ℝ)) := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) by norm_num, ← pow_mul]
    rw [← Real.rpow_natCast]
    congr 1
    push_cast
    ring
  -- Base-sum bookkeeping: `2·E_B + |B| ≤ (n-m)₊`.
  have hBcard : 2 * B.card ≤ m.toNat := by
    rw [hBdef]
    exact stairBases_card_le_half hm hk hkm.le
  have hΛcard : Λ.card ≤ k.toNat := by
    rw [hΛdef]
    exact stairLeftover_card_le
  have hSB : ∀ r ∈ B, 1 ≤ (((n : ℤ) - r) / m).toNat := by
    intro r hr
    rw [hBdef, mem_stairBases] at hr
    obtain ⟨hr1, hr2, -⟩ := hr
    have hle1 : (1 : ℤ) ≤ ((n : ℤ) - r) / m := by
      have : m ≤ (n : ℤ) - r := by omega
      have := Int.ediv_le_ediv hm this
      rwa [Int.ediv_self (by omega : m ≠ 0)] at this
    have htoNat : (((((n : ℤ) - r) / m).toNat : ℕ) : ℤ) = ((n : ℤ) - r) / m :=
      Int.toNat_of_nonneg (by omega)
    omega
  have hSBsum : (∑ r ∈ B, (((n : ℤ) - r) / m).toNat) =
      EB + B.card := by
    have h1 : ∑ r ∈ B, (((n : ℤ) - r) / m).toNat =
        ∑ r ∈ B, (((((n : ℤ) - r) / m).toNat - 1) + 1) := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [Nat.sub_add_cancel (hSB r hr)]
    rw [h1, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]
  have hEB2 : 2 * EB + B.card ≤ ((n : ℤ) - m).toNat := by
    have h := sum_L_bases_le (n := n) hm hk hkm.le
    rw [← hBdef] at h
    rw [hSBsum] at h
    have hΛpos : 0 ≤ ∑ ρ ∈ stairLeftover m k, (((n : ℤ) - ρ) / m).toNat :=
      Nat.zero_le _
    omega
  -- Leftover bookkeeping: `E_Λ' ≤ k·(n+k)/m`.
  set Lmax := (((n : ℤ) - (m - k + 1)) / m).toNat with hLmax
  have hEΛle : EΛ ≤ Λ.card * (Lmax + 1) := by
    calc EΛ = ∑ ρ ∈ Λ, ((((n : ℤ) - ρ) / m).toNat + 1) := by
          rw [hEΛdef, hΛdef]
      _ ≤ ∑ _ρ ∈ Λ, (Lmax + 1) := by
          apply Finset.sum_le_sum
          intro ρ hρ
          rw [hΛdef] at hρ
          exact Nat.succ_le_succ (stair_L_leftover_le hm hρ)
      _ = Λ.card * (Lmax + 1) := by rw [Finset.sum_const, smul_eq_mul]
  -- Real conversions.
  have hmr : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hnr : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hnr_m : ((m : ℝ)) ≤ (n : ℝ) / 4 := by
    have : (4 : ℝ) * (m : ℝ) < (n : ℝ) := by exact_mod_cast hn
    linarith
  have hNm : ((((n : ℤ) - m).toNat : ℕ) : ℝ) = (n : ℝ) - (m : ℝ) := by
    have : (((n : ℤ) - m).toNat : ℤ) = (n : ℤ) - m :=
      Int.toNat_of_nonneg (by omega)
    exact_mod_cast this
  have hkmr : ((k.toNat : ℕ) : ℝ) = (k : ℝ) := by
    rw [← Int.cast_natCast]
    exact_mod_cast (Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ k))
  -- `E_Λ' ≤ k·(n+k)/m` as a real inequality.
  have hEΛr : ((EΛ : ℕ) : ℝ) ≤ (k : ℝ) * ((n : ℝ) + k) / (m : ℝ) := by
    have hLmax : ((Lmax : ℕ) : ℝ) + 1 ≤ ((n : ℝ) + k) / (m : ℝ) := by
      have hle1 : ((Lmax : ℕ) : ℝ) ≤ ((n : ℝ) - m + k - 1) / (m : ℝ) := by
        have hpos : (0 : ℤ) ≤ (n : ℤ) - (m - k + 1) := by omega
        have hed : (((n : ℤ) - (m - k + 1)) / m : ℤ) * m ≤
            (n : ℤ) - (m - k + 1) := Int.ediv_mul_le _ (by omega)
        have hte : ((Lmax : ℤ)) = ((n : ℤ) - (m - k + 1)) / m := by
          rw [hLmax]
          exact Int.toNat_of_nonneg (Int.ediv_nonneg hpos (by omega))
        have e : ((Lmax : ℤ)) * m ≤ (n : ℤ) - (m - k + 1) := by
          rw [hte]; exact hed
        have er : ((Lmax : ℝ)) * (m : ℝ) ≤ (n : ℝ) - (m : ℝ) + (k : ℝ) - 1 := by
          have e' : ((Lmax : ℝ)) * (m : ℝ) ≤
              (((n : ℤ) - (m - k + 1) : ℤ) : ℝ) := by exact_mod_cast e
          push_cast at e'
          linarith
        rw [le_div_iff₀ hmr]
        linarith
      rw [le_div_iff₀ hmr] at hle1 ⊢
      linarith
    have e : ((EΛ : ℕ) : ℝ) ≤ ((Λ.card * (Lmax + 1) : ℕ) : ℝ) := by
      exact_mod_cast hEΛle
    push_cast at e
    have hΛr : ((Λ.card : ℕ) : ℝ) ≤ (k : ℝ) := by
      have : ((Λ.card : ℕ) : ℝ) ≤ ((k.toNat : ℕ) : ℝ) := by
        exact_mod_cast hΛcard
      rwa [hkmr] at this
    calc ((EΛ : ℕ) : ℝ)
        ≤ (Λ.card : ℝ) * (((Lmax : ℕ) : ℝ) + 1) := e
      _ ≤ (k : ℝ) * (((Lmax : ℕ) : ℝ) + 1) :=
          mul_le_mul_of_nonneg_right hΛr (by positivity)
      _ ≤ (k : ℝ) * ((n : ℝ) + k) / (m : ℝ) := by
          rw [le_div_iff₀ hmr]
          rw [le_div_iff₀ hmr] at hLmax
          nlinarith [hLmax, hmr]
  -- `k·(n+k)/m ≤ (n+k)/40` from `40·k ≤ m`.
  have hkk : (k : ℝ) * ((n : ℝ) + k) / (m : ℝ) ≤ ((n : ℝ) + k) / 40 := by
    have hk40r : (40 : ℝ) * (k : ℝ) ≤ (m : ℝ) := by
      have e : ((k * 40 : ℤ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hk40
      push_cast at e
      linarith
    have hnk : (0 : ℝ) ≤ (n : ℝ) + (k : ℝ) := by
      have hkr : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (show (0 : ℤ) ≤ k by omega)
      linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))]
    rw [div_le_iff₀ hmr, div_mul_eq_mul_div,
      le_div_iff₀ (by norm_num : (0 : ℝ) < 40)]
    linarith [mul_le_mul_of_nonneg_right hk40r hnk]
  -- `k ≤ n/160` from `40·k ≤ m` and `4·m < n`.
  have hk160 : (k : ℝ) ≤ (n : ℝ) / 160 := by
    have hk40r : (40 : ℝ) * (k : ℝ) ≤ (m : ℝ) := by
      have e : ((k * 40 : ℤ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hk40
      push_cast at e
      linarith
    linarith
  -- `2|B| + (4/3)E_B ≤ (2/3)n`.
  have hexp1 : 2 * (B.card : ℝ) + (4 / 3 : ℝ) * ((EB : ℕ) : ℝ) ≤
      (2 / 3 : ℝ) * (n : ℝ) := by
    have hE : (2 : ℝ) * ((EB : ℕ) : ℝ) + (B.card : ℝ) ≤ (n : ℝ) - (m : ℝ) := by
      have e : ((2 * EB + B.card : ℕ) : ℝ) ≤ (((n : ℤ) - m).toNat : ℝ) := by
        exact_mod_cast hEB2
      push_cast at e
      rwa [hNm] at e
    have hB2 : ((B.card : ℕ) : ℝ) ≤ (m : ℝ) / 2 := by
      have e : ((2 * B.card : ℕ) : ℝ) ≤ (m.toNat : ℝ) := by
        exact_mod_cast hBcard
      push_cast at e
      have e2 : ((m.toNat : ℕ) : ℝ) = (m : ℝ) := by
        exact_mod_cast (Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ m))
      rw [e2] at e
      linarith
    nlinarith [hE, hB2]
  -- Combine into the pure exponential.
  have hexp : (2 : ℝ) ^ (2 * (B.card : ℝ)) *
        (2 : ℝ) ^ ((4 / 3 : ℝ) * ((EB : ℕ) : ℝ)) * (2 : ℝ) ^ ((EΛ : ℕ) : ℝ) ≤
      (2 : ℝ) ^ ((111 / 160 : ℝ) * (n : ℝ)) := by
    rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2),
        ← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
    linarith [hexp1, hEΛr, hkk, hk160, hnr_m, hnr]
  calc ((secondMinClass n m (m + k)).card : ℝ)
      ≤ (4 : ℝ) ^ B.card * (5 / 2 : ℝ) ^ EB * (2 : ℝ) ^ EΛ := hdiv
    _ ≤ (2 : ℝ) ^ (2 * (B.card : ℝ)) *
          ((5 / 2 : ℝ) ^ 2 * (2 : ℝ) ^ ((4 / 3 : ℝ) * ((EB : ℕ) : ℝ))) *
          (2 : ℝ) ^ ((EΛ : ℕ) : ℝ) := by
        rw [h4, ← Real.rpow_natCast (2 : ℝ) EΛ]
        exact mul_le_mul
          (mul_le_mul le_rfl h52b (pow_nonneg (by norm_num : (0 : ℝ) ≤ 5 / 2) EB)
            (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _).le)
          le_rfl
          (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _).le
          (by positivity)
    _ = (25 / 4 : ℝ) *
          ((2 : ℝ) ^ (2 * (B.card : ℝ)) *
            (2 : ℝ) ^ ((4 / 3 : ℝ) * ((EB : ℕ) : ℝ)) *
            (2 : ℝ) ^ ((EΛ : ℕ) : ℝ)) := by ring
    _ ≤ (25 / 4 : ℝ) * (2 : ℝ) ^ ((111 / 160 : ℝ) * (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hexp (by norm_num)

/-! ### Uniform per-cell bound and frontier assembly at `111/160`

The regimes: `s = m` (singleton), `s = 2m` (void), `40k ≤ m` (staircase,
`111/160`), `m < 40k` with `k < n/1000` (orbit, `s < 41n/1000` gives
exponent `≤ 41/6000 + (1777/2700)(1041/1000) < 111/160`), and `k ≥ n/1000`
(golden ratio, `(25/36)(999/1000) = 111/160` exactly). -/

private theorem one_le_mul_of_ge {a b : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    1 ≤ a * b := by
  have h : (1 : ℝ) * 1 ≤ a * b :=
    mul_le_mul ha hb zero_le_one (zero_le_one.trans ha)
  rwa [mul_one] at h

/-- **Uniform per-cell bound.**  Every cell `(m, s)` on the frontier
`1 ≤ m`, `4m < n`, `m ≤ s` satisfies
`card ≤ cellSharpConst · 2^{(111/160)·n}`. -/
theorem secondMinClass_card_le_cell_111_160 {n : ℕ} {m s : ℤ}
    (hm : 1 ≤ m) (hn : 4 * m < (n : ℤ)) (hms : m ≤ s) :
    ((secondMinClass n m s).card : ℝ) ≤
      cellSharpConst * (2 : ℝ) ^ ((111 / 160 : ℝ) * (n : ℝ)) := by
  have h2n : (0 : ℝ) ≤ (2 : ℝ) ^ ((111 / 160 : ℝ) * (n : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have h1n : (1 : ℝ) ≤ (2 : ℝ) ^ ((111 / 160 : ℝ) * (n : ℝ)) :=
    Real.one_le_rpow (by norm_num) (by positivity)
  by_cases hsm_eq : s = m
  · -- `s = m`: the subsingleton `{m}`.
    have e : ((secondMinClass n m s).card : ℝ) ≤ 1 := by
      rw [hsm_eq]
      exact_mod_cast secondMinClass_self_le_one
    exact e.trans (one_le_mul_of_ge cellSharpConst_ge_one h1n)
  by_cases hs2m : s = 2 * m
  · -- `s = 2m`: void by `m + m = 2m`.
    rw [hs2m, secondMinClass_two_mul, Finset.card_empty, Nat.cast_zero]
    exact mul_nonneg cellSharpConst_pos.le h2n
  have hsm : m < s := lt_of_le_of_ne hms (Ne.symm hsm_eq)
  set k := s - m with hk_def
  have hk1 : 1 ≤ k := by omega
  have hseq : s = m + k := by omega
  by_cases hk40 : k * 40 ≤ m
  · -- Staircase regime: `40k ≤ m`.
    have hkm : k < m := by omega
    rw [hseq]
    refine (secondMinClass_card_le_stair_sharp hm hk1 hkm hn hk40).trans ?_
    exact mul_le_mul cellSharpConst_ge_quarter le_rfl h2n cellSharpConst_pos.le
  · have hm_lt : m < 40 * k := by omega
    have hs_lt : s < 41 * k := by omega
    by_cases hk1000 : k * 1000 < (n : ℤ)
    · -- Orbit regime: `s < 41k < 41n/1000`.
      refine (secondMinClass_card_le_orbit_sharp hm hsm).trans ?_
      apply mul_le_mul cellSharpConst_ge_orbit _
        (Real.rpow_nonneg (by norm_num) _) cellSharpConst_pos.le
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      have hsr : (s : ℝ) < 41 * (k : ℝ) := by exact_mod_cast hs_lt
      have hkr : (k : ℝ) * 1000 < (n : ℝ) := by exact_mod_cast hk1000
      linarith [hsr.le, hkr.le]
    · -- Golden-ratio regime: `k ≥ n/1000`, exponent `≤ n - k`.
      have hk1000' : (n : ℤ) ≤ 1000 * k := by omega
      have hφ := secondMinClass_card_le_goldenRatio (n := n) (m := m) (s := s) hm
      set E := ((n : ℤ) - s).toNat + (min m ((n : ℤ) - s)).toNat with hE_def
      -- `E ≤ (n - k)₊`.
      have hE : E ≤ (n - k).toNat := by
        rcases le_or_gt s (n : ℤ) with hsn | hsn
        · rw [hE_def]
          have hmin : (min m ((n : ℤ) - s)).toNat ≤ m.toNat :=
            Int.toNat_le_toNat (min_le_left _ _)
          have hsum : (↑n - s).toNat + m.toNat = (↑n - k).toNat := by
            apply Nat.cast_injective (R := ℤ)
            push_cast
            rw [Int.toNat_of_nonneg (by omega), Int.toNat_of_nonneg (by omega),
                Int.toNat_of_nonneg (by omega)]
            omega
          omega
        · rw [hE_def]
          have ht : ((n : ℤ) - s).toNat = 0 :=
            Int.toNat_eq_zero.mpr (by omega)
          have hm2 : (min m ((n : ℤ) - s)).toNat = 0 := by
            rw [min_eq_right (show (n : ℤ) - s ≤ m by omega)]
            exact Int.toNat_eq_zero.mpr (by omega)
          rw [ht, hm2]
          exact Nat.zero_le _
      have hEr : ((E : ℕ) : ℝ) ≤ max ((n : ℝ) - (k : ℝ)) 0 := by
        have e : ((E : ℕ) : ℝ) ≤ (((n - k).toNat : ℕ) : ℝ) := by
          exact_mod_cast hE
        refine e.trans ?_
        rcases le_or_gt 0 ((n : ℤ) - k) with hnk | hnk
        · have hnke : (((n - k).toNat : ℕ) : ℝ) = (n : ℝ) - (k : ℝ) := by
            have h : (((n - k).toNat : ℕ) : ℤ) = n - k :=
              Int.toNat_of_nonneg hnk
            exact_mod_cast h
          rw [hnke]
          exact le_max_left _ _
        · have hz : (n - k).toNat = 0 := Int.toNat_eq_zero.mpr (le_of_lt hnk)
          rw [hz, Nat.cast_zero]
          exact le_max_right _ _
      refine hφ.trans ?_
      refine (goldenRatio_pow_le_two_rpow E).trans ?_
      refine (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) ?_)
        (pow_nonneg Real.goldenRatio_pos.le _)).trans
        (mul_le_mul cellSharpConst_ge_phi le_rfl h2n cellSharpConst_pos.le)
      have hkr : (n : ℝ) ≤ 1000 * (k : ℝ) := by exact_mod_cast hk1000'
      rcases le_or_gt 0 ((n : ℝ) - (k : ℝ)) with hnk | hnk
      · rw [max_eq_left hnk] at hEr
        linarith [hEr, hkr]
      · rw [max_eq_right hnk.le] at hEr
        linarith [hEr, (Nat.cast_nonneg E : (0 : ℝ) ≤ (E : ℝ)),
          (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))]

/-- **Frontier double sum.**  At most `n²` cells, each bounded by the
uniform per-cell bound at exponent `111/160`. -/
theorem smallMinSum_le_cell_111_160 {n : ℕ} :
    (smallMinSum n : ℝ) ≤
      (n : ℝ) ^ 2 * cellSharpConst * (2 : ℝ) ^ ((111 / 160 : ℝ) * (n : ℝ)) := by
  have h2n : (0 : ℝ) ≤ (2 : ℝ) ^ ((111 / 160 : ℝ) * (n : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hC2X : (0 : ℝ) ≤
      cellSharpConst * (2 : ℝ) ^ ((111 / 160 : ℝ) * (n : ℝ)) :=
    mul_nonneg cellSharpConst_pos.le h2n
  have hcardIcc : ((Finset.Icc 1 (n : ℤ)).card : ℝ) ≤ (n : ℝ) := by
    have hnat : (Finset.Icc 1 (n : ℤ)).card ≤ n := by
      rw [Int.card_Icc]
      have h := Int.toNat_le_toNat
        (show ((n : ℤ) + 1 - 1) ≤ (n : ℤ) by omega)
      rwa [Int.toNat_natCast] at h
    exact_mod_cast hnat
  calc (smallMinSum n : ℝ)
      = ∑ m ∈ (Finset.Icc 1 (n : ℤ)).filter (fun m => 4 * m < (n : ℤ)),
          (((minClass n m).card : ℕ) : ℝ) := by
        rw [smallMinSum, Nat.cast_sum]
    _ = ∑ m ∈ (Finset.Icc 1 (n : ℤ)).filter (fun m => 4 * m < (n : ℤ)),
          ∑ s ∈ Finset.Icc m (n : ℤ),
            (((secondMinClass n m s).card : ℕ) : ℝ) := by
        apply Finset.sum_congr rfl
        intro m hm
        rw [minClass_card_eq_sum_secondMinClass, Nat.cast_sum]
    _ ≤ ∑ m ∈ (Finset.Icc 1 (n : ℤ)).filter (fun m => 4 * m < (n : ℤ)),
          ∑ _s ∈ Finset.Icc m (n : ℤ),
            (cellSharpConst * (2 : ℝ) ^ ((111 / 160 : ℝ) * (n : ℝ))) := by
        apply Finset.sum_le_sum
        intro m hm
        apply Finset.sum_le_sum
        intro s hs
        have hm1 : 1 ≤ m := (Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1).1
        have h4m : 4 * m < (n : ℤ) := (Finset.mem_filter.mp hm).2
        have hms : m ≤ s := (Finset.mem_Icc.mp hs).1
        exact secondMinClass_card_le_cell_111_160 hm1 h4m hms
    _ ≤ ∑ m ∈ (Finset.Icc 1 (n : ℤ)).filter (fun m => 4 * m < (n : ℤ)),
          ((n : ℝ) *
            (cellSharpConst * (2 : ℝ) ^ ((111 / 160 : ℝ) * (n : ℝ)))) := by
        apply Finset.sum_le_sum
        intro m hm
        rw [Finset.sum_const, nsmul_eq_mul]
        apply mul_le_mul_of_nonneg_right _ hC2X
        have hsub : Finset.Icc m (n : ℤ) ⊆ Finset.Icc 1 (n : ℤ) :=
          Finset.Icc_subset_Icc
            (Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1).1 le_rfl
        exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans hcardIcc
    _ = (((Finset.Icc 1 (n : ℤ)).filter (fun m => 4 * m < (n : ℤ))).card : ℝ) *
          ((n : ℝ) *
            (cellSharpConst * (2 : ℝ) ^ ((111 / 160 : ℝ) * (n : ℝ)))) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (n : ℝ) * ((n : ℝ) *
          (cellSharpConst * (2 : ℝ) ^ ((111 / 160 : ℝ) * (n : ℝ)))) := by
        apply mul_le_mul _ le_rfl (mul_nonneg (Nat.cast_nonneg n) hC2X)
          (Nat.cast_nonneg n)
        have hsub := Finset.card_filter_le (Finset.Icc 1 (n : ℤ))
          (fun m => 4 * m < (n : ℤ))
        exact (Nat.cast_le.mpr hsub).trans hcardIcc
    _ = (n : ℝ) ^ 2 * cellSharpConst * (2 : ℝ) ^ ((111 / 160 : ℝ) * (n : ℝ)) :=
        by ring

/-- **`SmallMinBound (111/160)`.** -/
theorem smallMinBound_111_160 : SmallMinBound (111 / 160) := by
  intro ε hε
  refine ⟨cellSharpConst, ?_⟩
  have hε2 : (0 : ℝ) < ε / 2 := by linarith
  have h1 := eventually_mul_two_pow_le (c := (111 / 160 : ℝ)) hε2
  have h2 := eventually_mul_two_pow_le (c := (111 / 160 : ℝ) + ε / 2) hε2
  filter_upwards [h1, h2] with n hn1 hn2
  calc (smallMinSum n : ℝ)
      ≤ (n : ℝ) ^ 2 * cellSharpConst *
          (2 : ℝ) ^ ((111 / 160 : ℝ) * (n : ℝ)) := smallMinSum_le_cell_111_160
    _ = cellSharpConst * ((n : ℝ) * ((n : ℝ) *
          (2 : ℝ) ^ ((111 / 160 : ℝ) * (n : ℝ)))) := by ring_nf
    _ ≤ cellSharpConst * ((n : ℝ) *
          (2 : ℝ) ^ (((111 / 160 : ℝ) + ε / 2) * (n : ℝ))) := by
        apply mul_le_mul_of_nonneg_left _ cellSharpConst_pos.le
        exact mul_le_mul_of_nonneg_left hn1 (Nat.cast_nonneg n)
    _ ≤ cellSharpConst * (2 : ℝ) ^ (((111 / 160 : ℝ) + ε) * (n : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ cellSharpConst_pos.le
        exact hn2.trans (le_of_eq (by congr 1; ring))

/-- **The unconditional eventual ratio bound at `111/160 = 0.69375`,
strictly below the previous `347/500 = 0.694`. -/
theorem eventualRatioUpper_111_160 :
    EventualRatioUpper (max (111 / 160 : ℝ) (1 / 2)) :=
  eventualRatioUpper_of_smallMinBound smallMinBound_111_160

end JSP000728
