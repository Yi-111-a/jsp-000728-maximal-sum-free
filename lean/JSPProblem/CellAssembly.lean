import JSPProblem.NearDiagBound
import JSPProblem.StairMatchSharp
import JSPProblem.OrbitStripCount
import JSPProblem.EventualUpper
import JSPProblem.TwoMinBound
import JSPProblem.OrbitDecomp
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

/-!
# JSP-000728 — assembly of the small-minimum frontier

This file assembles the per-cell engines developed in
`StairMatchSharp` (near-diagonal staircase matching),
`OrbitStripCount` (orbit-strip counting) and `TwoMinBound`
(golden-ratio / large-`s` bounds) into an unconditional bound on

  `smallMinSum n = Σ_{4m < n} (minClass n m).card`.

The main results:

* `pow_le_const_mul_two_rpow` — generic power-conversion lemma
  `b^j ≤ b^{q-1}·2^{(p/q)·j}` from `b^q ≤ 2^p`;
* `goldenRatio_pow_le_two_rpow` — `φ^j ≤ φ³⁵·2^{(25/36)·j}`;
* `pell_pow_le_two_rpow` — `(1+√2)^j ≤ C·2^{(32/25)·j}`;
* `card_powerset_filter_shiftFree2_Icc_le_orbitPhi` — the orbit-strip
  bound with the odd-orbit leftover charged at the golden-ratio rate;
* `secondMinClass_card_le_orbit_closed` — the closed form
  `card ≤ C·2^{s/6 + (33/50)·(n+s)}`;
* `secondMinClass_card_le_stair_closed` — the closed near-diagonal
  form `card ≤ (25/4)·2^{(347/500)·n}` for `50·k ≤ m`;
* `secondMinClass_card_le_cell` — the uniform per-cell bound
  `card ≤ cellSharpConst·2^{(347/500)·n}` over the whole frontier;
* `smallMinSum_le_cell` — `smallMinSum n ≤ n²·C·2^{(347/500)·n}`;
* `smallMinBound_347_500` — `SmallMinBound (347/500)`;
* `eventualRatioUpper_347_500` —
  `EventualRatioUpper (max (347/500) (1/2))`, i.e. the unconditional
  exponential rate `0.694` strictly below `log₂ φ ≈ 0.6942`.
-/

namespace JSP000728

/-! ### Generic power conversion -/

/-- If `b ≥ 1` and `b^q ≤ 2^{a·q}` (with `q > 0`, `a ≥ 0`), then every
power satisfies `b^j ≤ b^{q-1}·2^{a·j}`.  This packages the
`b ≤ 2^a` comparison in a form convenient for asymptotic bounds. -/
theorem pow_le_const_mul_two_rpow {b : ℝ} (hb : 1 ≤ b) {q : ℕ} (hq : 0 < q)
    {a : ℝ} (ha : 0 ≤ a) (h : b ^ q ≤ (2 : ℝ) ^ (a * q)) (j : ℕ) :
    b ^ j ≤ b ^ (q - 1) * (2 : ℝ) ^ (a * j) := by
  have hb0 : (0 : ℝ) ≤ b := le_trans zero_le_one hb
  have hdecomp : j = q * (j / q) + j % q := (Nat.div_add_mod j q).symm
  have hmod : j % q ≤ q - 1 := by
    have := Nat.mod_lt j hq
    omega
  calc b ^ j = (b ^ q) ^ (j / q) * b ^ (j % q) := by
        conv_lhs => rw [hdecomp]
        rw [pow_add, pow_mul]
    _ ≤ ((2 : ℝ) ^ (a * q)) ^ (j / q) * b ^ (q - 1) := by
        apply mul_le_mul
        · exact pow_le_pow_left₀ (pow_nonneg hb0 _) h _
        · exact pow_le_pow_right₀ hb hmod
        · exact pow_nonneg hb0 _
        · exact pow_nonneg (by positivity) _
    _ = b ^ (q - 1) * (2 : ℝ) ^ (a * (q * ((j / q : ℕ) : ℝ))) := by
        have hrw : ((2 : ℝ) ^ (a * q)) ^ (j / q) =
            (2 : ℝ) ^ (a * q * ((j / q : ℕ) : ℝ)) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
        rw [hrw, mul_comm (b ^ (q - 1)), mul_assoc]
    _ ≤ b ^ (q - 1) * (2 : ℝ) ^ (a * j) := by
        apply mul_le_mul_of_nonneg_left _ (pow_nonneg hb0 _)
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
        apply mul_le_mul_of_nonneg_left _ ha
        exact_mod_cast
          (show q * (j / q) ≤ j by rw [mul_comm]; exact Nat.div_mul_le_self j q)

/-- `φ^{36} = (φ+1)^{18} < 2^{25}`: the golden ratio satisfies
`φ < 2^{25/36}`, i.e. `log₂ φ < 25/36 ≈ 0.6944`. -/
theorem goldenRatio_pow36_le : Real.goldenRatio ^ 36 ≤ (2 : ℝ) ^ 25 := by
  have hφ : Real.goldenRatio + 1 < (26181 : ℝ) / 10000 := by
    have hsqrt : Real.sqrt 5 < (22362 : ℝ) / 10000 := by
      rw [Real.sqrt_lt' (by norm_num)]
      norm_num
    have : Real.goldenRatio = (1 + Real.sqrt 5) / 2 := rfl
    rw [this]
    linarith
  have hsq : Real.goldenRatio ^ 2 = Real.goldenRatio + 1 := by
    rw [Real.goldenRatio]; rw [sq]; ring_nf
    have h5 : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
    linarith [h5]
  calc Real.goldenRatio ^ 36 = (Real.goldenRatio ^ 2) ^ 18 := by
        rw [← pow_mul]
    _ = (Real.goldenRatio + 1) ^ 18 := by rw [hsq]
    _ ≤ ((26181 : ℝ) / 10000) ^ 18 :=
        pow_le_pow_left₀ (by linarith [Real.goldenRatio_pos]) hφ.le _
    _ ≤ (2 : ℝ) ^ 25 := by norm_num

/-- `φ^j ≤ φ^{35}·2^{(25/36)·j}` for every `j`. -/
theorem goldenRatio_pow_le_two_rpow (j : ℕ) :
    Real.goldenRatio ^ j ≤
      Real.goldenRatio ^ 35 * (2 : ℝ) ^ ((25 / 36 : ℝ) * j) := by
  have h := pow_le_const_mul_two_rpow Real.one_lt_goldenRatio.le
    (q := 36) (by norm_num) (a := 25 / 36) (by norm_num) ?_ j
  · simpa using h
  · calc Real.goldenRatio ^ 36 ≤ (2 : ℝ) ^ 25 := goldenRatio_pow36_le
      _ = (2 : ℝ) ^ ((25 / 36 : ℝ) * 36) := by norm_num

/-- `(1+√2)^{25} < 2^{32}`: `1+√2 < 2^{32/25}`, i.e.
`log₂ (1+√2) < 32/25 = 1.28`. -/
theorem pell_pow25_le : (1 + Real.sqrt 2) ^ 25 ≤ (2 : ℝ) ^ 32 := by
  have hs : (1 : ℝ) + Real.sqrt 2 < (24143 : ℝ) / 10000 := by
    have hsqrt : Real.sqrt 2 < (14143 : ℝ) / 10000 := by
      rw [Real.sqrt_lt' (by norm_num)]
      norm_num
    linarith
  calc (1 + Real.sqrt 2) ^ 25 ≤ ((24143 : ℝ) / 10000) ^ 25 :=
      pow_le_pow_left₀ (add_nonneg zero_le_one (Real.sqrt_nonneg _)) hs.le _
    _ ≤ (2 : ℝ) ^ 32 := by norm_num

/-- `(1+√2)^j ≤ (1+√2)^{24}·2^{(32/25)·j}` for every `j`. -/
theorem pell_pow_le_two_rpow (j : ℕ) :
    (1 + Real.sqrt 2) ^ j ≤
      (1 + Real.sqrt 2) ^ 24 * (2 : ℝ) ^ ((32 / 25 : ℝ) * j) := by
  have h := pow_le_const_mul_two_rpow (b := 1 + Real.sqrt 2)
    (le_add_of_nonneg_right (Real.sqrt_nonneg _)) (q := 25) (by norm_num)
    (a := 32 / 25) (by norm_num) ?_ j
  · simpa using h
  · calc (1 + Real.sqrt 2) ^ 25 ≤ (2 : ℝ) ^ 32 := pell_pow25_le
      _ = (2 : ℝ) ^ ((32 / 25 : ℝ) * 25) := by norm_num

/-- `(5/4)^j ≤ (5/4)^2·2^{(1/3)·j}` for every `j`, since
`(5/4)^3 = 125/64 < 2`. -/
theorem five_four_pow_le_two_rpow (j : ℕ) :
    (5 / 4 : ℝ) ^ j ≤ (5 / 4) ^ 2 * (2 : ℝ) ^ ((1 / 3 : ℝ) * j) := by
  have h := pow_le_const_mul_two_rpow (b := 5 / 4) (by norm_num)
    (q := 3) (by norm_num) (a := 1 / 3) (by norm_num) ?_ j
  · simpa using h
  · norm_num

/-- `(5/2)^j ≤ (5/2)^2·2^{(4/3)·j}` for every `j`, since
`(5/2)^3 = 125/8 < 16`. -/
theorem five_two_pow_le_two_rpow (j : ℕ) :
    (5 / 2 : ℝ) ^ j ≤ (5 / 2) ^ 2 * (2 : ℝ) ^ ((4 / 3 : ℝ) * j) := by
  have h := pow_le_const_mul_two_rpow (b := 5 / 2) (by norm_num)
    (q := 3) (by norm_num) (a := 4 / 3) (by norm_num) ?_ j
  · simpa using h
  · norm_num

/-! ### The orbit-strip bound with golden-ratio leftover

Adapting `card_powerset_filter_shiftFree2_Icc_le_realPow`: the odd-orbit
Fibonacci factor is charged at the golden-ratio rate rather than the
rate `2`, using `fib_le_goldenRatio_pow`. -/

/-- **Orbit-strip bound, golden-ratio leftover.**  For `1 ≤ m < s`,
the double-shift-free subsets of `Icc (s+1) n` are bounded by

  `(5/4·(1+√2)^{L+1})^{⌊c/2⌋·g} · φ^{(L+1)·(c%2)·g}`

where `c = orbitLen m s`, `g = Int.gcd s m` and
`L = ((n-1)/s).toNat`.  Same proof as `realPow`, but `F_{L+2}` is
bounded by `φ^{L+1}` instead of `2^{L+1}`. -/
theorem card_powerset_filter_shiftFree2_Icc_le_orbitPhi {n : ℕ} {m s : ℤ}
    (hm : 1 ≤ m) (hms : m < s) :
    (((Finset.Icc (s + 1) (n : ℤ)).powerset.filter (shiftFree2 m s)).card : ℝ) ≤
      (5 / 4 * (1 + Real.sqrt 2) ^ ((((n : ℤ) - 1) / s).toNat + 1)) ^
          (orbitLen m s / 2 * Int.gcd s m) *
        (Real.goldenRatio ^ ((((n : ℤ) - 1) / s).toNat + 1)) ^
          (orbitLen m s % 2 * Int.gcd s m) := by
  have hN := card_powerset_filter_shiftFree2_Icc_le_orbitPow (n := n) hm hms
  have hcast : (((Finset.Icc (s + 1) (n : ℤ)).powerset.filter
      (shiftFree2 m s)).card : ℝ) ≤
      (((ladSets ((((n : ℤ) - 1) / s).toNat + 1)).card ^
          (orbitLen m s / 2) *
        Nat.fib ((((n : ℤ) - 1) / s).toNat + 2) ^ (orbitLen m s % 2)) ^
        Int.gcd s m : ℝ) := by
    exact_mod_cast hN
  have hA : ((ladSets ((((n : ℤ) - 1) / s).toNat + 1)).card : ℝ) ≤
      5 / 4 * (1 + Real.sqrt 2) ^ ((((n : ℤ) - 1) / s).toNat + 1) :=
    ladSets_card_le_pell_pow _
  have hF : (Nat.fib ((((n : ℤ) - 1) / s).toNat + 2) : ℝ) ≤
      Real.goldenRatio ^ ((((n : ℤ) - 1) / s).toNat + 1) := by
    have h := fib_add_two_le_goldenRatio_pow (((n : ℤ) - 1) / s).toNat
    refine h.trans (pow_le_pow_right₀ Real.one_lt_goldenRatio.le ?_)
    split <;> omega
  have hA0 : (0 : ℝ) ≤ (ladSets ((((n : ℤ) - 1) / s).toNat + 1)).card :=
    Nat.cast_nonneg _
  have hF0 : (0 : ℝ) ≤ Nat.fib ((((n : ℤ) - 1) / s).toNat + 2) :=
    Nat.cast_nonneg _
  have hB0 : (0 : ℝ) ≤ 5 / 4 * (1 + Real.sqrt 2) ^
      ((((n : ℤ) - 1) / s).toNat + 1) := le_trans hA0 hA
  have h20 : (0 : ℝ) ≤ Real.goldenRatio ^
      ((((n : ℤ) - 1) / s).toNat + 1) := le_trans hF0 hF
  calc (((Finset.Icc (s + 1) (n : ℤ)).powerset.filter
        (shiftFree2 m s)).card : ℝ)
      ≤ (((ladSets ((((n : ℤ) - 1) / s).toNat + 1)).card ^
            (orbitLen m s / 2) *
          Nat.fib ((((n : ℤ) - 1) / s).toNat + 2) ^ (orbitLen m s % 2)) ^
          Int.gcd s m : ℝ) := hcast
    _ = ((ladSets ((((n : ℤ) - 1) / s).toNat + 1)).card : ℝ) ^
            (orbitLen m s / 2 * Int.gcd s m) *
          (Nat.fib ((((n : ℤ) - 1) / s).toNat + 2) : ℝ) ^
            (orbitLen m s % 2 * Int.gcd s m) := by
        rw [mul_pow, ← pow_mul, ← pow_mul]
    _ ≤ (5 / 4 * (1 + Real.sqrt 2) ^
            ((((n : ℤ) - 1) / s).toNat + 1)) ^
            (orbitLen m s / 2 * Int.gcd s m) *
          (Real.goldenRatio ^ ((((n : ℤ) - 1) / s).toNat + 1)) ^
            (orbitLen m s % 2 * Int.gcd s m) :=
        mul_le_mul (pow_le_pow_left₀ hA0 hA _) (pow_le_pow_left₀ hF0 hF _)
          (pow_nonneg hF0 _) (pow_nonneg hB0 _)

/-- **Closed orbit bound.**  For `1 ≤ m < s` the second-minimum class
is bounded by a pure exponential

  `card ≤ C · 2^{s/6 + (33/50)·(n+s)}`

with `C = (5/4)²·(1+√2)^{24}·φ^{35}`.  The key input is
`(L+1)·s ≤ n+s` where `L = ((n-1)/s).toNat`, together with the
`gcd`–`orbitLen` bookkeeping `(c/2)·g ≤ s/2` and `c%2·g ≤ s/3`. -/
theorem secondMinClass_card_le_orbit_closed {n : ℕ} {m s : ℤ}
    (hm : 1 ≤ m) (hms : m < s) :
    ((secondMinClass n m s).card : ℝ) ≤
      ((5 / 4 : ℝ) ^ 2 * (1 + Real.sqrt 2) ^ 24 * Real.goldenRatio ^ 35) *
        (2 : ℝ) ^ ((1 / 6 : ℝ) * s + (33 / 50 : ℝ) * ((n : ℝ) + s)) := by
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
  --   `≤ s/6 + (33/50)·(L+1)·s`.
  have hE : ((c / 2 * g : ℕ) : ℝ) / 3 +
        (32 / 25 : ℝ) * ((L : ℝ) + 1) * (c / 2 * g : ℕ) +
        (25 / 36 : ℝ) * ((L : ℝ) + 1) * (c % 2 * g : ℕ) ≤
      (1 / 6 : ℝ) * s + (33 / 50 : ℝ) * ((L : ℝ) + 1) * (s : ℝ) := by
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
      rw [hG0]
      nlinarith [hPr, hL1, mul_le_mul_of_nonneg_left hPr
        (show (0:ℝ) ≤ (32/25) * ((L:ℝ) + 1) by positivity),
        mul_nonneg hL1 hsr.le]
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
      nlinarith [hPre, hgr, hL1, hsr,
        mul_le_mul_of_nonneg_left hgr hL1,
        mul_nonneg hL1 hsr.le, (Nat.cast_nonneg g : (0:ℝ) ≤ (g:ℕ))]
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
          (2 : ℝ) ^ ((1 / 6 : ℝ) * s + (33 / 50 : ℝ) * ((n : ℝ) + s)) := by
        apply mul_le_mul_of_nonneg_left _ hK
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
        have e1 : (((L + 1) * (c / 2 * g) : ℕ) : ℝ) =
            ((L : ℝ) + 1) * ((c / 2 * g : ℕ) : ℝ) := by
          rw [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
        have e2 : (((L + 1) * (c % 2 * g) : ℕ) : ℝ) =
            ((L : ℝ) + 1) * ((c % 2 * g : ℕ) : ℝ) := by
          rw [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
        rw [e1, e2]
        have hsum : ((c / 2 * g : ℕ) : ℝ) / 3 +
              (32 / 25 : ℝ) * ((L : ℝ) + 1) * ((c / 2 * g : ℕ) : ℝ) +
              (25 / 36 : ℝ) * ((L : ℝ) + 1) * ((c % 2 * g : ℕ) : ℝ) ≤
            (1 / 6 : ℝ) * s + (33 / 50 : ℝ) * ((n : ℝ) + s) := by
          refine hE.trans ?_
          have hmono : (33 / 50 : ℝ) * ((L : ℝ) + 1) * (s : ℝ) ≤
              (33 / 50 : ℝ) * ((n : ℝ) + s) := by
            nlinarith [mul_le_mul_of_nonneg_left hLs
              (by norm_num : (0:ℝ) ≤ 33/50)]
          linarith [hmono]
        linarith [hsum]

/-- **Closed staircase bound.**  For `s = m+k` with `1 ≤ k < m` and
`50·k ≤ m`, the sharp staircase-matching bound gives

  `card ≤ (25/4) · 2^{(347/500)·n}`.

The key bookkeeping: `2·E_B + |B| ≤ (n-m)₊` for the base sum
`E_B = Σ_B (L_r - 1)` (which is what makes the `5`-factor a rate-`5/2`)
and `E_Λ' = Σ_Λ (L_ρ+1) ≤ k·(n+k)/m ≤ (n+m)/50` for the leftover. -/
theorem secondMinClass_card_le_stair_closed {n : ℕ} {m k : ℤ}
    (hm : 1 ≤ m) (hk : 1 ≤ k) (hkm : k < m) (hn : 4 * m < (n : ℤ))
    (hk50 : k * 50 ≤ m) :
    ((secondMinClass n m (m + k)).card : ℝ) ≤
      (25 / 4 : ℝ) * (2 : ℝ) ^ ((347 / 500 : ℝ) * (n : ℝ)) := by
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
  -- `k·(n+k)/m ≤ (n+m)/50` from `50·k ≤ m` and `k ≤ m`.
  have hkk : (k : ℝ) * ((n : ℝ) + k) / (m : ℝ) ≤ ((n : ℝ) + m) / 50 := by
    have hk50r : (50 : ℝ) * (k : ℝ) ≤ (m : ℝ) := by
      have e : ((k * 50 : ℤ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hk50
      push_cast at e
      linarith
    have hkmr2 : (k : ℝ) ≤ (m : ℝ) := by exact_mod_cast hkm.le
    have hnk : (0 : ℝ) ≤ (n : ℝ) + (k : ℝ) := by positivity
    have hnm : (0 : ℝ) ≤ (n : ℝ) + (m : ℝ) := by positivity
    rw [div_le_iff₀ hmr, div_mul_eq_mul_div, le_div_iff₀ (by norm_num : (0:ℝ) < 50)]
    nlinarith [mul_le_mul hk50r (show (n:ℝ)+(k:ℝ) ≤ (n:ℝ)+(m:ℝ) by linarith)
      hnk (show (0:ℝ) ≤ (m:ℝ) by linarith)]
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
      (2 : ℝ) ^ ((347 / 500 : ℝ) * (n : ℝ)) := by
    rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2),
        ← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
    nlinarith [hexp1, hEΛr, hkk, hnr_m, hnr]
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
    _ ≤ (25 / 4 : ℝ) * (2 : ℝ) ^ ((347 / 500 : ℝ) * (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hexp (by norm_num)

/-! ### Uniform per-cell bound and frontier assembly

The engines above give regime-specific estimates that jointly cover the
whole small-minimum frontier `4 m < n`, `m ≤ s ≤ n`:

* `s = m` — the subsingleton `{m}`, at most `1` member;
* `s = 2m` — void by the Schur triple `m + m = 2m`;
* `s = m + k` with `50k ≤ m` — the staircase bound `(25/4)·2^{(347/500)n}`;
* `s = m + k` with `50k > m` and `k < 7n/10000` — the orbit bound; here
  `s < 51k` keeps the exponent below `(68951/100000)n`;
* `s = m + k` with `k ≥ 7n/10000` — the golden-ratio bound
  `φ^{(n-s)₊ + min(m,n-s)₊}` whose exponent is at most `n - k`, i.e.
  `≤ φ³⁵·2^{(25/36)·(9993/10000)n} ≤ φ³⁵·2^{(69396/100000)n}`.

Every branch is at most `cellSharpConst · 2^{(347/500)·n}`, and the `≤ n²`
cells on the frontier are absorbed by `+ε` — discharging
`SmallMinBound (347/500)` and `EventualRatioUpper (max (347/500) (1/2))`
unconditionally. -/

/-- Universal prefactor: the staircase `25/4` times the orbit constant
`(5/4)²·(1+√2)²⁴·φ³⁵` (which itself dominates `φ³⁵`). -/
noncomputable def cellSharpConst : ℝ :=
  (25 / 4) * ((5 / 4) ^ 2 * (1 + Real.sqrt 2) ^ 24 * Real.goldenRatio ^ 35)

private theorem one_le_mul' {a b : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    1 ≤ a * b := by
  have h : (1 : ℝ) * 1 ≤ a * b :=
    mul_le_mul ha hb zero_le_one (zero_le_one.trans ha)
  rwa [mul_one] at h

private theorem le_mul_of_one_le_right_of_nonneg {a b : ℝ} (ha : 0 ≤ a)
    (hb : 1 ≤ b) : a ≤ a * b := by
  have h : a * 1 ≤ a * b := mul_le_mul_of_nonneg_left hb ha
  rwa [mul_one] at h

private theorem le_mul_of_one_le_left_of_nonneg {a b : ℝ} (ha : 0 ≤ a)
    (hb : 1 ≤ b) : a ≤ b * a := by
  have h : 1 * a ≤ b * a := mul_le_mul_of_nonneg_right hb ha
  rwa [one_mul] at h

theorem cellSharpFactor_ge_one : (1 : ℝ) ≤
    (5 / 4) ^ 2 * (1 + Real.sqrt 2) ^ 24 * Real.goldenRatio ^ 35 := by
  have h1 : (1 : ℝ) ≤ (5 / 4 : ℝ) ^ 2 := by norm_num
  have h2 : (1 : ℝ) ≤ (1 + Real.sqrt 2) ^ 24 :=
    one_le_pow₀ (by have := Real.sqrt_nonneg 2; linarith)
  have h3 : (1 : ℝ) ≤ Real.goldenRatio ^ 35 :=
    one_le_pow₀ Real.one_lt_goldenRatio.le
  exact one_le_mul' (one_le_mul' h1 h2) h3

theorem cellSharpConst_pos : (0 : ℝ) < cellSharpConst := by
  unfold cellSharpConst
  have hφ : (0 : ℝ) < Real.goldenRatio ^ 35 := pow_pos Real.goldenRatio_pos _
  have h2 : (0 : ℝ) < (1 + Real.sqrt 2) ^ 24 := by
    apply pow_pos
    have := Real.sqrt_nonneg 2
    linarith
  positivity

theorem cellSharpConst_ge_one : (1 : ℝ) ≤ cellSharpConst :=
  one_le_mul' (by norm_num) cellSharpFactor_ge_one

theorem cellSharpConst_ge_quarter : (25 / 4 : ℝ) ≤ cellSharpConst :=
  le_mul_of_one_le_right_of_nonneg (by norm_num) cellSharpFactor_ge_one

theorem cellSharpConst_ge_orbit :
    (5 / 4) ^ 2 * (1 + Real.sqrt 2) ^ 24 * Real.goldenRatio ^ 35 ≤
      cellSharpConst :=
  le_mul_of_one_le_left_of_nonneg
    (zero_le_one.trans cellSharpFactor_ge_one) (by norm_num)

theorem cellSharpConst_ge_phi : Real.goldenRatio ^ 35 ≤ cellSharpConst := by
  have hAB : (1 : ℝ) ≤ (5 / 4 : ℝ) ^ 2 * (1 + Real.sqrt 2) ^ 24 :=
    one_le_mul' (by norm_num)
      (one_le_pow₀ (by have := Real.sqrt_nonneg 2; linarith))
  calc Real.goldenRatio ^ 35
      ≤ ((5 / 4 : ℝ) ^ 2 * (1 + Real.sqrt 2) ^ 24) * Real.goldenRatio ^ 35 :=
        le_mul_of_one_le_left_of_nonneg
          (pow_nonneg Real.goldenRatio_pos.le _) hAB
    _ ≤ cellSharpConst := cellSharpConst_ge_orbit

/-- **Uniform per-cell bound.**  Every cell `(m, s)` on the frontier
`1 ≤ m`, `4m < n`, `m ≤ s` satisfies
`card ≤ cellSharpConst · 2^{(347/500)·n}`. -/
theorem secondMinClass_card_le_cell {n : ℕ} {m s : ℤ}
    (hm : 1 ≤ m) (hn : 4 * m < (n : ℤ)) (hms : m ≤ s) :
    ((secondMinClass n m s).card : ℝ) ≤
      cellSharpConst * (2 : ℝ) ^ ((347 / 500 : ℝ) * (n : ℝ)) := by
  have h2n : (0 : ℝ) ≤ (2 : ℝ) ^ ((347 / 500 : ℝ) * (n : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have h1n : (1 : ℝ) ≤ (2 : ℝ) ^ ((347 / 500 : ℝ) * (n : ℝ)) :=
    Real.one_le_rpow (by norm_num) (by positivity)
  by_cases hsm_eq : s = m
  · -- `s = m`: the subsingleton `{m}`.
    have e : ((secondMinClass n m s).card : ℝ) ≤ 1 := by
      rw [hsm_eq]
      exact_mod_cast secondMinClass_self_le_one
    exact e.trans (one_le_mul' cellSharpConst_ge_one h1n)
  by_cases hs2m : s = 2 * m
  · -- `s = 2m`: void by `m + m = 2m`.
    rw [hs2m, secondMinClass_two_mul, Finset.card_empty, Nat.cast_zero]
    exact mul_nonneg cellSharpConst_pos.le h2n
  have hsm : m < s := lt_of_le_of_ne hms (Ne.symm hsm_eq)
  set k := s - m with hk_def
  have hk1 : 1 ≤ k := by omega
  have hseq : s = m + k := by omega
  by_cases hk50 : k * 50 ≤ m
  · -- Staircase regime: `50k ≤ m`.
    have hkm : k < m := by omega
    rw [hseq]
    refine (secondMinClass_card_le_stair_closed hm hk1 hkm hn hk50).trans ?_
    exact mul_le_mul cellSharpConst_ge_quarter le_rfl h2n cellSharpConst_pos.le
  · have hm_lt : m < 50 * k := by omega
    have hs_lt : s < 51 * k := by omega
    by_cases hk7 : k * 10000 < 7 * (n : ℤ)
    · -- Orbit regime: `s < 51k < 51·7n/10000` keeps the exponent small.
      refine (secondMinClass_card_le_orbit_closed hm hsm).trans ?_
      apply mul_le_mul cellSharpConst_ge_orbit _
        (Real.rpow_nonneg (by norm_num) _) cellSharpConst_pos.le
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      have hsr : (s : ℝ) < 51 * (k : ℝ) := by exact_mod_cast hs_lt
      have hkr : (k : ℝ) * 10000 < 7 * (n : ℝ) := by exact_mod_cast hk7
      linarith
    · -- Golden-ratio regime: exponent `≤ n - k ≤ (9993/10000)n`.
      have hk7' : 7 * (n : ℤ) ≤ 10000 * k := by omega
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
      have hkr : 7 * (n : ℝ) ≤ 10000 * (k : ℝ) := by exact_mod_cast hk7'
      rcases le_or_gt 0 ((n : ℝ) - (k : ℝ)) with hnk | hnk
      · rw [max_eq_left hnk] at hEr
        nlinarith [hEr, hkr, (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))]
      · rw [max_eq_right hnk.le] at hEr
        nlinarith [hEr, (Nat.cast_nonneg E : (0 : ℝ) ≤ (E : ℝ)),
          (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))]

/-- **Frontier double sum.**  At most `n²` cells, each bounded by the
uniform per-cell bound. -/
theorem smallMinSum_le_cell {n : ℕ} :
    (smallMinSum n : ℝ) ≤
      (n : ℝ) ^ 2 * cellSharpConst * (2 : ℝ) ^ ((347 / 500 : ℝ) * (n : ℝ)) := by
  have h2n : (0 : ℝ) ≤ (2 : ℝ) ^ ((347 / 500 : ℝ) * (n : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hC2X : (0 : ℝ) ≤
      cellSharpConst * (2 : ℝ) ^ ((347 / 500 : ℝ) * (n : ℝ)) :=
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
            (cellSharpConst * (2 : ℝ) ^ ((347 / 500 : ℝ) * (n : ℝ))) := by
        apply Finset.sum_le_sum
        intro m hm
        apply Finset.sum_le_sum
        intro s hs
        have hm1 : 1 ≤ m := (Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1).1
        have h4m : 4 * m < (n : ℤ) := (Finset.mem_filter.mp hm).2
        have hms : m ≤ s := (Finset.mem_Icc.mp hs).1
        exact secondMinClass_card_le_cell hm1 h4m hms
    _ ≤ ∑ m ∈ (Finset.Icc 1 (n : ℤ)).filter (fun m => 4 * m < (n : ℤ)),
          ((n : ℝ) *
            (cellSharpConst * (2 : ℝ) ^ ((347 / 500 : ℝ) * (n : ℝ)))) := by
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
            (cellSharpConst * (2 : ℝ) ^ ((347 / 500 : ℝ) * (n : ℝ)))) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (n : ℝ) * ((n : ℝ) *
          (cellSharpConst * (2 : ℝ) ^ ((347 / 500 : ℝ) * (n : ℝ)))) := by
        apply mul_le_mul _ le_rfl (mul_nonneg (Nat.cast_nonneg n) hC2X)
          (Nat.cast_nonneg n)
        have hsub := Finset.card_filter_le (Finset.Icc 1 (n : ℤ))
          (fun m => 4 * m < (n : ℤ))
        exact (Nat.cast_le.mpr hsub).trans hcardIcc
    _ = (n : ℝ) ^ 2 * cellSharpConst * (2 : ℝ) ^ ((347 / 500 : ℝ) * (n : ℝ)) :=
        by ring

/-- **`SmallMinBound (347/500)`.**  The `n²` cells are absorbed by `+ε`:
`n²·C·2^{0.694n} ≤ C·2^{(0.694+ε)n}` eventually. -/
theorem smallMinBound_347_500 : SmallMinBound (347 / 500) := by
  intro ε hε
  refine ⟨cellSharpConst, ?_⟩
  have hε2 : (0 : ℝ) < ε / 2 := by linarith
  have h1 := eventually_mul_two_pow_le (c := (347 / 500 : ℝ)) hε2
  have h2 := eventually_mul_two_pow_le (c := (347 / 500 : ℝ) + ε / 2) hε2
  filter_upwards [h1, h2] with n hn1 hn2
  calc (smallMinSum n : ℝ)
      ≤ (n : ℝ) ^ 2 * cellSharpConst *
          (2 : ℝ) ^ ((347 / 500 : ℝ) * (n : ℝ)) := smallMinSum_le_cell
    _ = cellSharpConst * ((n : ℝ) * ((n : ℝ) *
          (2 : ℝ) ^ ((347 / 500 : ℝ) * (n : ℝ)))) := by ring_nf
    _ ≤ cellSharpConst * ((n : ℝ) *
          (2 : ℝ) ^ (((347 / 500 : ℝ) + ε / 2) * (n : ℝ))) := by
        apply mul_le_mul_of_nonneg_left _ cellSharpConst_pos.le
        exact mul_le_mul_of_nonneg_left hn1 (Nat.cast_nonneg n)
    _ ≤ cellSharpConst * (2 : ℝ) ^ (((347 / 500 : ℝ) + ε) * (n : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ cellSharpConst_pos.le
        exact hn2.trans (le_of_eq (by congr 1; ring))

/-- **The unconditional eventual ratio bound.** -/
theorem eventualRatioUpper_347_500 :
    EventualRatioUpper (max (347 / 500 : ℝ) (1 / 2)) :=
  eventualRatioUpper_of_smallMinBound smallMinBound_347_500

end JSP000728
