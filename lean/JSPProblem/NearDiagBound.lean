import JSPProblem.EventualUpper
import JSPProblem.StairLadder
import JSPProblem.TwoMin
import JSPProblem.TwoMinBound
import JSPProblem.LargeS
import Mathlib.Algebra.Field.GeomSum
import Mathlib.NumberTheory.Real.GoldenRatio

/-!
# JSP-000728 — near-diagonal cell bounds and `s`-sum bookkeeping

The second-minimum decomposition
(`minClass_card_eq_sum_secondMinClass`, `TwoMin.lean`) writes

  `(minClass n m).card = ∑_{s ∈ Icc m n} (secondMinClass n m s).card`,

and `smallMinSum n` (`EventualUpper.lean`) sums the `minClass` cards over
the frontier `4m < n`.  This file assembles the per-cell layer of that
double sum:

* `card_powerset_filter_shiftFree2_mono_Icc` — monotonicity of the
  double-shift-free subset count in the ambient finset.  Combined with
  `Icc (s+1) n ⊆ Icc (m+1) n` this upgrades every bound on the `Icc
  (m+1) n` count (e.g. a staircase product bound) to a bound on
  `secondMinClass n m s`
  (`secondMinClass_card_le_stairProd_conditional`,
  `secondMinClass_card_le_stairProd`).

* `cellBound n m s` — the ℕ-valued per-cell bound, namely the
  `shiftFree2`-subset count of `Icc (s+1) n` into which the class
  injects (`secondMinClass_card_le_shiftFree2`), and the bookkeeping
  inequality `smallMinSum_le_sum_cellBound`.

* `cellBoundReal n m s` — the unconditional ℝ-valued per-cell bound,
  piecewise by regime: `s = m` (subsingleton class, `≤ 1`), `s = 2m`
  (void, `0`), `m < s` with `n ≤ 2s` (vacuous `s`-shift, matching bound
  `3^{(n-s)₊}`), and the golden-ratio fallback
  `φ^{(n-s)₊ + min(m,n-s)₊}` (`secondMinClass_card_le_cellBoundReal`,
  `smallMinSum_le_sum_cellBoundReal`).

* `sum_Icc_int_reflect`, `sum_Icc_goldenRatio_reflect_le`,
  `sum_Icc_goldenRatio_add_le` — the ℝ-level geometric decay of the
  `s`-sum: reindexing `s ↦ n − s` turns the sum into a geometric series,
  bounded by the largest term times `φ/(φ − 1)`
  (`sum_secondMinClass_Icc_le_goldenRatio`,
  `sum_Icc_goldenRatio_min_le`).

* `eventually_mul_two_pow_le`, `eventually_const_mul_two_pow_le` —
  polynomial/constant absorption into `2^{ε n}`, repackaging
  `eventually_natCast_le_two_pow_mul` and `eventually_le_two_pow_mul`.

* `smallMinBound_of_cellBound`, `smallMinBound_of_cellBoundReal` and the
  chained `eventualRatioUpper_of_cellBound(Real)` — conditional
  discharge of `SmallMinBound c` (hence `EventualRatioUpper (max c
  (1/2))`) from an eventual bound on the cell-bound double sum.  These
  are *conditional*: they take the sum estimate as hypothesis, leaving
  the staircase/matching cells to be discharged elsewhere.
-/

namespace JSP000728

/-- **Monotonicity in the ambient finset.**  If `a ⊆ b`, the
double-shift-free subsets of `a` are double-shift-free subsets of `b`,
so the filtered-powerset count is monotone.  Applied to
`Icc (s+1) n ⊆ Icc (m+1) n` (for `m ≤ s`), this lets any product bound
over `Icc (m+1) n` serve as a per-cell bound for `secondMinClass n m s`. -/
theorem card_powerset_filter_shiftFree2_mono_Icc {m s : ℤ}
    {a b : Finset ℤ} (h : a ⊆ b) :
    (a.powerset.filter (shiftFree2 m s)).card ≤
      (b.powerset.filter (shiftFree2 m s)).card := by
  apply Finset.card_le_card
  intro t ht
  rw [Finset.mem_filter, Finset.mem_powerset] at ht
  rw [Finset.mem_filter, Finset.mem_powerset]
  exact ⟨ht.1.trans h, ht.2⟩

/-- **Conditional cell bound.**  For `m ≤ s` (e.g. the near-diagonal
`s = m + k`, `1 ≤ k < m`), the class injects into the double-shift-free
subsets of `Icc (s+1) n ⊆ Icc (m+1) n`; hence *any* bound `P` on the
`Icc (m+1) n` count bounds the class.  This is the hook through which a
staircase matching bound on `Icc (m+1) n` enters per cell. -/
theorem secondMinClass_card_le_stairProd_conditional {n : ℕ} {m s : ℤ}
    (hms : m ≤ s) {P : ℕ}
    (hprod : ((Finset.Icc (m + 1) (n : ℤ)).powerset.filter
        (shiftFree2 m s)).card ≤ P) :
    (secondMinClass n m s).card ≤ P :=
  (secondMinClass_card_le_shiftFree2.trans
    (card_powerset_filter_shiftFree2_mono_Icc
      (Finset.Icc_subset_Icc (by omega) le_rfl))).trans hprod

/-- **Conditional staircase product bound per cell.**  In the staircase
regime `1 ≤ m < s`, `2s ≤ 3m`, if every mod-`m` rail pair
`cls n m r ∪ cls n m (r + s - m)` admits the staircase estimate, then
`secondMinClass n m s` is bounded by the staircase product times the
leftover-rail Fibonacci product — the conclusion of
`card_powerset_filter_shiftFree2_Icc_le_stairProd` transported to the
class via `secondMinClass_card_le_stairProd_conditional`. -/
theorem secondMinClass_card_le_stairProd {n : ℕ} {m s : ℤ}
    (hm : 1 ≤ m) (hms : m < s) (hsm : 2 * s ≤ 3 * m)
    (hpair : ∀ r ∈ Finset.Icc 1 (s - m),
      ((cls n m r ∪ cls n m (r + s - m)).powerset.filter
          (shiftFree2 m s)).card ≤
        (stairSets (((n : ℤ) - r) / m).toNat).card) :
    (secondMinClass n m s).card ≤
      (∏ r ∈ Finset.Icc 1 (s - m),
          (stairSets (((n : ℤ) - r) / m).toNat).card) *
        ∏ ρ ∈ Finset.Icc (2 * (s - m) + 1) m,
          Nat.fib ((((n : ℤ) - ρ) / m).toNat + 2) :=
  secondMinClass_card_le_stairProd_conditional hms.le
    (card_powerset_filter_shiftFree2_Icc_le_stairProd hm hms hsm hpair)

/-- **Per-cell bound (ℕ-valued).**  The entry-level bound for
`secondMinClass n m s`: the number of double-shift-free subsets of
`Icc (s+1) n`, into which the class injects
(`secondMinClass_card_le_shiftFree2`).  Every finer per-cell analysis
(staircase product, matching, vacuous `s`-shift) improves on this. -/
def cellBound (n : ℕ) (m s : ℤ) : ℕ :=
  ((Finset.Icc (s + 1) (n : ℤ)).powerset.filter (shiftFree2 m s)).card

/-- The class card is bounded by its cell bound — this is exactly
`secondMinClass_card_le_shiftFree2`. -/
theorem secondMinClass_card_le_cellBound {n : ℕ} {m s : ℤ} :
    (secondMinClass n m s).card ≤ cellBound n m s :=
  secondMinClass_card_le_shiftFree2

/-- **Bookkeeping.**  The frontier sum is bounded by the cell-bound
double sum: `minClass_card_eq_sum_secondMinClass` expands each
`minClass` into its `s`-sum and `secondMinClass_card_le_cellBound`
bounds each cell.  Pure `Finset.sum_le_sum` assembly. -/
theorem smallMinSum_le_sum_cellBound (n : ℕ) :
    smallMinSum n ≤
      ∑ m ∈ (Finset.Icc 1 (n : ℤ)).filter (fun m => 4 * m < (n : ℤ)),
        ∑ s ∈ Finset.Icc m (n : ℤ), cellBound n m s := by
  unfold smallMinSum
  apply Finset.sum_le_sum
  intro m _
  rw [minClass_card_eq_sum_secondMinClass]
  exact Finset.sum_le_sum fun s _ => secondMinClass_card_le_cellBound

/-- **Reindexing an integer-interval sum by reflection.**  The map
`s ↦ (b − s).toNat` sends `Icc a b` bijectively onto `Icc 0 (b−a)` in ℕ
(for `0 ≤ a ≤ b`), turning a reflected sum into a ℕ-indexed one. -/
theorem sum_Icc_int_reflect {a b : ℤ} (_ha : 0 ≤ a) (hab : a ≤ b)
    {f : ℕ → ℝ} :
    ∑ s ∈ Finset.Icc a b, f (b - s).toNat =
      ∑ u ∈ Finset.Icc 0 (b - a).toNat, f u := by
  refine Finset.sum_nbij' (i := fun s => (b - s).toNat)
    (j := fun u => b - (u : ℤ)) ?_ ?_ ?_ ?_ ?_
  · intro s hs
    rw [Finset.mem_Icc] at hs
    rw [Finset.mem_Icc]
    exact ⟨Nat.zero_le _, Int.toNat_le_toNat (by omega : b - s ≤ b - a)⟩
  · intro u hu
    rw [Finset.mem_Icc] at hu
    rw [Finset.mem_Icc]
    have hcast : (u : ℤ) ≤ (((b - a).toNat : ℕ) : ℤ) :=
      Nat.cast_le.mpr hu.2
    rw [Int.toNat_of_nonneg (sub_nonneg.mpr hab)] at hcast
    have hu0 : (0 : ℤ) ≤ (u : ℤ) := Nat.cast_nonneg u
    exact ⟨by omega, by omega⟩
  · intro s hs
    rw [Finset.mem_Icc] at hs
    have hbs : (((b - s).toNat : ℕ) : ℤ) = b - s :=
      Int.toNat_of_nonneg (by omega)
    rw [hbs]
    ring
  · intro u _
    have he : b - (b - (u : ℤ)) = (u : ℤ) := by ring
    rw [he]
    simp
  · intro _ _
    rfl

/-- **Geometric decay of the reflected `φ`-sum.**  For `0 ≤ a ≤ b`,
`∑_{s ∈ Icc a b} φ^{(b-s)₊}` is a geometric series bounded by the
largest term times `φ/(φ−1)`. -/
theorem sum_Icc_goldenRatio_reflect_le {a b : ℤ} (ha : 0 ≤ a)
    (hab : a ≤ b) :
    ∑ s ∈ Finset.Icc a b, Real.goldenRatio ^ (b - s).toNat ≤
      Real.goldenRatio ^ ((b - a).toNat + 1) / (Real.goldenRatio - 1) := by
  have hφ : (0 : ℝ) < Real.goldenRatio - 1 :=
    sub_pos.mpr Real.one_lt_goldenRatio
  calc ∑ s ∈ Finset.Icc a b, Real.goldenRatio ^ (b - s).toNat
      = ∑ u ∈ Finset.Icc 0 (b - a).toNat, Real.goldenRatio ^ u :=
        sum_Icc_int_reflect ha hab
    _ = ∑ u ∈ Finset.range ((b - a).toNat + 1), Real.goldenRatio ^ u := by
        rw [Nat.range_succ_eq_Icc_zero]
    _ = (Real.goldenRatio ^ ((b - a).toNat + 1) - 1) /
          (Real.goldenRatio - 1) :=
        geom_sum_eq (ne_of_gt Real.one_lt_goldenRatio) _
    _ ≤ Real.goldenRatio ^ ((b - a).toNat + 1) / (Real.goldenRatio - 1) :=
        div_le_div_of_nonneg_right (sub_le_self _ zero_le_one) hφ.le

/-- **Geometric decay with a constant exponent shift.**  Factoring
`φ^{(n-s)₊ + M} = φ^{(n-s)₊} · φ^M` out of the reflected sum gives
`∑_{s ∈ Icc a n} φ^{(n-s)₊ + M} ≤ (φ/(φ−1)) · φ^{(n-a)₊ + M}` — the
`s`-sum decays geometrically away from the diagonal `s = a`. -/
theorem sum_Icc_goldenRatio_add_le {n : ℕ} (M : ℕ) {a : ℤ} (ha : 0 ≤ a)
    (han : a ≤ (n : ℤ)) :
    ∑ s ∈ Finset.Icc a (n : ℤ),
        Real.goldenRatio ^ (((n : ℤ) - s).toNat + M) ≤
      (Real.goldenRatio / (Real.goldenRatio - 1)) *
        Real.goldenRatio ^ (((n : ℤ) - a).toNat + M) := by
  have hrewrite : ∀ s ∈ Finset.Icc a (n : ℤ),
      Real.goldenRatio ^ (((n : ℤ) - s).toNat + M) =
        Real.goldenRatio ^ ((n : ℤ) - s).toNat * Real.goldenRatio ^ M :=
    fun s _ => pow_add _ _ _
  rw [Finset.sum_congr rfl hrewrite, ← Finset.sum_mul]
  calc (∑ s ∈ Finset.Icc a (n : ℤ),
          Real.goldenRatio ^ ((n : ℤ) - s).toNat) * Real.goldenRatio ^ M
      ≤ (Real.goldenRatio ^ (((n : ℤ) - a).toNat + 1) /
          (Real.goldenRatio - 1)) * Real.goldenRatio ^ M :=
        mul_le_mul_of_nonneg_right (sum_Icc_goldenRatio_reflect_le ha han)
          (pow_nonneg Real.goldenRatio_pos.le _)
    _ = (Real.goldenRatio / (Real.goldenRatio - 1)) *
          Real.goldenRatio ^ (((n : ℤ) - a).toNat + M) := by
        have e : Real.goldenRatio ^ (((n : ℤ) - a).toNat + 1) *
            Real.goldenRatio ^ M =
            Real.goldenRatio *
              Real.goldenRatio ^ (((n : ℤ) - a).toNat + M) := by
          rw [pow_succ', mul_assoc, ← pow_add]
        rw [div_mul_eq_mul_div, e]
        ring

/-- **The golden-ratio tail bound for the `s`-sum.**  For `1 ≤ m` and
`0 ≤ a ≤ n`, summing the coarse per-cell bound
`secondMinClass_card_le_goldenRatio_add` over `s ∈ Icc a n` gives
`∑_s (secondMinClass n m s).card ≤ (φ/(φ−1)) · φ^{(n-a)₊ + m₊}`:
geometric decay in the second minimum. -/
theorem sum_secondMinClass_Icc_le_goldenRatio {n : ℕ} {m a : ℤ}
    (hm : 1 ≤ m) (ha : 0 ≤ a) (han : a ≤ (n : ℤ)) :
    ∑ s ∈ Finset.Icc a (n : ℤ), ((secondMinClass n m s).card : ℝ) ≤
      (Real.goldenRatio / (Real.goldenRatio - 1)) *
        Real.goldenRatio ^ (((n : ℤ) - a).toNat + m.toNat) :=
  (Finset.sum_le_sum fun _ _ =>
    secondMinClass_card_le_goldenRatio_add hm).trans
      (sum_Icc_goldenRatio_add_le m.toNat ha han)

/-- **Sharper summand version.**  The same geometric bound with the
sharper exponent `(n-s)₊ + min(m, n-s)₊` of
`secondMinClass_card_le_goldenRatio` (bounded above by `m₊`). -/
theorem sum_Icc_goldenRatio_min_le {n : ℕ} {m a : ℤ} (ha : 0 ≤ a)
    (han : a ≤ (n : ℤ)) :
    ∑ s ∈ Finset.Icc a (n : ℤ),
        Real.goldenRatio ^
          (((n : ℤ) - s).toNat + (min m ((n : ℤ) - s)).toNat) ≤
      (Real.goldenRatio / (Real.goldenRatio - 1)) *
        Real.goldenRatio ^ (((n : ℤ) - a).toNat + m.toNat) := by
  refine (Finset.sum_le_sum fun s _ =>
    pow_le_pow_right₀ Real.one_lt_goldenRatio.le ?_).trans
      (sum_Icc_goldenRatio_add_le m.toNat ha han)
  have h : (min m ((n : ℤ) - s)).toNat ≤ m.toNat :=
    Int.toNat_le_toNat (min_le_left m _)
  omega

/-- **Absorption of the polynomial factor.**  `n · 2^{c·n} ≤ 2^{(c+ε)n}`
eventually — a repackaging of `eventually_natCast_le_two_pow_mul`
(`n ≤ 2^{ε n}`) for use inside `SmallMinBound`-style estimates. -/
theorem eventually_mul_two_pow_le {c ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in Filter.atTop,
      (n : ℝ) * (2 : ℝ) ^ (c * (n : ℝ)) ≤
        (2 : ℝ) ^ ((c + ε) * (n : ℝ)) := by
  filter_upwards [eventually_natCast_le_two_pow_mul hε] with n hn
  calc (n : ℝ) * (2 : ℝ) ^ (c * (n : ℝ))
      ≤ (2 : ℝ) ^ (ε * (n : ℝ)) * (2 : ℝ) ^ (c * (n : ℝ)) :=
        mul_le_mul_of_nonneg_right hn (Real.rpow_nonneg (by norm_num) _)
    _ = (2 : ℝ) ^ ((c + ε) * (n : ℝ)) := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        congr 1
        ring

/-- **Absorption of a constant factor.**  `D · 2^{c·n} ≤ 2^{(c+ε)n}`
eventually — repackaging of `eventually_le_two_pow_mul`. -/
theorem eventually_const_mul_two_pow_le {c ε : ℝ} (hε : 0 < ε) (D : ℝ) :
    ∀ᶠ n : ℕ in Filter.atTop,
      D * (2 : ℝ) ^ (c * (n : ℝ)) ≤ (2 : ℝ) ^ ((c + ε) * (n : ℝ)) := by
  filter_upwards [eventually_le_two_pow_mul hε D] with n hn
  calc D * (2 : ℝ) ^ (c * (n : ℝ))
      ≤ (2 : ℝ) ^ (ε * (n : ℝ)) * (2 : ℝ) ^ (c * (n : ℝ)) :=
        mul_le_mul_of_nonneg_right hn (Real.rpow_nonneg (by norm_num) _)
    _ = (2 : ℝ) ^ ((c + ε) * (n : ℝ)) := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        congr 1
        ring

/-- **Conditional discharge of `SmallMinBound` (ℕ cells).**  If the
cell-bound double sum `∑_{4m<n} ∑_{s ∈ Icc m n} cellBound n m s` is
eventually at most `C · 2^{(c+ε)n}` for every `ε > 0`, then
`SmallMinBound c` holds: `smallMinSum_le_sum_cellBound` dominates the
frontier sum pointwise in `n`. -/
theorem smallMinBound_of_cellBound {c : ℝ}
    (h : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ᶠ n : ℕ in Filter.atTop,
      ((∑ m ∈ (Finset.Icc 1 (n : ℤ)).filter (fun m => 4 * m < (n : ℤ)),
          ∑ s ∈ Finset.Icc m (n : ℤ), cellBound n m s) : ℝ) ≤
        C * (2 : ℝ) ^ ((c + ε) * (n : ℝ))) :
    SmallMinBound c := by
  intro ε hε
  obtain ⟨C, hC⟩ := h ε hε
  refine ⟨C, hC.mono fun n hn => ?_⟩
  have h1 : (smallMinSum n : ℝ) ≤
      Nat.cast (∑ m ∈ (Finset.Icc 1 (n : ℤ)).filter (fun m => 4 * m < (n : ℤ)),
        ∑ s ∈ Finset.Icc m (n : ℤ), cellBound n m s) :=
    Nat.cast_le.mpr (smallMinSum_le_sum_cellBound n)
  push_cast at h1
  exact h1.trans hn

/-- **Chained conditional upper bound (ℕ cells).**  The cell-bound
hypothesis of `smallMinBound_of_cellBound` implies
`EventualRatioUpper (max c (1/2))` via
`eventualRatioUpper_of_smallMinBound`. -/
theorem eventualRatioUpper_of_cellBound {c : ℝ}
    (h : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ᶠ n : ℕ in Filter.atTop,
      ((∑ m ∈ (Finset.Icc 1 (n : ℤ)).filter (fun m => 4 * m < (n : ℤ)),
          ∑ s ∈ Finset.Icc m (n : ℤ), cellBound n m s) : ℝ) ≤
        C * (2 : ℝ) ^ ((c + ε) * (n : ℝ))) :
    EventualRatioUpper (max c (1 / 2)) :=
  eventualRatioUpper_of_smallMinBound (smallMinBound_of_cellBound h)

/-- The subsingleton class `s = m` has at most one member: the
constraint `s = m → M ⊆ {m}` together with `m ∈ M` forces `M = {m}`. -/
theorem secondMinClass_self_le_one {n : ℕ} {m : ℤ} :
    (secondMinClass n m m).card ≤ 1 := by
  have hsub : secondMinClass n m m ⊆ {({m} : Finset ℤ)} := by
    intro M hM
    obtain ⟨-, hmM, -, hsg⟩ := mem_secondMinClass.mp hM
    rw [Finset.mem_singleton]
    refine Finset.eq_singleton_iff_unique_mem.mpr ⟨hmM, fun x hx => ?_⟩
    exact Finset.mem_singleton.mp (hsg rfl hx)
  exact (Finset.card_le_card hsub).trans (Finset.card_singleton _).le

/-- **Unconditional per-cell bound (ℝ-valued).**  The best unconditional
estimate for `(secondMinClass n m s).card`, piecewise by regime:

* `s = m` — the subsingleton class `{m}`, at most `1` member
  (`secondMinClass_self_le_one`);
* `s = 2m` — void by the Schur triple `m + m = 2m`
  (`secondMinClass_two_mul`), bound `0`;
* `m < s` with `n ≤ 2s` — vacuous `s`-shift, matching bound
  `3^{(n-s)₊}` (`secondMinClass_card_le_of_half_le_real`);
* otherwise — the golden-ratio bound `φ^{(n-s)₊ + min(m,n-s)₊}`
  (`secondMinClass_card_le_goldenRatio`).

The near-diagonal staircase cells `m < s ≤ 3m/2` currently fall through
to the golden-ratio branch; their improvement stays conditional
(`secondMinClass_card_le_stairProd_conditional`). -/
noncomputable def cellBoundReal (n : ℕ) (m s : ℤ) : ℝ :=
  if s = m then 1
  else if s = 2 * m then 0
  else if m < s ∧ (n : ℤ) ≤ 2 * s then (3 : ℝ) ^ ((n : ℤ) - s).toNat
  else Real.goldenRatio ^
    (((n : ℤ) - s).toNat + (min m ((n : ℤ) - s)).toNat)

/-- The class card is bounded by `cellBoundReal n m s` in every regime
(for `1 ≤ m ≤ s`; the `s = m` and `s = 2m` branches use the subsingleton
and void facts, the `n ≤ 2s` branch the matching bound, and the fallback
the golden-ratio bound). -/
theorem secondMinClass_card_le_cellBoundReal {n : ℕ} {m s : ℤ}
    (hm : 1 ≤ m) (_hms : m ≤ s) :
    ((secondMinClass n m s).card : ℝ) ≤ cellBoundReal n m s := by
  unfold cellBoundReal
  split_ifs with hsm hs2 hbig
  · rw [hsm]
    exact_mod_cast secondMinClass_self_le_one
  · rw [hs2, secondMinClass_two_mul]
    simp
  · exact secondMinClass_card_le_of_half_le_real hm hbig.1 hbig.2
  · exact secondMinClass_card_le_goldenRatio hm

/-- **Bookkeeping (ℝ).**  The frontier sum, cast to ℝ, is bounded by the
`cellBoundReal` double sum — same assembly as
`smallMinSum_le_sum_cellBound`, now over the unconditional piecewise
bound. -/
theorem smallMinSum_le_sum_cellBoundReal {n : ℕ} :
    (smallMinSum n : ℝ) ≤
      ∑ m ∈ (Finset.Icc 1 (n : ℤ)).filter (fun m => 4 * m < (n : ℤ)),
        ∑ s ∈ Finset.Icc m (n : ℤ), cellBoundReal n m s := by
  unfold smallMinSum
  rw [Nat.cast_sum]
  apply Finset.sum_le_sum
  intro m hm
  have hm1 : 1 ≤ m := (Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1).1
  rw [minClass_card_eq_sum_secondMinClass, Nat.cast_sum]
  apply Finset.sum_le_sum
  intro s hs
  exact secondMinClass_card_le_cellBoundReal hm1 (Finset.mem_Icc.mp hs).1

/-- **Conditional discharge of `SmallMinBound` (ℝ cells).**  If the
`cellBoundReal` double sum is eventually at most `C · 2^{(c+ε)n}` for
every `ε > 0`, then `SmallMinBound c` holds. -/
theorem smallMinBound_of_cellBoundReal {c : ℝ}
    (h : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ᶠ n : ℕ in Filter.atTop,
      (∑ m ∈ (Finset.Icc 1 (n : ℤ)).filter (fun m => 4 * m < (n : ℤ)),
          ∑ s ∈ Finset.Icc m (n : ℤ), cellBoundReal n m s) ≤
        C * (2 : ℝ) ^ ((c + ε) * (n : ℝ))) :
    SmallMinBound c := by
  intro ε hε
  obtain ⟨C, hC⟩ := h ε hε
  exact ⟨C, hC.mono fun _ hn =>
    smallMinSum_le_sum_cellBoundReal.trans hn⟩

/-- **Chained conditional upper bound (ℝ cells).**  The `cellBoundReal`
hypothesis implies `EventualRatioUpper (max c (1/2))`. -/
theorem eventualRatioUpper_of_cellBoundReal {c : ℝ}
    (h : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ᶠ n : ℕ in Filter.atTop,
      (∑ m ∈ (Finset.Icc 1 (n : ℤ)).filter (fun m => 4 * m < (n : ℤ)),
          ∑ s ∈ Finset.Icc m (n : ℤ), cellBoundReal n m s) ≤
        C * (2 : ℝ) ^ ((c + ε) * (n : ℝ))) :
    EventualRatioUpper (max c (1 / 2)) :=
  eventualRatioUpper_of_smallMinBound (smallMinBound_of_cellBoundReal h)

end JSP000728
