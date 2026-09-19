import JSPProblem.Supersaturation
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Linarith

/-!
# JSP-000728 — quadratic supersaturation for Schur triples

The *elementary* supersaturation input to the sparse-container method:
summing the per-fiber inclusion–exclusion estimate
`card_filter_sub_mem_ge` over all `z ∈ s` gives a quadratic lower bound
on the number of Schur triples of `s ⊆ {1,…,n}`:

  `2 · schurTripleCount s ≥ 3·t² − 2·t·n − t`   where `t = s.card`

(`two_mul_schurTripleCount_ge`; the subtraction-free `ℕ` reformulation
is `schurTripleCount_quadratic`).  The bound is tight on `s =
interval n`, where it recovers `schurTripleCount_interval_ge`.

The two counting inputs are:

* `sum_card_filter_lt_eq_choose_two` — the fibers `|s ∩ [1, z)|` sum to
  `C(t, 2)`, the number of strictly ordered pairs of `s`;
* `sum_toNat_add_choose_le` — `∑ z ∈ s, z ≤ t·n − C(t, 2)`, because the
  complementary pairs `(z, j)` with `z ∈ s`, `z < j ≤ n` contain all
  `C(t, 2)` strict pairs of `s`.

Solving the resulting quadratic in `t` gives
`card_le_of_schurTripleCount_le`: `schurTripleCount s ≤ δ·n²` forces
`s.card ≤ n·(1 + √(4 + 6δ))/3` — in particular `s.card ≤ (2/3 +
o(1))·n` once `δ = o(1)` … up to the `-t` slack term, which is what the
container refinement is for.
-/

namespace JSP000728

/-! ## Strict-pair counts -/

/-- The fibers `|{x ∈ s : x < z}|` over `z ∈ s` enumerate the strictly
ordered pairs of `s`; there are `C(|s|, 2)` of them. -/
theorem sum_card_filter_lt_eq_choose_two (s : Finset ℤ) :
    ∑ z ∈ s, (s.filter fun x => x < z).card = s.card.choose 2 := by
  classical
  have e : ((s ×ˢ s).filter fun p => p.1 < p.2).card
      = ∑ z ∈ s, (s.filter fun x => x < z).card := by
    rw [Finset.card_filter, Finset.sum_product_right]
    exact Finset.sum_congr rfl fun z _ => (Finset.card_filter _ s).symm
  rw [← e, Finset.card_product_filter_lt]

/-- The same strict-pair count with the roles of the coordinates
swapped: `∑ z ∈ s, |{w ∈ s : z < w}| = C(|s|, 2)`. -/
theorem sum_card_filter_gt_eq_choose_two (s : Finset ℤ) :
    ∑ z ∈ s, (s.filter fun w => z < w).card = s.card.choose 2 := by
  classical
  have e : ((s ×ˢ s).filter fun p => p.1 < p.2).card
      = ∑ z ∈ s, (s.filter fun w => z < w).card := by
    rw [Finset.card_filter, Finset.sum_product]
    exact Finset.sum_congr rfl fun z _ => (Finset.card_filter _ s).symm
  rw [← e, Finset.card_product_filter_lt]

/-- **Complement counting.**  For `s ⊆ {1,…,n}` one has
`∑ z ∈ s, z ≤ t·n − C(t,2)` where `t = |s|`: for each `z` the elements
`w ∈ s` above `z` all lie in `{z+1,…,n}`, so
`∑ z, (n − z) = ∑ z |{z+1,…,n}| ≥ ∑ z |{w ∈ s : z < w}| = C(t,2)`. -/
theorem sum_toNat_add_choose_le {n : ℕ} {s : Finset ℤ}
    (hsub : s ⊆ interval n) :
    ∑ z ∈ s, z.toNat + s.card.choose 2 ≤ s.card * n := by
  classical
  have hmem : ∀ z ∈ s, 1 ≤ z ∧ z ≤ (n : ℤ) := fun z hz =>
    Finset.mem_Icc.mp (hsub hz)
  have hfib : ∀ z ∈ s, (s.filter fun w => z < w).card ≤ n - z.toNat := by
    intro z hz
    obtain ⟨hz1, hzn⟩ := hmem z hz
    have hsub2 : s.filter (fun w => z < w) ⊆ Finset.Icc (z + 1) (n : ℤ) := by
      intro w hw
      obtain ⟨hws, hzw⟩ := Finset.mem_filter.mp hw
      obtain ⟨-, hwn⟩ := hmem w hws
      rw [Finset.mem_Icc]
      omega
    calc (s.filter fun w => z < w).card
        ≤ (Finset.Icc (z + 1) (n : ℤ)).card := Finset.card_le_card hsub2
      _ = n - z.toNat := by rw [Int.card_Icc]; omega
  have hsum := Finset.sum_le_sum hfib
  rw [sum_card_filter_gt_eq_choose_two s] at hsum
  rw [Finset.sum_tsub_distrib s (fun z hz => by
      have h' := (hmem z hz).2; omega)] at hsum
  rw [Finset.sum_const, smul_eq_mul] at hsum
  have hsumz : ∑ z ∈ s, z.toNat ≤ s.card * n := by
    calc ∑ z ∈ s, z.toNat ≤ ∑ _z ∈ s, n :=
          Finset.sum_le_sum fun z hz => by
            have h' := (hmem z hz).2; omega
      _ = s.card * n := by rw [Finset.sum_const, smul_eq_mul]
  omega

/-! ## The quadratic supersaturation bound -/

/-- **Quadratic supersaturation.**  For `s ⊆ {1,…,n}` with `t = |s|`,

  `2 · schurTripleCount s ≥ 3·t² − 2·t·n − t`.

Proof: sum `P_z ≥ 2·|s ∩ [1,z)| − (z−1)` over `z ∈ s`; the first sum is
`2·C(t,2)` and `∑ z ≤ t·n − C(t,2)` by `sum_toNat_add_choose_le`. -/
theorem two_mul_schurTripleCount_ge {n : ℕ} {s : Finset ℤ}
    (hsub : s ⊆ interval n) :
    3 * (s.card : ℤ) ^ 2 - 2 * (s.card : ℤ) * (n : ℤ) - (s.card : ℤ)
      ≤ 2 * (schurTripleCount s : ℤ) := by
  classical
  have hmem : ∀ z ∈ s, 1 ≤ z ∧ z ≤ (n : ℤ) := fun z hz =>
    Finset.mem_Icc.mp (hsub hz)
  -- Per-fiber inclusion–exclusion, lifted to `ℤ`.
  have hfib : ∀ z ∈ s, 2 * ((s.filter fun x => x < z).card : ℤ)
      ≤ (z - 1) + ((s.filter fun x => z - x ∈ s).card : ℤ) := by
    intro z hz
    have hA : s ∩ Finset.Icc 1 (z - 1) = s.filter fun x => x < z := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_Icc, Finset.mem_filter]
      constructor
      · rintro ⟨hxs, -, hxz⟩; exact ⟨hxs, by omega⟩
      · rintro ⟨hxs, hxz⟩
        obtain ⟨hx1, -⟩ := hmem x hxs
        exact ⟨hxs, hx1, by omega⟩
    have h := card_filter_sub_mem_ge s z
    rw [hA] at h
    have h' : (2 * (s.filter fun x => x < z).card : ℤ)
        ≤ ((z - 1).toNat : ℤ)
          + ((s.filter fun x => z - x ∈ s).card : ℤ) := by
      exact_mod_cast h
    obtain ⟨hz1, -⟩ := hmem z hz
    have hz1' : ((z - 1).toNat : ℤ) = z - 1 :=
      Int.toNat_of_nonneg (by omega)
    omega
  have hsum := Finset.sum_le_sum hfib
  rw [Finset.sum_add_distrib] at hsum
  have hC : (∑ z ∈ s, 2 * ((s.filter fun x => x < z).card : ℤ))
      = 2 * ((s.card.choose 2 : ℕ) : ℤ) := by
    rw [← Finset.mul_sum, ← Nat.cast_sum, sum_card_filter_lt_eq_choose_two]
  have hB : ∑ z ∈ s, (z - 1 : ℤ) = (∑ z ∈ s, z) - (s.card : ℤ) := by
    rw [Finset.sum_sub_distrib]
    congr 1
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  have hT : (schurTripleCount s : ℤ)
      = ∑ z ∈ s, ((s.filter fun x => z - x ∈ s).card : ℤ) := by
    rw [← Nat.cast_sum, ← schurTripleCount_eq_sum_filter]
  have hsumz : (∑ z ∈ s, z) = ((∑ z ∈ s, z.toNat : ℕ) : ℤ) := by
    rw [Nat.cast_sum]
    exact Finset.sum_congr rfl fun z hz =>
      (Int.toNat_of_nonneg (by have h' := hmem z hz; omega)).symm
  have hbound : ((∑ z ∈ s, z.toNat : ℕ) : ℤ) + (s.card.choose 2 : ℤ)
      ≤ (s.card : ℤ) * (n : ℤ) := by
    exact_mod_cast sum_toNat_add_choose_le hsub
  have hchoose : 2 * ((s.card.choose 2 : ℕ) : ℤ)
      = (s.card : ℤ) * ((s.card : ℤ) - 1) := by
    have h2 : 2 * s.card.choose 2 = s.card * (s.card - 1) := by
      rw [Nat.choose_two_right, Nat.mul_comm 2,
        Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self _)]
    rcases Nat.eq_zero_or_pos s.card with h0 | h0
    · simp [h0]
    · have hc : ((2 * s.card.choose 2 : ℕ) : ℤ)
          = ((s.card * (s.card - 1) : ℕ) : ℤ) := by exact_mod_cast h2
      rw [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_mul, Nat.cast_sub h0,
        Nat.cast_one] at hc
      exact hc
  have key : (s.card : ℤ) * ((s.card : ℤ) - 1)
      = (s.card : ℤ) ^ 2 - (s.card : ℤ) := by ring
  linarith [hsum, hC, hB, hT, hsumz, hbound, hchoose, key]

/-- The supersaturation bound in subtraction-free `ℕ` form:
`3·t² ≤ 2·triples + 2·t·n + t`. -/
theorem schurTripleCount_quadratic {n : ℕ} {s : Finset ℤ}
    (hsub : s ⊆ interval n) :
    3 * s.card ^ 2 ≤ 2 * schurTripleCount s + 2 * s.card * n + s.card := by
  have h := two_mul_schurTripleCount_ge hsub
  zify
  linarith

/-! ## Solving the quadratic -/

/-- **Quadratic consequence.**  If `s ⊆ {1,…,n}` has at most `δ·n²`
Schur triples then `|s| ≤ n·(1 + √(4 + 6δ))/3`.  In particular
`|s| ≤ (1 + o(1))·n` when `δ = o(1)` (and the `2/3`-type threshold
appears after removing the linear slack, e.g. inside the container
method). -/
theorem card_le_of_schurTripleCount_le {n : ℕ} {s : Finset ℤ} {δ : ℝ}
    (hsub : s ⊆ interval n) (hδ : 0 ≤ δ)
    (htri : (schurTripleCount s : ℝ) ≤ δ * (n : ℝ) ^ 2) :
    (s.card : ℝ) ≤ (n : ℝ) * (1 + Real.sqrt (4 + 6 * δ)) / 3 := by
  have hmain : 3 * (s.card : ℝ) ^ 2
      ≤ 2 * (schurTripleCount s : ℝ) + 2 * s.card * n + s.card := by
    exact_mod_cast schurTripleCount_quadratic hsub
  have ht : (s.card : ℝ) ≤ n := by
    have hc := Finset.card_le_card hsub
    rw [card_interval] at hc
    exact_mod_cast hc
  have hn2 : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · simp [h0]
    · have h1 : (1 : ℝ) ≤ n := by exact_mod_cast h0
      have e : (n : ℝ) ^ 2 - n = n * (n - 1) := by ring
      have hnn : (0 : ℝ) ≤ n * (n - 1) :=
        mul_nonneg (Nat.cast_nonneg _) (by linarith)
      linarith
  -- `3t² ≤ 2δn² + 2tn + t ≤ (1 + 2δ)n² + 2tn`.
  have hquad : 3 * (s.card : ℝ) ^ 2 - 2 * (s.card : ℝ) * (n : ℝ)
      - (1 + 2 * δ) * (n : ℝ) ^ 2 ≤ 0 := by
    nlinarith [hmain, htri, ht, hn2]
  -- So `(3t − n)² ≤ n²·(4 + 6δ)`, and taking square roots gives the bound.
  have hr2 : Real.sqrt (4 + 6 * δ) ^ 2 = 4 + 6 * δ :=
    Real.sq_sqrt (by positivity)
  have hkey : 3 * (s.card : ℝ) - (n : ℝ)
      ≤ (n : ℝ) * Real.sqrt (4 + 6 * δ) := by
    apply le_of_sq_le_sq _
      (mul_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _))
    rw [mul_pow, hr2]
    nlinarith [hquad]
  have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
  have hfinal : 3 * (s.card : ℝ)
      ≤ (n : ℝ) * (1 + Real.sqrt (4 + 6 * δ)) := by linarith [hkey]
  linarith [hfinal]

end JSP000728
