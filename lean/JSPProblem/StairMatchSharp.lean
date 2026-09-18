import JSPProblem.StairMatch
import JSPProblem.NearDiagBound
import Mathlib.NumberTheory.Real.GoldenRatio

/-!
# JSP-000728 — the sharp staircase-matching bound

For `s = m + k` with `1 ≤ k < m` the block-parity matching of
`StairMatch.lean` pairs each base rail `r ∈ stairBases m k` with its
partner `r + k` and leaves an even-block leftover `stairLeftover m k`.
The closed bound `card_powerset_filter_shiftFree2_Icc_le_stairMatchClosed`
plugged the *loose* per-pair estimate `a(L) ≤ 4·5^L` into the product and
charged the whole `Σ L ≤ (n−m)₊` budget to the bases alone, yielding
`4^{(m-k)₊}·5^{(n-m)₊}·2^{k₊}` — exponent `log₂ 5 ≈ 2.32` per element.

This module sharpens the bookkeeping in three steps.

* `stairSets_card_mul_two_pow_le'` /
  `stairSets_card_le_four_mul_five_pow_sub_one` : the integer-normalised
  staircase estimate `a(L)·2^{L-1} ≤ 4·5^{L-1}` extended to `L = 0`,
  i.e. `a(L) ≤ 4·5^{L-1}` with ℕ-truncated exponent.
* The residue-level observation that the matching *partitions*
  `Icc 1 m` (`stairMatch_residues_cover`, `stairMatch_card_eq`), while
  the partner rail `r + k` is at most one level shorter than its base
  (`stair_L_le_partner_add_one`).  Hence
  `2·Σ_B L + Σ_Λ L ≤ (n−m)₊ + |B|` (`sum_L_bases_le`): the `5`-power is
  charged to only *half* the total rail length.
* `card_powerset_filter_shiftFree2_Icc_le_stairMatchSharp` :
  `card ≤ 4^{|B|}·5^{Σ_B (L_r-1)}·2^{Σ_Λ (L_ρ+1)}`; the multiplied
  refinement
  `card·2^{Σ_B(L_r-1)} ≤ 4^{|B|}·5^{Σ_B(L_r-1)}·2^{Σ_Λ(L_ρ+1)}`
  (honest per-pair rate `5/2`, in the `_mul_le` style of
  `TriBridge.lean`); and the uniform closed form
  `card ≤ 4^{(m-k)₊}·2^{k₊}·5^{((n-m)₊+m₊)/2}` — a `√5` rate per element
  of `Icc (m+1) n`, halving the `log₂` exponent of the loose bound.
* Real-valued sharpening to the golden ratio: `5/2 ≤ φ²` and
  `F_{L+2} ≤ φ^{L+1}` give `card ≤ 4^{(m-k)₊}·φ^{(n-m)₊+m₊}` — exponent
  `log₂ φ ≈ 0.694` per element — together with the
  `secondMinClass n m (m+k)` corollaries via
  `secondMinClass_card_le_stairProd_conditional`.
-/

namespace JSP000728

/-! ### Per-staircase sharp estimates, extended to `L = 0` -/

/-- `a(L)·2^{L-1} ≤ 4·5^{L-1}` for all `L`, with ℕ-truncated exponents
(`L = 0` reads `a(0)·2^0 = 1 ≤ 4·5^0`). -/
theorem stairSets_card_mul_two_pow_le' (L : ℕ) :
    (stairSets L).card * 2 ^ (L - 1) ≤ 4 * 5 ^ (L - 1) := by
  rcases Nat.eq_zero_or_pos L with rfl | hL
  · rw [stairSets_card_zero]
    norm_num
  · exact stairSets_card_mul_two_pow_le hL

/-- `a(L) ≤ 4·5^{L-1}` for all `L` (ℕ-truncated exponent): the sharp
per-pair factor `4·(5/2)^{L-1}` with its denominator dropped. -/
theorem stairSets_card_le_four_mul_five_pow_sub_one (L : ℕ) :
    (stairSets L).card ≤ 4 * 5 ^ (L - 1) := by
  calc (stairSets L).card
      ≤ (stairSets L).card * 2 ^ (L - 1) := by
        apply Nat.le_mul_of_pos_right
        exact pow_pos (by norm_num) _
    _ ≤ 4 * 5 ^ (L - 1) := stairSets_card_mul_two_pow_le' L

/-! ### The residue-level matching partition -/

/-- Sums over the partners reindex to sums over the bases. -/
theorem stairPartners_sum {m k : ℤ} (f : ℤ → ℕ) :
    ∑ x ∈ stairPartners m k, f x =
      ∑ r ∈ stairBases m k, f (r + k) := by
  simp only [stairPartners]
  exact Finset.sum_image (fun x _ y _ h => by omega)

/-- Specialisation of `stairPartners_sum` to the rail-length
function. -/
theorem stairPartners_sum_L {n : ℕ} {m k : ℤ} :
    ∑ x ∈ stairPartners m k, (((n : ℤ) - x) / m).toNat =
      ∑ r ∈ stairBases m k, (((n : ℤ) - (r + k)) / m).toNat :=
  stairPartners_sum (fun x => (((n : ℤ) - x) / m).toNat)

/-- There are as many partners as bases. -/
theorem stairPartners_card {m k : ℤ} :
    (stairPartners m k).card = (stairBases m k).card := by
  rw [stairPartners]
  exact Finset.card_image_of_injOn (fun x _ y _ h => by omega)

/-- Partners and leftover are disjoint: a partner has odd block index
while a leftover residue has even block index. -/
theorem stairPartners_leftover_disjoint {m k : ℤ} (hk : 1 ≤ k) :
    Disjoint (stairPartners m k) (stairLeftover m k) := by
  rw [Finset.disjoint_left]
  intro ρ hρp hρl
  rw [mem_stairPartners] at hρp
  obtain ⟨r, hr, rfl⟩ := hρp
  rw [mem_stairBases] at hr
  rw [mem_stairLeftover] at hρl
  obtain ⟨hr1, -, hpar⟩ := hr
  obtain ⟨-, -, hparρ⟩ := hρl
  rw [stair_block_add hk] at hparρ
  have hq : Even ((r - 1) / k) := Int.even_iff.mpr hpar
  have h1 : ((r - 1) / k + 1) % 2 = 1 := Int.odd_iff.mp hq.add_one
  omega

/-- Bases and leftover are disjoint (they lie on opposite sides of
`m - k`). -/
theorem stairBases_leftover_disjoint {m k : ℤ} :
    Disjoint (stairBases m k) (stairLeftover m k) := by
  rw [Finset.disjoint_left]
  intro x hxb hxl
  rw [mem_stairBases] at hxb
  rw [mem_stairLeftover] at hxl
  omega

/-- **The residue-level matching partition.**  For `1 ≤ k ≤ m` the
bases, partners and leftover are disjoint and cover `Icc 1 m`: an
even-block residue is a base or a leftover according as it sits below
or above `m - k`, and an odd-block residue `ρ` is the partner of the
base `ρ - k`. -/
theorem stairMatch_residues_cover {m k : ℤ} (_hm : 1 ≤ m) (hk : 1 ≤ k)
    (hkm : k ≤ m) :
    stairBases m k ∪ stairPartners m k ∪ stairLeftover m k =
      Finset.Icc 1 m := by
  apply Finset.Subset.antisymm
  · intro x hx
    rw [Finset.mem_union, Finset.mem_union] at hx
    rw [Finset.mem_Icc]
    rcases hx with (hx | hx) | hx
    · rw [mem_stairBases] at hx; omega
    · rw [mem_stairPartners] at hx
      obtain ⟨r, hr, rfl⟩ := hx
      rw [mem_stairBases] at hr; omega
    · rw [mem_stairLeftover] at hx; omega
  · intro ρ hρ
    rw [Finset.mem_Icc] at hρ
    obtain ⟨hρ1, hρm⟩ := hρ
    rw [Finset.mem_union, Finset.mem_union]
    rcases Int.even_or_odd ((ρ - 1) / k) with hpar | hpar
    · have hpar0 : ((ρ - 1) / k) % 2 = 0 := Int.even_iff.mp hpar
      rcases lt_or_ge (m - k) ρ with hgt | hle
      · exact Or.inr
          (mem_stairLeftover.mpr ⟨by omega, hρm, hpar0⟩)
      · exact Or.inl (Or.inl (mem_stairBases.mpr ⟨hρ1, hle, hpar0⟩))
    · have hpar1 : ((ρ - 1) / k) % 2 = 1 := Int.odd_iff.mp hpar
      have hq1 : 1 ≤ (ρ - 1) / k := by
        have h0 : 0 ≤ (ρ - 1) / k :=
          Int.ediv_nonneg (by omega) (by omega)
        rcases lt_or_eq_of_le h0 with h | h
        · exact h
        · rw [← h] at hpar1
          exact absurd hpar1 (by norm_num)
      have hrk : k ≤ ρ - 1 := by
        have h := (Int.le_ediv_iff_mul_le (by omega : 0 < k)).mp hq1
        omega
      have hbmem : ρ - k ∈ stairBases m k := by
        rw [mem_stairBases]
        refine ⟨by omega, by omega, ?_⟩
        rw [stair_block_sub hk]
        have hqev : Even ((ρ - 1) / k - 1) := hpar.sub_odd odd_one
        exact Int.even_iff.mp hqev
      exact Or.inl (Or.inr
        (mem_stairPartners.mpr ⟨ρ - k, hbmem, by ring⟩))

/-- **Cardinality bookkeeping.**  The partition
`Icc 1 m = B ⊔ P ⊔ Λ` with `|P| = |B|` gives
`2·|B| + |Λ| = m₊`; in particular `|B| + |Λ| ≤ m₊` and `2·|B| ≤ m₊`. -/
theorem stairMatch_card_eq {m k : ℤ} (hm : 1 ≤ m) (hk : 1 ≤ k)
    (hkm : k ≤ m) :
    2 * (stairBases m k).card + (stairLeftover m k).card = m.toNat := by
  have hdisjP : Disjoint (stairBases m k) (stairPartners m k) :=
    stairBases_partners_disjoint hk
  have hdisjBL := stairBases_leftover_disjoint (m := m) (k := k)
  have hdisjPL : Disjoint (stairPartners m k) (stairLeftover m k) :=
    stairPartners_leftover_disjoint hk
  have hdisj : Disjoint (stairBases m k ∪ stairPartners m k)
      (stairLeftover m k) :=
    Finset.disjoint_union_left.mpr ⟨hdisjBL, hdisjPL⟩
  have hcov := stairMatch_residues_cover hm hk hkm
  have hcard : (Finset.Icc 1 m).card = m.toNat := by
    rw [Int.card_Icc]; congr 1; omega
  have hpc := stairPartners_card (m := m) (k := k)
  calc 2 * (stairBases m k).card + (stairLeftover m k).card
      = (stairBases m k).card + (stairPartners m k).card +
          (stairLeftover m k).card := by rw [hpc]; ring
    _ = (stairBases m k ∪ stairPartners m k ∪
          stairLeftover m k).card := by
        rw [Finset.card_union_of_disjoint hdisj,
          Finset.card_union_of_disjoint hdisjP]
    _ = (Finset.Icc 1 m).card := by rw [hcov]
    _ = m.toNat := hcard

/-- The base count is at most `m - k` (the crude bound used in
`stairMatchClosed`). -/
theorem stairBases_card_le {m k : ℤ} :
    (stairBases m k).card ≤ (m - k).toNat := by
  calc (stairBases m k).card
      ≤ (Finset.Icc 1 (m - k)).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
    _ = (m - k).toNat := by rw [Int.card_Icc]; congr 1; omega

/-- The leftover count is at most `k`. -/
theorem stairLeftover_card_le {m k : ℤ} :
    (stairLeftover m k).card ≤ k.toNat := by
  calc (stairLeftover m k).card
      ≤ (Finset.Icc (m - k + 1) m).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
    _ = k.toNat := by rw [Int.card_Icc]; congr 1; omega

/-- The matching partners force `2·|B| ≤ m`: bases and their distinct
`+k`-translates are disjoint subsets of `Icc 1 m`. -/
theorem stairBases_card_le_half {m k : ℤ} (hm : 1 ≤ m) (hk : 1 ≤ k)
    (hkm : k ≤ m) :
    2 * (stairBases m k).card ≤ m.toNat := by
  have h := stairMatch_card_eq hm hk hkm
  omega

/-! ### Rail-length bookkeeping along the matching -/

/-- The rail lengths summed over the whole matching equal `(n-m)₊` —
the matching partition of `Icc 1 m` composed with `sum_cls_card`. -/
theorem sum_L_stairMatch {n : ℕ} {m k : ℤ} (hm : 1 ≤ m) (hk : 1 ≤ k)
    (hkm : k ≤ m) :
    (∑ r ∈ stairBases m k, (((n : ℤ) - r) / m).toNat) +
        (∑ x ∈ stairPartners m k, (((n : ℤ) - x) / m).toNat) +
      ∑ ρ ∈ stairLeftover m k, (((n : ℤ) - ρ) / m).toNat =
        ((n : ℤ) - m).toNat := by
  have hdisjP : Disjoint (stairBases m k) (stairPartners m k) :=
    stairBases_partners_disjoint hk
  have hdisjBL := stairBases_leftover_disjoint (m := m) (k := k)
  have hdisjPL : Disjoint (stairPartners m k) (stairLeftover m k) :=
    stairPartners_leftover_disjoint hk
  have hdisj : Disjoint (stairBases m k ∪ stairPartners m k)
      (stairLeftover m k) :=
    Finset.disjoint_union_left.mpr ⟨hdisjBL, hdisjPL⟩
  have hcov := stairMatch_residues_cover hm hk hkm
  calc (∑ r ∈ stairBases m k, (((n : ℤ) - r) / m).toNat) +
          (∑ x ∈ stairPartners m k, (((n : ℤ) - x) / m).toNat) +
        ∑ ρ ∈ stairLeftover m k, (((n : ℤ) - ρ) / m).toNat
      = (∑ r ∈ stairBases m k ∪ stairPartners m k,
            (((n : ℤ) - r) / m).toNat) +
          ∑ ρ ∈ stairLeftover m k, (((n : ℤ) - ρ) / m).toNat := by
        rw [Finset.sum_union hdisjP]
    _ = ∑ x ∈ stairBases m k ∪ stairPartners m k ∪
            stairLeftover m k, (((n : ℤ) - x) / m).toNat :=
        (Finset.sum_union hdisj).symm
    _ = ∑ x ∈ Finset.Icc 1 m, (((n : ℤ) - x) / m).toNat := by
        rw [hcov]
    _ = ((n : ℤ) - m).toNat := sum_cls_card hm

/-- The partner rail is at most one level shorter than its base:
`L_r ≤ L_{r+k} + 1`, since `(n - r - k)/m ≥ (n - r - m)/m = (n-r)/m - 1`
for `k ≤ m`. -/
theorem stair_L_le_partner_add_one {n : ℕ} {m k r : ℤ} (hm : 1 ≤ m)
    (hkm : k ≤ m) :
    (((n : ℤ) - r) / m).toNat ≤
      (((n : ℤ) - (r + k)) / m).toNat + 1 := by
  have hpos : 0 < m := by omega
  have hstep : ((n : ℤ) - r - m) / m = ((n : ℤ) - r) / m - 1 := by
    have e : (n : ℤ) - r - m = ((n : ℤ) - r) + m * (-1) := by ring
    rw [e, Int.add_mul_ediv_left _ _ (ne_of_gt hpos)]
    ring
  have hle : ((n : ℤ) - r) / m - 1 ≤ ((n : ℤ) - (r + k)) / m := by
    rw [← hstep]
    exact Int.ediv_le_ediv hpos (by omega)
  have h2 := Int.toNat_le_toNat hle
  rw [Int.pred_toNat] at h2
  omega

/-- Sum version: the partner-rail total is at least the base total
minus `|B|` (each partner loses at most one level). -/
theorem sum_L_stairPartners_ge {n : ℕ} {m k : ℤ} (hm : 1 ≤ m)
    (hkm : k ≤ m) :
    (∑ r ∈ stairBases m k, (((n : ℤ) - r) / m).toNat) -
        (stairBases m k).card ≤
      ∑ x ∈ stairPartners m k, (((n : ℤ) - x) / m).toNat := by
  rw [stairPartners_sum_L]
  have h := Finset.sum_le_sum (s := stairBases m k)
    (fun r _ => stair_L_le_partner_add_one (n := n) (m := m) (k := k)
      (r := r) hm hkm)
  rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul,
    mul_one] at h
  omega

/-- **Sum bookkeeping, bases.**  Since `Σ_B + Σ_P + Σ_Λ = (n−m)₊` and
`Σ_P ≥ Σ_B − |B|`, the doubled base sum plus the leftover sum is at
most `(n−m)₊ + |B|` — the `5`-power budget of the matched pairs is only
*half* the total rail length. -/
theorem sum_L_bases_le {n : ℕ} {m k : ℤ} (hm : 1 ≤ m) (hk : 1 ≤ k)
    (hkm : k ≤ m) :
    2 * (∑ r ∈ stairBases m k, (((n : ℤ) - r) / m).toNat) +
        (∑ ρ ∈ stairLeftover m k, (((n : ℤ) - ρ) / m).toNat) ≤
      ((n : ℤ) - m).toNat + (stairBases m k).card := by
  have hpart := sum_L_stairMatch (n := n) hm hk hkm
  have hge := sum_L_stairPartners_ge (n := n) hm hkm
  omega

/-- Halved corollary of `sum_L_bases_le`. -/
theorem sum_L_bases_le_div_two {n : ℕ} {m k : ℤ} (hm : 1 ≤ m)
    (hk : 1 ≤ k) (hkm : k ≤ m) :
    (∑ r ∈ stairBases m k, (((n : ℤ) - r) / m).toNat) ≤
      (((n : ℤ) - m).toNat + (stairBases m k).card) / 2 := by
  have h := sum_L_bases_le (n := n) hm hk hkm
  omega

/-- **Sum bookkeeping, leftover.**  The leftover rail lengths are part
of the `Icc 1 m` partition, hence sum to at most `(n−m)₊`. -/
theorem sum_L_leftover_le {n : ℕ} {m k : ℤ} (hm : 1 ≤ m) (_hk : 1 ≤ k)
    (_hkm : k ≤ m) :
    ∑ ρ ∈ stairLeftover m k, (((n : ℤ) - ρ) / m).toNat ≤
      ((n : ℤ) - m).toNat := by
  have hsub : stairLeftover m k ⊆ Finset.Icc 1 m := by
    intro x hx
    rw [mem_stairLeftover] at hx
    rw [Finset.mem_Icc]
    omega
  calc ∑ ρ ∈ stairLeftover m k, (((n : ℤ) - ρ) / m).toNat
      ≤ ∑ x ∈ Finset.Icc 1 m, (((n : ℤ) - x) / m).toNat :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun x _ _ => Nat.zero_le _)
    _ = ((n : ℤ) - m).toNat := sum_cls_card hm

/-- Every leftover rail has `ρ ≥ m - k + 1`, hence length at most
`((n - m + k - 1)/m)₊`. -/
theorem stair_L_leftover_le {n : ℕ} {m k ρ : ℤ} (hm : 1 ≤ m)
    (hρ : ρ ∈ stairLeftover m k) :
    (((n : ℤ) - ρ) / m).toNat ≤
      (((n : ℤ) - (m - k + 1)) / m).toNat := by
  rw [mem_stairLeftover] at hρ
  exact Int.toNat_le_toNat (Int.ediv_le_ediv (by omega) (by omega))

/-- Sharper leftover bound: `Σ_Λ L ≤ |Λ|·((n-m+k-1)/m)₊` — the leftover
rails are all short when `k` is small relative to `n`. -/
theorem sum_L_leftover_le_card_mul {n : ℕ} {m k : ℤ} (hm : 1 ≤ m) :
    ∑ ρ ∈ stairLeftover m k, (((n : ℤ) - ρ) / m).toNat ≤
      (stairLeftover m k).card *
        (((n : ℤ) - (m - k + 1)) / m).toNat := by
  calc ∑ ρ ∈ stairLeftover m k, (((n : ℤ) - ρ) / m).toNat
      ≤ ∑ _ρ ∈ stairLeftover m k,
          (((n : ℤ) - (m - k + 1)) / m).toNat :=
        Finset.sum_le_sum fun ρ hρ => stair_L_leftover_le hm hρ
    _ = (stairLeftover m k).card *
          (((n : ℤ) - (m - k + 1)) / m).toNat := by
        rw [Finset.sum_const, smul_eq_mul]

/-! ### The sharp staircase-matching bounds -/

/-- `2^u ≤ 2·5^{u/2}`: writing `u = 2·(u/2) + u%2` gives
`2^u = 4^{u/2}·2^{u%2} ≤ 5^{u/2}·2`.  Used to fold the leftover `2`-rate
under the uniform `√5` rate. -/
theorem two_pow_le_two_mul_five_pow_half (u : ℕ) :
    2 ^ u ≤ 2 * 5 ^ (u / 2) := by
  have h : 2 ^ u = 4 ^ (u / 2) * 2 ^ (u % 2) := by
    conv_lhs => rw [← Nat.div_add_mod u 2]
    rw [pow_add, pow_mul, show (2 : ℕ) ^ 2 = 4 by norm_num]
  rw [h]
  calc 4 ^ (u / 2) * 2 ^ (u % 2)
      ≤ 5 ^ (u / 2) * 2 := by
        apply Nat.mul_le_mul
          (Nat.pow_le_pow_left (show (4 : ℕ) ≤ 5 by norm_num) _)
        have h2 : u % 2 ≤ 1 := by omega
        calc 2 ^ (u % 2) ≤ 2 ^ 1 :=
              Nat.pow_le_pow_right (by norm_num) h2
          _ = 2 := pow_one 2
    _ = 2 * 5 ^ (u / 2) := by ring

/-- **The sharp staircase-matching bound (product form).**  Each
matched pair contributes `a(L_r) ≤ 4·5^{L_r-1}` and each leftover rail
`F_{L+2} ≤ 2^{L+1}`:

  `card ≤ 4^{|B|} · 5^{Σ_B (L_r - 1)} · 2^{Σ_Λ (L_ρ + 1)}`.

Since `Σ_B L` is only about half the total rail length
(`sum_L_bases_le`), the `5`-exponent is roughly halved versus
`stairMatchClosed`. -/
theorem card_powerset_filter_shiftFree2_Icc_le_stairMatchSharp {n : ℕ}
    {m k : ℤ} (hm : 1 ≤ m) (hk : 1 ≤ k) (hkm : k < m) :
    ((Finset.Icc (m + 1) (n : ℤ)).powerset.filter
        (shiftFree2 m (m + k))).card ≤
      4 ^ (stairBases m k).card *
        5 ^ (∑ r ∈ stairBases m k,
          ((((n : ℤ) - r) / m).toNat - 1)) *
        2 ^ (∑ ρ ∈ stairLeftover m k,
          ((((n : ℤ) - ρ) / m).toNat + 1)) := by
  have hprod :=
    card_powerset_filter_shiftFree2_Icc_le_stairMatchProd (n := n) hm hk hkm
  refine hprod.trans ?_
  refine Nat.mul_le_mul ?_ ?_
  · calc ∏ r ∈ stairBases m k,
          (stairSets (((n : ℤ) - r) / m).toNat).card
        ≤ ∏ r ∈ stairBases m k,
            4 * 5 ^ ((((n : ℤ) - r) / m).toNat - 1) :=
          Finset.prod_le_prod fun r _ =>
            stairSets_card_le_four_mul_five_pow_sub_one _
      _ = 4 ^ (stairBases m k).card *
            5 ^ (∑ r ∈ stairBases m k,
              ((((n : ℤ) - r) / m).toNat - 1)) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const,
            Finset.prod_pow_eq_pow_sum]
  · calc ∏ ρ ∈ stairLeftover m k,
          Nat.fib ((((n : ℤ) - ρ) / m).toNat + 2)
        ≤ ∏ ρ ∈ stairLeftover m k,
            2 ^ ((((n : ℤ) - ρ) / m).toNat + 1) :=
          Finset.prod_le_prod fun ρ _ => fib_add_two_le_two_pow' _
      _ = 2 ^ (∑ ρ ∈ stairLeftover m k,
            ((((n : ℤ) - ρ) / m).toNat + 1)) := by
          rw [Finset.prod_pow_eq_pow_sum]

/-- **The sharp bound in multiplied (rate-`5/2`) form.**  Keeping the
`2^{L-1}` denominators on the left — in the `_mul_le` style of
`TriBridge.lean` — records the honest per-pair rate `5/2`:
`card·2^{Σ_B(L_r-1)} ≤ 4^{|B|}·5^{Σ_B(L_r-1)}·2^{Σ_Λ(L_ρ+1)}`. -/
theorem card_powerset_filter_shiftFree2_Icc_mul_two_pow_le_stairMatch
    {n : ℕ} {m k : ℤ} (hm : 1 ≤ m) (hk : 1 ≤ k) (hkm : k < m) :
    ((Finset.Icc (m + 1) (n : ℤ)).powerset.filter
        (shiftFree2 m (m + k))).card *
        2 ^ (∑ r ∈ stairBases m k,
          ((((n : ℤ) - r) / m).toNat - 1)) ≤
      4 ^ (stairBases m k).card *
        5 ^ (∑ r ∈ stairBases m k,
          ((((n : ℤ) - r) / m).toNat - 1)) *
        2 ^ (∑ ρ ∈ stairLeftover m k,
          ((((n : ℤ) - ρ) / m).toNat + 1)) := by
  have hprod :=
    card_powerset_filter_shiftFree2_Icc_le_stairMatchProd (n := n) hm hk hkm
  have hA : (∏ r ∈ stairBases m k,
          (stairSets (((n : ℤ) - r) / m).toNat).card) *
        2 ^ (∑ r ∈ stairBases m k, ((((n : ℤ) - r) / m).toNat - 1)) ≤
      4 ^ (stairBases m k).card *
        5 ^ (∑ r ∈ stairBases m k, ((((n : ℤ) - r) / m).toNat - 1)) := by
    calc (∏ r ∈ stairBases m k,
            (stairSets (((n : ℤ) - r) / m).toNat).card) *
          2 ^ (∑ r ∈ stairBases m k, ((((n : ℤ) - r) / m).toNat - 1))
        = ∏ r ∈ stairBases m k,
            ((stairSets (((n : ℤ) - r) / m).toNat).card *
              2 ^ ((((n : ℤ) - r) / m).toNat - 1)) := by
          rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
      _ ≤ ∏ r ∈ stairBases m k,
            4 * 5 ^ ((((n : ℤ) - r) / m).toNat - 1) :=
          Finset.prod_le_prod fun r _ =>
            stairSets_card_mul_two_pow_le' _
      _ = 4 ^ (stairBases m k).card *
            5 ^ (∑ r ∈ stairBases m k,
              ((((n : ℤ) - r) / m).toNat - 1)) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const,
            Finset.prod_pow_eq_pow_sum]
  have hB : ∏ ρ ∈ stairLeftover m k,
          Nat.fib ((((n : ℤ) - ρ) / m).toNat + 2) ≤
      2 ^ (∑ ρ ∈ stairLeftover m k, ((((n : ℤ) - ρ) / m).toNat + 1)) := by
    calc ∏ ρ ∈ stairLeftover m k,
          Nat.fib ((((n : ℤ) - ρ) / m).toNat + 2)
        ≤ ∏ ρ ∈ stairLeftover m k,
            2 ^ ((((n : ℤ) - ρ) / m).toNat + 1) :=
          Finset.prod_le_prod fun ρ _ => fib_add_two_le_two_pow' _
      _ = 2 ^ (∑ ρ ∈ stairLeftover m k,
            ((((n : ℤ) - ρ) / m).toNat + 1)) := by
          rw [Finset.prod_pow_eq_pow_sum]
  calc ((Finset.Icc (m + 1) (n : ℤ)).powerset.filter
          (shiftFree2 m (m + k))).card *
        2 ^ (∑ r ∈ stairBases m k, ((((n : ℤ) - r) / m).toNat - 1))
      ≤ ((∏ r ∈ stairBases m k,
              (stairSets (((n : ℤ) - r) / m).toNat).card) *
            ∏ ρ ∈ stairLeftover m k,
              Nat.fib ((((n : ℤ) - ρ) / m).toNat + 2)) *
          2 ^ (∑ r ∈ stairBases m k, ((((n : ℤ) - r) / m).toNat - 1)) :=
        Nat.mul_le_mul hprod (le_refl _)
    _ = ((∏ r ∈ stairBases m k,
              (stairSets (((n : ℤ) - r) / m).toNat).card) *
            2 ^ (∑ r ∈ stairBases m k,
              ((((n : ℤ) - r) / m).toNat - 1))) *
          ∏ ρ ∈ stairLeftover m k,
              Nat.fib ((((n : ℤ) - ρ) / m).toNat + 2) := by ring
    _ ≤ (4 ^ (stairBases m k).card *
            5 ^ (∑ r ∈ stairBases m k,
              ((((n : ℤ) - r) / m).toNat - 1))) *
          2 ^ (∑ ρ ∈ stairLeftover m k,
            ((((n : ℤ) - ρ) / m).toNat + 1)) :=
        Nat.mul_le_mul hA hB
    _ = 4 ^ (stairBases m k).card *
        5 ^ (∑ r ∈ stairBases m k, ((((n : ℤ) - r) / m).toNat - 1)) *
        2 ^ (∑ ρ ∈ stairLeftover m k,
          ((((n : ℤ) - ρ) / m).toNat + 1)) := by ring

/-- **Closed form of the sharp bound.**  Folding the leftover `2`-rate
under `√5` (`2^u ≤ 2·5^{u/2}`) and using
`2·Σ_B L + Σ_Λ L ≤ (n−m)₊ + |B|` gives a single `√5`-rate:

  `card ≤ 4^{(m-k)₊}·2^{k₊}·5^{((n-m)₊ + m₊)/2}`.

For `m ≤ n` the `5`-exponent is `≤ n/2`, i.e.
`card = O(4^{m-k}·2^k·(√5)^n)` versus the loose
`4^{m-k}·5^{n-m}·2^k` of `stairMatchClosed`. -/
theorem card_powerset_filter_shiftFree2_Icc_le_stairMatchSharpClosed
    {n : ℕ} {m k : ℤ} (hm : 1 ≤ m) (hk : 1 ≤ k) (hkm : k < m) :
    ((Finset.Icc (m + 1) (n : ℤ)).powerset.filter
        (shiftFree2 m (m + k))).card ≤
      4 ^ (m - k).toNat * 2 ^ k.toNat *
        5 ^ ((((n : ℤ) - m).toNat + m.toNat) / 2) := by
  have hsharp :=
    card_powerset_filter_shiftFree2_Icc_le_stairMatchSharp (n := n) hm hk hkm
  have hcardB := stairBases_card_le (m := m) (k := k)
  have hcardL := stairLeftover_card_le (m := m) (k := k)
  have hcard := stairMatch_card_eq (m := m) (k := k) hm hk (le_of_lt hkm)
  have hsum := sum_L_bases_le (n := n) hm hk (le_of_lt hkm)
  -- fold the leftover `2`-power under `√5`
  have hB : 2 ^ (∑ ρ ∈ stairLeftover m k,
          ((((n : ℤ) - ρ) / m).toNat + 1)) ≤
      2 ^ (stairLeftover m k).card *
        5 ^ (∑ ρ ∈ stairLeftover m k,
          ((((n : ℤ) - ρ) / m).toNat + 1) / 2) := by
    calc 2 ^ (∑ ρ ∈ stairLeftover m k, ((((n : ℤ) - ρ) / m).toNat + 1))
        = ∏ ρ ∈ stairLeftover m k,
            2 ^ ((((n : ℤ) - ρ) / m).toNat + 1) :=
          (Finset.prod_pow_eq_pow_sum _ _ _).symm
      _ ≤ ∏ ρ ∈ stairLeftover m k,
            2 * 5 ^ (((((n : ℤ) - ρ) / m).toNat + 1) / 2) :=
          Finset.prod_le_prod fun ρ _ =>
            two_pow_le_two_mul_five_pow_half _
      _ = 2 ^ (stairLeftover m k).card *
            5 ^ (∑ ρ ∈ stairLeftover m k,
              ((((n : ℤ) - ρ) / m).toNat + 1) / 2) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const,
            Finset.prod_pow_eq_pow_sum]
  -- exponent bookkeeping: `2·(E + G) ≤ (n-m)₊ + |B| + |Λ|`
  have hE : (∑ r ∈ stairBases m k, ((((n : ℤ) - r) / m).toNat - 1)) ≤
      ∑ r ∈ stairBases m k, (((n : ℤ) - r) / m).toNat :=
    Finset.sum_le_sum fun r _ => Nat.sub_le _ _
  have hG : 2 * (∑ ρ ∈ stairLeftover m k,
          ((((n : ℤ) - ρ) / m).toNat + 1) / 2) ≤
      (∑ ρ ∈ stairLeftover m k, (((n : ℤ) - ρ) / m).toNat) +
        (stairLeftover m k).card := by
    have h2 : 2 * (∑ ρ ∈ stairLeftover m k,
          ((((n : ℤ) - ρ) / m).toNat + 1) / 2) =
        ∑ ρ ∈ stairLeftover m k,
          2 * (((((n : ℤ) - ρ) / m).toNat + 1) / 2) := by
      rw [Finset.mul_sum]
    rw [h2]
    calc ∑ ρ ∈ stairLeftover m k,
          2 * (((((n : ℤ) - ρ) / m).toNat + 1) / 2)
        ≤ ∑ ρ ∈ stairLeftover m k,
            ((((n : ℤ) - ρ) / m).toNat + 1) :=
          Finset.sum_le_sum fun ρ _ => by omega
      _ = (∑ ρ ∈ stairLeftover m k, (((n : ℤ) - ρ) / m).toNat) +
            (stairLeftover m k).card := by
          rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul,
            mul_one]
  have hEG : (∑ r ∈ stairBases m k, ((((n : ℤ) - r) / m).toNat - 1)) +
        (∑ ρ ∈ stairLeftover m k,
          ((((n : ℤ) - ρ) / m).toNat + 1) / 2) ≤
      (((n : ℤ) - m).toNat + (stairBases m k).card +
        (stairLeftover m k).card) / 2 := by
    omega
  have hdiv : (((n : ℤ) - m).toNat + (stairBases m k).card +
        (stairLeftover m k).card) / 2 ≤
      (((n : ℤ) - m).toNat + m.toNat) / 2 := by
    omega
  calc ((Finset.Icc (m + 1) (n : ℤ)).powerset.filter
          (shiftFree2 m (m + k))).card
      ≤ 4 ^ (stairBases m k).card *
          5 ^ (∑ r ∈ stairBases m k,
            ((((n : ℤ) - r) / m).toNat - 1)) *
          2 ^ (∑ ρ ∈ stairLeftover m k,
            ((((n : ℤ) - ρ) / m).toNat + 1)) := hsharp
    _ ≤ 4 ^ (stairBases m k).card *
          5 ^ (∑ r ∈ stairBases m k,
            ((((n : ℤ) - r) / m).toNat - 1)) *
          (2 ^ (stairLeftover m k).card *
            5 ^ (∑ ρ ∈ stairLeftover m k,
              ((((n : ℤ) - ρ) / m).toNat + 1) / 2)) :=
        Nat.mul_le_mul (le_refl _) hB
    _ = 4 ^ (stairBases m k).card * 2 ^ (stairLeftover m k).card *
          5 ^ ((∑ r ∈ stairBases m k, ((((n : ℤ) - r) / m).toNat - 1)) +
            (∑ ρ ∈ stairLeftover m k,
              ((((n : ℤ) - ρ) / m).toNat + 1) / 2)) := by
        rw [pow_add]; ring
    _ ≤ 4 ^ (stairBases m k).card * 2 ^ (stairLeftover m k).card *
          5 ^ ((((n : ℤ) - m).toNat + (stairBases m k).card +
            (stairLeftover m k).card) / 2) :=
        Nat.mul_le_mul (le_refl _)
          (Nat.pow_le_pow_right (show (0 : ℕ) < 5 by norm_num) hEG)
    _ ≤ 4 ^ (m - k).toNat * 2 ^ k.toNat *
          5 ^ ((((n : ℤ) - m).toNat + m.toNat) / 2) :=
        Nat.mul_le_mul
          (Nat.mul_le_mul
            (Nat.pow_le_pow_right (show (0 : ℕ) < 4 by norm_num) hcardB)
            (Nat.pow_le_pow_right (show (0 : ℕ) < 2 by norm_num) hcardL))
          (Nat.pow_le_pow_right (show (0 : ℕ) < 5 by norm_num) hdiv)

/-- **Per-cell corollary.**  `secondMinClass n m (m+k)` injects into the
double-shift-free subsets of `Icc (m+1) n`, so the sharp closed bound
applies per cell. -/
theorem secondMinClass_card_le_stairMatchSharpClosed {n : ℕ} {m k : ℤ}
    (hm : 1 ≤ m) (hk : 1 ≤ k) (hkm : k < m) :
    (secondMinClass n m (m + k)).card ≤
      4 ^ (m - k).toNat * 2 ^ k.toNat *
        5 ^ ((((n : ℤ) - m).toNat + m.toNat) / 2) :=
  secondMinClass_card_le_stairProd_conditional (by omega)
    (card_powerset_filter_shiftFree2_Icc_le_stairMatchSharpClosed
      (n := n) hm hk hkm)

/-! ### The real-valued `√(5/2)`/`φ` sharpening -/

/-- `a(L) ≤ 4·(5/2)^{L-1}` over ℝ (ℕ-truncated exponent), the divided
form of `a(L)·2^{L-1} ≤ 4·5^{L-1}`. -/
theorem stairSets_card_le_four_mul_five_div_two_pow (L : ℕ) :
    ((stairSets L).card : ℝ) ≤ 4 * (5 / 2 : ℝ) ^ (L - 1) := by
  have h := stairSets_card_mul_two_pow_le' L
  have h2 : (0 : ℝ) < (2 : ℝ) ^ (L - 1) := pow_pos (by norm_num) _
  calc ((stairSets L).card : ℝ)
      ≤ 4 * (5 : ℝ) ^ (L - 1) / (2 : ℝ) ^ (L - 1) := by
        rw [le_div_iff₀ h2]
        exact_mod_cast h
    _ = 4 * (5 / 2 : ℝ) ^ (L - 1) := by
        rw [div_pow, mul_div_assoc]

/-- `5/2 ≤ φ² = φ + 1` (since `φ = (1 + √5)/2 ≥ 3/2`), hence
`(5/2)^e ≤ φ^{2e}`: the matched-pair rate `√(5/2)` per element is below
the golden ratio. -/
theorem five_half_pow_le_goldenRatio_sq_pow (e : ℕ) :
    (5 / 2 : ℝ) ^ e ≤ Real.goldenRatio ^ (2 * e) := by
  have hsqrt : (2 : ℝ) ≤ Real.sqrt 5 := by
    rw [Real.le_sqrt' (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have hφ3 : (3 : ℝ) / 2 ≤ Real.goldenRatio := by
    show (3 : ℝ) / 2 ≤ (1 + Real.sqrt 5) / 2
    linarith
  have hφ : (5 / 2 : ℝ) ≤ Real.goldenRatio ^ 2 := by
    rw [Real.goldenRatio_sq]
    linarith
  calc (5 / 2 : ℝ) ^ e ≤ (Real.goldenRatio ^ 2) ^ e :=
        pow_le_pow_left₀ (by norm_num) hφ e
    _ = Real.goldenRatio ^ (2 * e) := by rw [← pow_mul]

/-- **The golden-ratio closed bound.**  Matching the pair rate
`(5/2)^{L-1} ≤ φ^{2(L-1)}` against `F_{L+2} ≤ φ^{L+1}` on the leftover
and using `2·Σ_B(L-1) + Σ_Λ(L+1) ≤ (n-m)₊ + |B| + |Λ|`:

  `card ≤ 4^{|B|}·φ^{(n-m)₊+|B|+|Λ|} ≤ 4^{(m-k)₊}·φ^{(n-m)₊+m₊}` —
exponent `log₂ φ ≈ 0.694` per element of `Icc (m+1) n`. -/
theorem card_powerset_filter_shiftFree2_Icc_le_stairMatchSharp_real
    {n : ℕ} {m k : ℤ} (hm : 1 ≤ m) (hk : 1 ≤ k) (hkm : k < m) :
    (((Finset.Icc (m + 1) (n : ℤ)).powerset.filter
        (shiftFree2 m (m + k))).card : ℝ) ≤
      (4 : ℝ) ^ (m - k).toNat *
        Real.goldenRatio ^ (((n : ℤ) - m).toNat + m.toNat) := by
  have hprod :=
    card_powerset_filter_shiftFree2_Icc_le_stairMatchProd (n := n) hm hk hkm
  have hcardB := stairBases_card_le (m := m) (k := k)
  have hcard := stairMatch_card_eq (m := m) (k := k) hm hk (le_of_lt hkm)
  have hsum := sum_L_bases_le (n := n) hm hk (le_of_lt hkm)
  have hA : (∏ r ∈ stairBases m k,
          ((stairSets (((n : ℤ) - r) / m).toNat).card : ℝ)) ≤
      ∏ r ∈ stairBases m k,
        4 * Real.goldenRatio ^
          (2 * ((((n : ℤ) - r) / m).toNat - 1)) := by
    apply Finset.prod_le_prod₀
    · intro r _
      exact Nat.cast_nonneg _
    · intro r _
      exact (stairSets_card_le_four_mul_five_div_two_pow _).trans
        (mul_le_mul_of_nonneg_left
          (five_half_pow_le_goldenRatio_sq_pow _) (by norm_num))
  have hB : (∏ ρ ∈ stairLeftover m k,
          (Nat.fib ((((n : ℤ) - ρ) / m).toNat + 2) : ℝ)) ≤
      ∏ ρ ∈ stairLeftover m k,
        Real.goldenRatio ^ ((((n : ℤ) - ρ) / m).toNat + 1) := by
    apply Finset.prod_le_prod₀
    · intro ρ _
      exact Nat.cast_nonneg _
    · intro ρ _
      refine (fib_add_two_le_goldenRatio_pow _).trans ?_
      apply pow_le_pow_right₀ Real.one_lt_goldenRatio.le
      split_ifs <;> omega
  have hexp : 2 * (∑ r ∈ stairBases m k,
          ((((n : ℤ) - r) / m).toNat - 1)) +
        (∑ ρ ∈ stairLeftover m k, ((((n : ℤ) - ρ) / m).toNat + 1)) ≤
      ((n : ℤ) - m).toNat + (stairBases m k).card +
        (stairLeftover m k).card := by
    have hE : 2 * (∑ r ∈ stairBases m k,
            ((((n : ℤ) - r) / m).toNat - 1)) ≤
        2 * ∑ r ∈ stairBases m k, (((n : ℤ) - r) / m).toNat :=
      Nat.mul_le_mul (le_refl 2)
        (Finset.sum_le_sum fun r _ => Nat.sub_le _ _)
    have hF : (∑ ρ ∈ stairLeftover m k,
            ((((n : ℤ) - ρ) / m).toNat + 1)) =
        (∑ ρ ∈ stairLeftover m k, (((n : ℤ) - ρ) / m).toNat) +
          (stairLeftover m k).card := by
      rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul,
        mul_one]
    omega
  have hexp2 : ((n : ℤ) - m).toNat + (stairBases m k).card +
        (stairLeftover m k).card ≤
      ((n : ℤ) - m).toNat + m.toNat := by
    omega
  have h1 : ∏ r ∈ stairBases m k,
        4 * Real.goldenRatio ^ (2 * ((((n : ℤ) - r) / m).toNat - 1)) =
      (4 : ℝ) ^ (stairBases m k).card *
        Real.goldenRatio ^ (2 * ∑ r ∈ stairBases m k,
          ((((n : ℤ) - r) / m).toNat - 1)) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const,
      Finset.prod_pow_eq_pow_sum, Finset.mul_sum]
  have h2 : ∏ ρ ∈ stairLeftover m k,
        Real.goldenRatio ^ ((((n : ℤ) - ρ) / m).toNat + 1) =
      Real.goldenRatio ^ (∑ ρ ∈ stairLeftover m k,
        ((((n : ℤ) - ρ) / m).toNat + 1)) :=
    Finset.prod_pow_eq_pow_sum _ _ _
  calc (((Finset.Icc (m + 1) (n : ℤ)).powerset.filter
          (shiftFree2 m (m + k))).card : ℝ)
      ≤ (∏ r ∈ stairBases m k,
            ((stairSets (((n : ℤ) - r) / m).toNat).card : ℝ)) *
          ∏ ρ ∈ stairLeftover m k,
            (Nat.fib ((((n : ℤ) - ρ) / m).toNat + 2) : ℝ) := by
        exact_mod_cast hprod
    _ ≤ (∏ r ∈ stairBases m k,
            4 * Real.goldenRatio ^
              (2 * ((((n : ℤ) - r) / m).toNat - 1))) *
          ∏ ρ ∈ stairLeftover m k,
            Real.goldenRatio ^ ((((n : ℤ) - ρ) / m).toNat + 1) :=
        mul_le_mul hA hB
          (Finset.prod_nonneg fun ρ _ => Nat.cast_nonneg _)
          (Finset.prod_nonneg fun r _ =>
            mul_nonneg (by norm_num)
              (pow_nonneg Real.goldenRatio_pos.le _))
    _ = ((4 : ℝ) ^ (stairBases m k).card *
            Real.goldenRatio ^ (2 * (∑ r ∈ stairBases m k,
              ((((n : ℤ) - r) / m).toNat - 1)))) *
          Real.goldenRatio ^ (∑ ρ ∈ stairLeftover m k,
            ((((n : ℤ) - ρ) / m).toNat + 1)) := by
        rw [h1, h2]
    _ = (4 : ℝ) ^ (stairBases m k).card *
          Real.goldenRatio ^
            (2 * (∑ r ∈ stairBases m k,
              ((((n : ℤ) - r) / m).toNat - 1)) +
              (∑ ρ ∈ stairLeftover m k,
                ((((n : ℤ) - ρ) / m).toNat + 1))) := by
        rw [pow_add]; ring
    _ ≤ (4 : ℝ) ^ (stairBases m k).card *
          Real.goldenRatio ^
            (((n : ℤ) - m).toNat + (stairBases m k).card +
              (stairLeftover m k).card) :=
        mul_le_mul (le_refl _)
          (pow_le_pow_right₀ Real.one_lt_goldenRatio.le hexp)
          (pow_nonneg Real.goldenRatio_pos.le _)
          (pow_nonneg (by norm_num : (0 : ℝ) ≤ 4) _)
    _ ≤ (4 : ℝ) ^ (m - k).toNat *
          Real.goldenRatio ^ (((n : ℤ) - m).toNat + m.toNat) :=
        mul_le_mul
          (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) hcardB)
          (pow_le_pow_right₀ Real.one_lt_goldenRatio.le hexp2)
          (pow_nonneg Real.goldenRatio_pos.le _)
          (pow_nonneg (by norm_num : (0 : ℝ) ≤ 4) _)

/-- **Per-cell corollary over ℝ.**  `secondMinClass n m (m+k)` injects
into the double-shift-free subsets of `Icc (m+1) n`, so the golden-ratio
bound applies per cell:
`(secondMinClass n m (m+k)).card ≤ 4^{(m-k)₊}·φ^{(n-m)₊+m₊}`. -/
theorem secondMinClass_card_le_stairMatchSharp_real {n : ℕ} {m k : ℤ}
    (hm : 1 ≤ m) (hk : 1 ≤ k) (hkm : k < m) :
    ((secondMinClass n m (m + k)).card : ℝ) ≤
      (4 : ℝ) ^ (m - k).toNat *
        Real.goldenRatio ^ (((n : ℤ) - m).toNat + m.toNat) := by
  have hle := secondMinClass_card_le_stairProd_conditional
    (n := n) (m := m) (s := m + k) (by omega)
    (le_refl ((Finset.Icc (m + 1) (n : ℤ)).powerset.filter
      (shiftFree2 m (m + k))).card)
  have hreal :=
    card_powerset_filter_shiftFree2_Icc_le_stairMatchSharp_real
      (n := n) hm hk hkm
  calc ((secondMinClass n m (m + k)).card : ℝ)
      ≤ (((Finset.Icc (m + 1) (n : ℤ)).powerset.filter
          (shiftFree2 m (m + k))).card : ℝ) := by
        exact_mod_cast hle
    _ ≤ (4 : ℝ) ^ (m - k).toNat *
          Real.goldenRatio ^ (((n : ℤ) - m).toNat + m.toNat) := hreal

end JSP000728
