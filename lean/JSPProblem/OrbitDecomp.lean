import JSPProblem.TwoMin
import JSPProblem.NoConsec
import JSPProblem.RailPairing
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.GCD.Basic

/-!
# JSP-000728 — orbit decomposition of the `+m` map on the mod-`s` rails

Fix `1 ≤ m < s`.  The residue classes `cls n s r` (`r ∈ Icc 1 s`) partition
`Icc (s + 1) n` into `s` "rails": the `s`-shift acts inside each rail, while
the `m`-shift carries rail `r` to rail `(r - 1 + m) % s + 1`.  Iterating, the
`m`-shift splits the `s` rails into `gcd (m, s)` disjoint *orbits*, each of
`c = s / gcd (m, s)` rails.

* `orbitRep m s r k` : the `k`-th iterate `(r - 1 + k·m) % s + 1 ∈ [1, s]`.
* `orbit m s r` : the finset of rail representatives reached from `r`.
* `orbitLen m s = s.toNat / Int.gcd s m` : the common orbit length.
* Membership/periodicity: `mem_orbit`, `orbit_self_mem`,
  `orbit_subset_Icc`, `orbitRep_mod_toNat`, `orbitRep_mod_orbitLen`,
  `orbitRep_add_orbitLen`, `orbitRep_injective_on`, `orbit_card`,
  `orbit_eq_image_orbitLen`.
* Partition: `orbit_subset_of_mem`, `mem_orbit_symm`, `orbit_eq_of_mem`,
  `orbit_eq_or_disjoint`, `orbit_image_pairwiseDisjoint`.
* `Icc_subset_biUnion_orbitCls` : `Icc (s+1) n` is covered by the orbit
  unions `O.biUnion (cls n s)` as `O` ranges over the distinct orbits.
* `card_powerset_filter_shiftFree2_Icc_le_orbitProd` : conditional product
  bound — given a per-orbit estimate `B O`, the `shiftFree2 m s` subsets of
  `Icc (s+1) n` are at most `∏ O, B O`.
-/

namespace JSP000728

/-- The `k`-th iterate of the `+m` map on rail representatives:
`r ↦ (r - 1 + k·m) % s + 1`, valued in `[1, s]` whenever `s ≥ 1`. -/
def orbitRep (m s : ℤ) (r : ℤ) (k : ℕ) : ℤ := (r - 1 + (k : ℤ) * m) % s + 1

/-- The orbit of rail `r` under `+m`, as a finset of residues.  Every
iterate is captured since `orbitRep` is `s.toNat`-periodic in `k`. -/
def orbit (m s : ℤ) (r : ℤ) : Finset ℤ :=
  (Finset.range s.toNat).image (orbitRep m s r)

/-- The common length of the `+m` orbits on the `s` rails: `s / gcd (m, s)`. -/
def orbitLen (m s : ℤ) : ℕ := s.toNat / Int.gcd s m

/-- Auxiliary: `s.toNat` is positive for `s ≥ 1`. -/
theorem toNat_pos_of_one_le {s : ℤ} (hs : 1 ≤ s) : 0 < s.toNat := by
  have h : (0 : ℤ) < (s.toNat : ℤ) := by
    rw [Int.toNat_of_nonneg (by omega)]
    omega
  exact_mod_cast h

/-- Auxiliary: `↑s.toNat = s` for `s ≥ 1`. -/
theorem toNat_cast_of_one_le {s : ℤ} (hs : 1 ≤ s) : (s.toNat : ℤ) = s :=
  Int.toNat_of_nonneg (by omega)

/-- `k = 0` returns `r` itself (for `r ∈ [1, s]`). -/
theorem orbitRep_zero (_hs : 1 ≤ s) {r : ℤ} (hr : r ∈ Finset.Icc 1 s) :
    orbitRep m s r 0 = r := by
  rw [Finset.mem_Icc] at hr
  unfold orbitRep
  rw [Nat.cast_zero, zero_mul, add_zero,
    Int.emod_eq_of_lt (by omega) (by omega)]
  omega

/-- Membership in the orbit: an iterate of `r`. -/
theorem mem_orbit {m s r ρ : ℤ} :
    ρ ∈ orbit m s r ↔ ∃ k : ℕ, k < s.toNat ∧ orbitRep m s r k = ρ := by
  rw [orbit, Finset.mem_image]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, Finset.mem_range.mp hk, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, Finset.mem_range.mpr hk, rfl⟩

/-- Every orbit lies inside `Icc 1 s`. -/
theorem orbit_subset_Icc (hs : 1 ≤ s) (m r : ℤ) :
    orbit m s r ⊆ Finset.Icc 1 s := by
  intro ρ hρ
  rw [mem_orbit] at hρ
  obtain ⟨k, -, rfl⟩ := hρ
  rw [Finset.mem_Icc]
  have h0 := Int.emod_nonneg (r - 1 + (k : ℤ) * m) (show s ≠ 0 by omega)
  have h1 := Int.emod_lt_of_pos (r - 1 + (k : ℤ) * m) (show 0 < s by omega)
  unfold orbitRep
  constructor <;> omega

/-- Every rail lies in its own orbit (take `k = 0`). -/
theorem orbit_self_mem (hs : 1 ≤ s) {r : ℤ} (hr : r ∈ Finset.Icc 1 s) :
    r ∈ orbit m s r := by
  rw [mem_orbit]
  exact ⟨0, toNat_pos_of_one_le hs, orbitRep_zero hs hr⟩

/-- `orbitRep k − 1` is congruent to `r - 1 + k·m` modulo `s`. -/
theorem orbitRep_sub_one_modEq (m s r : ℤ) (k : ℕ) :
    orbitRep m s r k - 1 ≡ r - 1 + (k : ℤ) * m [ZMOD s] := by
  show (r - 1 + (k : ℤ) * m) % s + 1 - 1 ≡ r - 1 + (k : ℤ) * m [ZMOD s]
  rw [add_sub_cancel_right]
  exact Int.mod_modEq _ _

/-- `orbitRep` is `s.toNat`-periodic in `k`. -/
theorem orbitRep_mod_toNat (hs : 1 ≤ s) (k : ℕ) :
    orbitRep m s r k = orbitRep m s r (k % s.toNat) := by
  have hst : (s.toNat : ℤ) = s := toNat_cast_of_one_le hs
  have hcast : (k : ℤ) =
      ((k % s.toNat : ℕ) : ℤ) + s * ((k / s.toNat : ℕ) : ℤ) := by
    have h := Nat.mod_add_div k s.toNat
    have h2 : (k : ℤ) =
        ((k % s.toNat + s.toNat * (k / s.toNat) : ℕ) : ℤ) := by
      rw [h]
    rw [h2, Nat.cast_add, Nat.cast_mul, hst]
  have hmod : r - 1 + (k : ℤ) * m ≡
      r - 1 + ((k % s.toNat : ℕ) : ℤ) * m [ZMOD s] := by
    rw [Int.modEq_iff_dvd]
    refine ⟨-(((k / s.toNat : ℕ) : ℤ) * m), ?_⟩
    rw [show (k : ℤ) * m =
        (((k % s.toNat : ℕ) : ℤ) + s * ((k / s.toNat : ℕ) : ℤ)) * m from
        congrArg (· * m) hcast]
    ring
  have e := hmod.eq
  unfold orbitRep
  rw [e]

/-- Elements of an orbit are characterised by the congruence
`ρ - 1 ≡ r - 1 + k·m [ZMOD s]` for some `k : ℕ`. -/
theorem mem_orbit_of_modEq (hs : 1 ≤ s) {m r ρ : ℤ}
    (hρ : ρ ∈ Finset.Icc 1 s) {k : ℕ}
    (h : ρ - 1 ≡ r - 1 + (k : ℤ) * m [ZMOD s]) :
    ρ ∈ orbit m s r := by
  rw [Finset.mem_Icc] at hρ
  -- `orbitRep r k = ρ` since `ρ - 1 ∈ [0, s)` agrees modulo `s`
  have heq : orbitRep m s r k = ρ := by
    have e := h.eq
    have e2 : (ρ - 1) % s = ρ - 1 := Int.emod_eq_of_lt (by omega) (by omega)
    rw [e2] at e
    unfold orbitRep
    omega
  rw [← heq, mem_orbit]
  exact ⟨k % s.toNat, Nat.mod_lt _ (toNat_pos_of_one_le hs),
    (orbitRep_mod_toNat hs k).symm⟩

/-- The orbit length is positive. -/
theorem orbitLen_pos (hm : 1 ≤ m) (hs : 1 ≤ s) : 0 < orbitLen m s := by
  have hst : 0 < s.toNat := toNat_pos_of_one_le hs
  have es : s.natAbs = s.toNat := by
    conv_lhs => rw [← toNat_cast_of_one_le hs]
    exact Int.natAbs_natCast _
  have em : m.natAbs = m.toNat := by
    conv_lhs => rw [← Int.toNat_of_nonneg (show (0 : ℤ) ≤ m by omega)]
    exact Int.natAbs_natCast _
  have hg : Int.gcd s m = Nat.gcd s.toNat m.toNat := by
    rw [Int.gcd_def, es, em]
  rw [orbitLen, hg]
  apply Nat.div_pos (Nat.le_of_dvd hst (Nat.gcd_dvd_left _ _))
  exact Nat.gcd_pos_of_pos_left _ hst

/-- `gcd s m` times the orbit length recovers `s`. -/
theorem gcd_mul_orbitLen (hs : 1 ≤ s) :
    (Int.gcd s m : ℤ) * (orbitLen m s : ℤ) = s := by
  have hg : (Int.gcd s m : ℤ) ∣ s := Int.gcd_dvd_left s m
  have h1 : s / (Int.gcd s m : ℤ) * (Int.gcd s m : ℤ) = s :=
    Int.ediv_mul_cancel hg
  have h2 : (s / (Int.gcd s m : ℤ)) = (orbitLen m s : ℤ) := by
    have e : ((orbitLen m s : ℕ) : ℤ) =
        (s.toNat : ℤ) / (Int.gcd s m : ℤ) := by
      unfold orbitLen
      rw [Int.natCast_ediv]
    rw [e, toNat_cast_of_one_le hs]
  rw [h2] at h1
  calc (Int.gcd s m : ℤ) * (orbitLen m s : ℤ)
      = (orbitLen m s : ℤ) * (Int.gcd s m : ℤ) := mul_comm _ _
    _ = s := h1

/-- `s` divides `orbitLen · m`: the `+m` map has period `orbitLen`. -/
theorem orbitLen_mul_dvd (_hm : 1 ≤ m) (hs : 1 ≤ s) :
    s ∣ (orbitLen m s : ℤ) * m := by
  have hgm : (Int.gcd s m : ℤ) ∣ m := Int.gcd_dvd_right s m
  have hsc := gcd_mul_orbitLen (m := m) hs
  obtain ⟨t, ht⟩ := hgm
  refine ⟨t, ?_⟩
  calc (orbitLen m s : ℤ) * m
      = (orbitLen m s : ℤ) * ((Int.gcd s m : ℤ) * t) :=
        congrArg (fun a => (orbitLen m s : ℤ) * a) ht
    _ = ((Int.gcd s m : ℤ) * (orbitLen m s : ℤ)) * t := by ring
    _ = s * t := by rw [hsc]

/-- `orbitRep` in `k` is periodic with period `orbitLen`: every index
reduces modulo `orbitLen`. -/
theorem orbitRep_mod_orbitLen (hm : 1 ≤ m) (hs : 1 ≤ s) (k : ℕ) :
    orbitRep m s r k = orbitRep m s r (k % orbitLen m s) := by
  obtain ⟨t, ht⟩ := orbitLen_mul_dvd (m := m) hm hs
  have hcast : (k : ℤ) = ((k % orbitLen m s : ℕ) : ℤ) +
      (orbitLen m s : ℤ) * ((k / orbitLen m s : ℕ) : ℤ) := by
    have h := Nat.mod_add_div k (orbitLen m s)
    have h2 : (k : ℤ) =
        ((k % orbitLen m s + orbitLen m s * (k / orbitLen m s) : ℕ) : ℤ) := by
      rw [h]
    rw [h2, Nat.cast_add, Nat.cast_mul]
  have hmod : r - 1 + (k : ℤ) * m ≡
      r - 1 + ((k % orbitLen m s : ℕ) : ℤ) * m [ZMOD s] := by
    rw [Int.modEq_iff_dvd]
    refine ⟨-(((k / orbitLen m s : ℕ) : ℤ) * t), ?_⟩
    rw [show (k : ℤ) * m =
        (((k % orbitLen m s : ℕ) : ℤ) +
          (orbitLen m s : ℤ) * ((k / orbitLen m s : ℕ) : ℤ)) * m from
        congrArg (· * m) hcast]
    have e : (r - 1 + ((k % orbitLen m s : ℕ) : ℤ) * m) -
        (r - 1 + (((k % orbitLen m s : ℕ) : ℤ) +
          (orbitLen m s : ℤ) * ((k / orbitLen m s : ℕ) : ℤ)) * m) =
        -(((k / orbitLen m s : ℕ) : ℤ) * ((orbitLen m s : ℤ) * m)) := by ring
    rw [e, ht]
    ring
  have e := hmod.eq
  unfold orbitRep
  rw [e]

/-- Iterating by one period returns to the same rail. -/
theorem orbitRep_add_orbitLen (hm : 1 ≤ m) (hs : 1 ≤ s) (k : ℕ) :
    orbitRep m s r (k + orbitLen m s) = orbitRep m s r k := by
  rw [orbitRep_mod_orbitLen hm hs (k + orbitLen m s), Nat.add_mod_right,
    ← orbitRep_mod_orbitLen hm hs k]

/-- The orbit is already exhausted by `orbitLen` iterates. -/
theorem orbit_eq_image_orbitLen (hm : 1 ≤ m) (hs : 1 ≤ s) (r : ℤ) :
    orbit m s r =
      (Finset.range (orbitLen m s)).image (orbitRep m s r) := by
  ext ρ
  rw [mem_orbit, Finset.mem_image]
  constructor
  · rintro ⟨k, -, rfl⟩
    exact ⟨k % orbitLen m s,
      Finset.mem_range.mpr (Nat.mod_lt _ (orbitLen_pos hm hs)),
      (orbitRep_mod_orbitLen hm hs k).symm⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, lt_of_lt_of_le (Finset.mem_range.mp hk)
      (Nat.div_le_self _ _), rfl⟩

/-- The iterates `orbitRep r 0, …, orbitRep r (orbitLen - 1)` are
pairwise distinct: `orbitRep r i = orbitRep r j` with `i, j < orbitLen`
forces `i = j`, since `s ∣ (i - j)·m` and `s / gcd` exceeds `|i - j|`. -/
theorem orbitRep_injective_on (_hm : 1 ≤ m) (hs : 1 ≤ s) (r : ℤ) :
    Set.InjOn (orbitRep m s r)
      (↑(Finset.range (orbitLen m s)) : Set ℕ) := by
  intro i hi j hj hij
  rw [Finset.mem_coe, Finset.mem_range] at hi hj
  -- `orbitRep i = orbitRep j` gives `i·m ≡ j·m [ZMOD s]`
  have hmod : (i : ℤ) * m ≡ (j : ℤ) * m [ZMOD s] := by
    have e : orbitRep m s r i - 1 ≡ orbitRep m s r j - 1 [ZMOD s] := by
      rw [hij]
    have h2 : r - 1 + (i : ℤ) * m ≡ r - 1 + (j : ℤ) * m [ZMOD s] :=
      (orbitRep_sub_one_modEq m s r i).symm.trans
        (e.trans (orbitRep_sub_one_modEq m s r j))
    exact Int.ModEq.add_left_cancel' (r - 1) h2
  -- cancel `m`: `i ≡ j [ZMOD s / gcd s m]`
  have hcancel : (i : ℤ) ≡ (j : ℤ) [ZMOD s / (Int.gcd s m : ℤ)] :=
    Int.ModEq.cancel_right_div_gcd (by omega : 0 < s) hmod
  have hc : (s / (Int.gcd s m : ℤ)) = (orbitLen m s : ℤ) := by
    have e : ((orbitLen m s : ℕ) : ℤ) =
        (s.toNat : ℤ) / (Int.gcd s m : ℤ) := by
      unfold orbitLen
      rw [Int.natCast_ediv]
    rw [e, toNat_cast_of_one_le hs]
  rw [hc] at hcancel
  -- `i ≡ j [ZMOD orbitLen]` with `i, j < orbitLen` gives `i = j`
  have e := hcancel.eq
  have hi' : (i : ℤ) % (orbitLen m s : ℤ) = (i : ℤ) := by
    apply Int.emod_eq_of_lt (by omega)
    exact_mod_cast hi
  have hj' : (j : ℤ) % (orbitLen m s : ℤ) = (j : ℤ) := by
    apply Int.emod_eq_of_lt (by omega)
    exact_mod_cast hj
  rw [hi', hj'] at e
  exact_mod_cast e

/-- Every orbit has exactly `orbitLen` rails. -/
theorem orbit_card (hm : 1 ≤ m) (hs : 1 ≤ s) (r : ℤ) :
    (orbit m s r).card = orbitLen m s := by
  rw [orbit_eq_image_orbitLen hm hs r,
    Finset.card_image_of_injOn (orbitRep_injective_on hm hs r),
    Finset.card_range]

/-- One-step behaviour of `orbitRep` (as a congruence). -/
theorem orbitRep_succ_modEq (m s r : ℤ) (k : ℕ) :
    orbitRep m s r (k + 1) - 1 ≡ orbitRep m s r k - 1 + m [ZMOD s] := by
  have h1 := orbitRep_sub_one_modEq m s r (k + 1)
  have h2 : r - 1 + ((k + 1 : ℕ) : ℤ) * m = r - 1 + (k : ℤ) * m + m := by
    push_cast; ring
  rw [h2] at h1
  exact h1.trans ((orbitRep_sub_one_modEq m s r k).add_right m).symm

/-- The one-step rail update: `orbitRep (k+1)` is `orbitRep k + m`
reduced back into `[1, s]`. -/
theorem orbitRep_succ (hm : 1 ≤ m) (hms : m < s) (k : ℕ) :
    orbitRep m s r (k + 1) =
      if orbitRep m s r k + m ≤ s then orbitRep m s r k + m
        else orbitRep m s r k + m - s := by
  have hs : 1 ≤ s := by omega
  have hmem : orbitRep m s r k ∈ Finset.Icc 1 s :=
    orbit_subset_Icc hs m r
      (mem_orbit.mpr ⟨k % s.toNat, Nat.mod_lt _ (toNat_pos_of_one_le hs),
        (orbitRep_mod_toNat hs k).symm⟩)
  rw [Finset.mem_Icc] at hmem
  have hmem1 : orbitRep m s r (k + 1) ∈ Finset.Icc 1 s :=
    orbit_subset_Icc hs m r
      (mem_orbit.mpr ⟨(k + 1) % s.toNat,
        Nat.mod_lt _ (toNat_pos_of_one_le hs),
        (orbitRep_mod_toNat hs (k + 1)).symm⟩)
  rw [Finset.mem_Icc] at hmem1
  -- `(orbitRep (k+1) - 1) = (orbitRep k - 1 + m) % s`
  have hmod : (orbitRep m s r (k + 1) - 1) % s =
      (orbitRep m s r k - 1 + m) % s := (orbitRep_succ_modEq m s r k).eq
  rw [Int.emod_eq_of_lt (by omega : 0 ≤ orbitRep m s r (k + 1) - 1)
    (by omega : orbitRep m s r (k + 1) - 1 < s)] at hmod
  by_cases hcase : orbitRep m s r k + m ≤ s
  · rw [ite_eq_left hcase]
    rw [Int.emod_eq_of_lt (by omega : 0 ≤ orbitRep m s r k - 1 + m)
      (by omega : orbitRep m s r k - 1 + m < s)] at hmod
    omega
  · rw [ite_eq_right hcase]
    have e : (orbitRep m s r k - 1 + m) % s =
        orbitRep m s r k - 1 + m - s := by
      have e1 : (orbitRep m s r k - 1 + m - s) % s =
          orbitRep m s r k - 1 + m - s :=
        Int.emod_eq_of_lt (by omega) (by omega)
      have e2 : (orbitRep m s r k - 1 + m - s) % s =
          (orbitRep m s r k - 1 + m) % s := by
        rw [show orbitRep m s r k - 1 + m - s =
            orbitRep m s r k - 1 + m + (-1) * s from by ring]
        exact Int.add_mul_emod_self_right _ _ _
      exact e2.symm.trans e1
    rw [e] at hmod
    omega

/-- The orbit is symmetric: `ρ ∈ orbit r` implies `r ∈ orbit ρ`. -/
theorem mem_orbit_symm (_hm : 1 ≤ m) (hs : 1 ≤ s) {r ρ : ℤ}
    (hr : r ∈ Finset.Icc 1 s) (hρ : ρ ∈ orbit m s r) :
    r ∈ orbit m s ρ := by
  obtain ⟨k, -, hkeq⟩ := mem_orbit.mp hρ
  -- `ρ - 1 ≡ r - 1 + k·m`, so `r - 1 ≡ ρ - 1 - k·m ≡ ρ - 1 + j·m`
  -- for `j = s.toNat * (k + 1) - k`.
  have hmodρ : ρ - 1 ≡ r - 1 + (k : ℤ) * m [ZMOD s] := by
    have h1 := orbitRep_sub_one_modEq m s r k
    rw [hkeq] at h1
    exact h1
  refine mem_orbit_of_modEq hs hr (k := s.toNat * (k + 1) - k) ?_
  have hst : (s.toNat : ℤ) = s := toNat_cast_of_one_le hs
  have hkj : k ≤ s.toNat * (k + 1) := by
    have h1 : 1 ≤ s.toNat := toNat_pos_of_one_le hs
    calc k ≤ k + 1 := Nat.le_succ k
      _ = 1 * (k + 1) := (one_mul _).symm
      _ ≤ s.toNat * (k + 1) := Nat.mul_le_mul_right _ h1
  have hj : ((s.toNat * (k + 1) - k : ℕ) : ℤ) * m ≡ -((k : ℤ) * m)
      [ZMOD s] := by
    rw [Int.modEq_iff_dvd]
    refine ⟨-(((k + 1 : ℕ) : ℤ) * m), ?_⟩
    rw [Nat.cast_sub hkj]
    push_cast
    rw [hst]
    ring
  have hmodr : r - 1 ≡ ρ - 1 - (k : ℤ) * m [ZMOD s] := by
    have h2 := hmodρ.symm.sub_right ((k : ℤ) * m)
    rwa [add_sub_cancel_right] at h2
  have h3 : ρ - 1 - (k : ℤ) * m ≡
      ρ - 1 + ((s.toNat * (k + 1) - k : ℕ) : ℤ) * m [ZMOD s] := by
    rw [sub_eq_add_neg]
    exact (Int.ModEq.refl _).add hj.symm
  exact hmodr.trans h3

/-- Membership is transitive: the orbit of an orbit element is contained
in the orbit. -/
theorem orbit_subset_of_mem (_hm : 1 ≤ m) (hs : 1 ≤ s) {r ρ : ℤ}
    (hρ : ρ ∈ orbit m s r) : orbit m s ρ ⊆ orbit m s r := by
  obtain ⟨k, -, hkeq⟩ := mem_orbit.mp hρ
  have hmodρ : ρ - 1 ≡ r - 1 + (k : ℤ) * m [ZMOD s] := by
    have h1 := orbitRep_sub_one_modEq m s r k
    rw [hkeq] at h1
    exact h1
  intro σ hσ
  obtain ⟨j, -, hjeq⟩ := mem_orbit.mp hσ
  have hσIcc := orbit_subset_Icc hs m ρ hσ
  have hmodσ : σ - 1 ≡ ρ - 1 + (j : ℤ) * m [ZMOD s] := by
    have h1 := orbitRep_sub_one_modEq m s ρ j
    rw [hjeq] at h1
    exact h1
  refine mem_orbit_of_modEq hs hσIcc (k := k + j) ?_
  have e : r - 1 + ((k + j : ℕ) : ℤ) * m =
      r - 1 + (k : ℤ) * m + (j : ℤ) * m := by
    push_cast; ring
  rw [e]
  exact hmodσ.trans (hmodρ.add_right ((j : ℤ) * m))

/-- **Orbit equality**: two rails in the same orbit generate the same
orbit. -/
theorem orbit_eq_of_mem (hm : 1 ≤ m) (hs : 1 ≤ s) {r ρ : ℤ}
    (hr : r ∈ Finset.Icc 1 s) (hρ : ρ ∈ orbit m s r) :
    orbit m s ρ = orbit m s r := by
  apply le_antisymm
  · exact orbit_subset_of_mem hm hs hρ
  · exact orbit_subset_of_mem hm hs (mem_orbit_symm hm hs hr hρ)

/-- **Orbit partition**: two orbits are either equal or disjoint. -/
theorem orbit_eq_or_disjoint (hm : 1 ≤ m) (hs : 1 ≤ s) {r₁ r₂ : ℤ}
    (hr₁ : r₁ ∈ Finset.Icc 1 s) (hr₂ : r₂ ∈ Finset.Icc 1 s) :
    orbit m s r₁ = orbit m s r₂ ∨
      Disjoint (orbit m s r₁) (orbit m s r₂) := by
  by_cases h : (orbit m s r₁ ∩ orbit m s r₂).Nonempty
  · obtain ⟨ρ, hρ⟩ := h
    rw [Finset.mem_inter] at hρ
    refine Or.inl ?_
    rw [← orbit_eq_of_mem hm hs hr₁ hρ.1,
      ← orbit_eq_of_mem hm hs hr₂ hρ.2]
  · exact Or.inr (Finset.disjoint_iff_inter_eq_empty.mpr
      (Finset.not_nonempty_iff_eq_empty.mp h))

/-- The distinct orbits form a pairwise-disjoint family. -/
theorem orbit_image_pairwiseDisjoint (hm : 1 ≤ m) (hs : 1 ≤ s) :
    (↑((Finset.Icc 1 s).image (orbit m s)) : Set (Finset ℤ)).PairwiseDisjoint
      id := by
  intro O₁ hO₁ O₂ hO₂ hne
  rw [Finset.mem_coe, Finset.mem_image] at hO₁ hO₂
  obtain ⟨r₁, hr₁, rfl⟩ := hO₁
  obtain ⟨r₂, hr₂, rfl⟩ := hO₂
  rcases orbit_eq_or_disjoint hm hs hr₁ hr₂ with h | h
  · exact absurd h (by simpa using hne)
  · exact h

/-- **Orbit cover.**  Every `x ∈ Icc (s+1) n` lies in some rail `cls n s ρ`
with `ρ` in the orbit of a rail `r ∈ Icc 1 s` — i.e. in the union over the
distinct orbits of their rail unions. -/
theorem Icc_subset_biUnion_orbitCls {n : ℕ} {m s : ℤ} (hm : 1 ≤ m)
    (hms : m < s) :
    Finset.Icc (s + 1) (n : ℤ) ⊆
      ((Finset.Icc 1 s).image (orbit m s)).biUnion
        (fun O => O.biUnion (cls n s)) := by
  have hs : 1 ≤ s := by omega
  intro x hx
  obtain ⟨r, hr, hxr⟩ := Finset.mem_biUnion.mp (Icc_subset_biUnion_cls hs hx)
  rw [Finset.mem_biUnion]
  refine ⟨orbit m s r, ?_, ?_⟩
  · exact Finset.mem_image.mpr ⟨r, hr, rfl⟩
  · rw [Finset.mem_biUnion]
    exact ⟨r, orbit_self_mem hs hr, hxr⟩

/-- **Conditional orbit-product bound.**  If each orbit union
`O.biUnion (cls n s)` admits the estimate `B O`, the double-shift-free
subsets of `Icc (s+1) n` are at most `∏ O, B O` over the distinct orbits. -/
theorem card_powerset_filter_shiftFree2_Icc_le_orbitProd {n : ℕ} {m s : ℤ}
    (hm : 1 ≤ m) (hms : m < s) {B : Finset ℤ → ℕ}
    (horbit : ∀ O ∈ (Finset.Icc 1 s).image (orbit m s),
      ((O.biUnion (cls n s)).powerset.filter (shiftFree2 m s)).card ≤ B O) :
    ((Finset.Icc (s + 1) (n : ℤ)).powerset.filter (shiftFree2 m s)).card ≤
      ∏ O ∈ (Finset.Icc 1 s).image (orbit m s), B O := by
  have hT := Icc_subset_biUnion_orbitCls (n := n) hm hms
  have hA := card_powerset_filter_shiftFree2_le_prod (m := m) (s := s)
    ((Finset.Icc 1 s).image (orbit m s)) (fun O => O.biUnion (cls n s)) _ hT
  exact hA.trans (Finset.prod_le_prod fun O hO => horbit O hO)

/-- **Raw orbit-product bound.**  Without a per-orbit estimate, the product
of the exact orbit counts. -/
theorem card_powerset_filter_shiftFree2_Icc_le_orbitProd' {n : ℕ} {m s : ℤ}
    (hm : 1 ≤ m) (hms : m < s) :
    ((Finset.Icc (s + 1) (n : ℤ)).powerset.filter (shiftFree2 m s)).card ≤
      ∏ O ∈ (Finset.Icc 1 s).image (orbit m s),
        ((O.biUnion (cls n s)).powerset.filter (shiftFree2 m s)).card :=
  card_powerset_filter_shiftFree2_le_prod (m := m) (s := s)
    ((Finset.Icc 1 s).image (orbit m s)) (fun O => O.biUnion (cls n s)) _
    (Icc_subset_biUnion_orbitCls hm hms)

/-! ### Per-orbit strip bound (stretch) -/

/-- Membership in a residue class, as an indexed progression.
(`PairRails.mem_cls_iff`, restated here to keep the import profile.) -/
theorem cls_mem_iff {n : ℕ} {m r : ℤ} {x : ℤ} :
    x ∈ cls n m r ↔
      ∃ k : ℕ, k < (((n : ℤ) - r) / m).toNat ∧ x = r + m + m * (k : ℤ) := by
  rw [cls_eq_prog, prog_eq_image, Finset.mem_image]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, Finset.mem_range.mp hk, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, Finset.mem_range.mpr hk, rfl⟩

/-- Position of rail `ρ` within the orbit of `r`: the least index
`i < orbitLen m s` with `orbitRep m s r i = ρ`, or `0` if `ρ` is not in
the orbit. -/
def orbitPos (m s r ρ : ℤ) : ℕ :=
  if h : ((Finset.range (orbitLen m s)).filter
      fun i => orbitRep m s r i = ρ).Nonempty then
    ((Finset.range (orbitLen m s)).filter
      fun i => orbitRep m s r i = ρ).min' h
  else 0

/-- The defining property of `orbitPos`: for `ρ` in the orbit, it is an
index `< orbitLen` whose iterate is `ρ`. -/
theorem orbitPos_spec (hm : 1 ≤ m) (hs : 1 ≤ s) {r ρ : ℤ}
    (hρ : ρ ∈ orbit m s r) :
    orbitPos m s r ρ < orbitLen m s ∧
      orbitRep m s r (orbitPos m s r ρ) = ρ := by
  have hW : ((Finset.range (orbitLen m s)).filter
      fun i => orbitRep m s r i = ρ).Nonempty := by
    rw [orbit_eq_image_orbitLen hm hs r, Finset.mem_image] at hρ
    obtain ⟨i, hi, rfl⟩ := hρ
    exact ⟨i, Finset.mem_filter.mpr ⟨hi, rfl⟩⟩
  unfold orbitPos
  rw [dite_eq_left hW]
  have hmem := Finset.min'_mem _ hW
  rw [Finset.mem_filter] at hmem
  exact ⟨Finset.mem_range.mp hmem.1, hmem.2⟩

/-- `orbitPos` inverts `orbitRep` below `orbitLen`. -/
theorem orbitPos_orbitRep (hm : 1 ≤ m) (hs : 1 ≤ s) (r : ℤ) {i : ℕ}
    (hi : i < orbitLen m s) : orbitPos m s r (orbitRep m s r i) = i := by
  have hW : ((Finset.range (orbitLen m s)).filter
      fun j => orbitRep m s r j = orbitRep m s r i).Nonempty :=
    ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi, rfl⟩⟩
  unfold orbitPos
  rw [dite_eq_left hW]
  have hmem := Finset.min'_mem _ hW
  rw [Finset.mem_filter] at hmem
  exact orbitRep_injective_on hm hs r
    (Finset.mem_coe.mpr hmem.1)
    (Finset.mem_coe.mpr (Finset.mem_range.mpr hi)) hmem.2

/-- Every `x ∈ Icc (s+1) n` lies in its own residue rail
`cls n s ((x-1) % s + 1)`.  This is the membership half of
`Icc_subset_biUnion_cls`. -/
theorem mem_cls_residue {n : ℕ} {s x : ℤ} (hs : 1 ≤ s)
    (hx : x ∈ Finset.Icc (s + 1) (n : ℤ)) :
    x ∈ cls n s ((x - 1) % s + 1) := by
  rw [Finset.mem_Icc] at hx
  obtain ⟨hx1, hx2⟩ := hx
  have hm0 : s ≠ 0 := by omega
  set e := (x - 1) % s with he_def
  set j := (x - 1) / s with hj_def
  have he0 : 0 ≤ e := Int.emod_nonneg _ hm0
  have helm : e < s := Int.emod_lt_of_pos _ (by omega)
  have hdecomp : s * j + e = x - 1 := by
    have h := Int.mul_ediv_add_emod (x - 1) s
    rwa [← hj_def, ← he_def] at h
  have hj1 : 1 ≤ j := by
    rw [hj_def, Int.le_ediv_iff_mul_le (by omega : 0 < s)]
    omega
  have hjle : j ≤ ((n : ℤ) - (e + 1)) / s := by
    rw [Int.le_ediv_iff_mul_le (by omega : 0 < s), mul_comm j s]
    omega
  rw [cls_eq_prog, prog_eq_image, Finset.mem_image]
  refine ⟨(j - 1).toNat, ?_, ?_⟩
  · rw [Finset.mem_range, Int.lt_toNat]
    have hkj : ((j - 1).toNat : ℤ) = j - 1 := Int.toNat_of_nonneg (by omega)
    omega
  · have hkj : ((j - 1).toNat : ℤ) = j - 1 := Int.toNat_of_nonneg (by omega)
    rw [hkj]
    have hsub : s * (j - 1) = s * j - s := by ring
    rw [hsub]
    omega

/-- The residue rail is the *unique* `Icc 1 s` class containing `x`. -/
theorem cls_residue_eq {n : ℕ} {s ρ x : ℤ} (hs : 1 ≤ s)
    (hρ : ρ ∈ Finset.Icc 1 s) (hx : x ∈ cls n s ρ) :
    ρ = (x - 1) % s + 1 := by
  have hxIcc := cls_subset_Icc hs (Finset.mem_Icc.mp hρ).1 hx
  have hxr := mem_cls_residue hs hxIcc
  have hr₀mem : (x - 1) % s + 1 ∈ Finset.Icc 1 s := by
    rw [Finset.mem_Icc]
    have h0 := Int.emod_nonneg (x - 1) (show s ≠ 0 by omega)
    have h1 := Int.emod_lt_of_pos (x - 1) (show 0 < s by omega)
    constructor <;> omega
  by_contra hne
  have hd := cls_pairwise (n := n) (m := s) hs
    (Finset.mem_coe.mpr hρ) (Finset.mem_coe.mpr hr₀mem) hne
  exact Finset.disjoint_left.mp hd hx hxr

/-- The index map for one orbit: `x ↦ (position of its rail in the orbit,
level along the rail)`.  Elements of the orbit union land in
`range (orbitLen) × range L`. -/
def orbitIdx (_n : ℕ) (m s r : ℤ) (x : ℤ) : ℕ × ℕ :=
  (orbitPos m s r ((x - 1) % s + 1),
    ((x - ((x - 1) % s + 1) - s) / s).toNat)

/-- The index map on the `ρ`-rail: `ρ + s + s·k ↦ (orbitPos ρ, k)`. -/
theorem orbitIdx_cls {n : ℕ} {m s r ρ : ℤ} (_hm : 1 ≤ m) (hs : 1 ≤ s)
    (hρ : ρ ∈ orbit m s r) {k : ℕ}
    (_hk : ρ + s + s * (k : ℤ) ∈ cls n s ρ) :
    orbitIdx n m s r (ρ + s + s * (k : ℤ)) = (orbitPos m s r ρ, k) := by
  have hρIcc := orbit_subset_Icc hs m r hρ
  rw [Finset.mem_Icc] at hρIcc
  have hrail : (ρ + s + s * (k : ℤ) - 1) % s + 1 = ρ := by
    have e : ρ + s + s * (k : ℤ) - 1 = ρ - 1 + s * ((k : ℤ) + 1) := by ring
    rw [e, Int.add_mul_emod_self_left,
      Int.emod_eq_of_lt (by omega) (by omega)]
    omega
  unfold orbitIdx
  rw [hrail]
  have elvl : (ρ + s + s * (k : ℤ) - ρ - s) / s = (k : ℤ) := by
    rw [show ρ + s + s * (k : ℤ) - ρ - s = (k : ℤ) * s from by ring]
    exact Int.mul_ediv_cancel _ (by omega)
  rw [elvl, Int.toNat_natCast]

/-- The index map is injective on the orbit rail union. -/
theorem orbitIdx_injOn {n : ℕ} {m s r : ℤ} (hm : 1 ≤ m) (hms : m < s) :
    Set.InjOn (orbitIdx n m s r)
      (↑((orbit m s r).biUnion (cls n s)) : Set ℤ) := by
  have hs : 1 ≤ s := by omega
  intro x hx y hy hxy
  rw [Finset.mem_coe, Finset.mem_biUnion] at hx hy
  obtain ⟨ρx, hρx, hxρ⟩ := hx
  obtain ⟨ρy, hρy, hyρ⟩ := hy
  have hρxIcc := orbit_subset_Icc hs m r hρx
  have hρyIcc := orbit_subset_Icc hs m r hρy
  have hrx : ρx = (x - 1) % s + 1 := cls_residue_eq hs hρxIcc hxρ
  have hry : ρy = (y - 1) % s + 1 := cls_residue_eq hs hρyIcc hyρ
  obtain ⟨kx, -, hxe⟩ := cls_mem_iff.mp hxρ
  obtain ⟨ky, -, hye⟩ := cls_mem_iff.mp hyρ
  -- equal first components: positions of `ρx` and `ρy` agree
  have hpos : orbitPos m s r ρx = orbitPos m s r ρy := by
    have e := congrArg Prod.fst hxy
    unfold orbitIdx at e
    rw [← hrx, ← hry] at e
    exact e
  have hρ : ρx = ρy := by
    have e1 := (orbitPos_spec hm hs hρx).2
    have e2 := (orbitPos_spec hm hs hρy).2
    rw [← e1, ← e2, hpos]
  -- equal second components: levels agree
  have hlv : ((x - ρx - s) / s).toNat = ((y - ρx - s) / s).toNat := by
    have e := congrArg Prod.snd hxy
    unfold orbitIdx at e
    rw [← hrx, ← hry, ← hρ] at e
    exact e
  have ekx : (x - ρx - s) / s = (kx : ℤ) := by
    rw [hxe, show ρx + s + s * (kx : ℤ) - ρx - s = (kx : ℤ) * s from by ring]
    exact Int.mul_ediv_cancel _ (by omega)
  have eky : (y - ρx - s) / s = (ky : ℤ) := by
    rw [← hρ] at hye
    rw [hye, show ρx + s + s * (ky : ℤ) - ρx - s = (ky : ℤ) * s from by ring]
    exact Int.mul_ediv_cancel _ (by omega)
  have hkk : kx = ky := by
    rw [ekx, eky, Int.toNat_natCast, Int.toNat_natCast] at hlv
    exact hlv
  rw [hxe, hye, hρ, hkk]

/-- Vertex set of the `c × L` orbit strip: `range c × range L`. -/
def orbitStripVert (c L : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range c).product (Finset.range L)

theorem mem_orbitStripVert {c L i k : ℕ} :
    (i, k) ∈ orbitStripVert c L ↔ i < c ∧ k < L := by
  simp [orbitStripVert]

/-- Independence predicate for the orbit strip: no vertical successor
`(i, k+1)` (the `s`-shift within a rail) and no horizontal neighbour
`(i+1, k + δ i)` (the `m`-shift, level-twisted by `δ i`).  The wrap edge
from rail `c-1` to rail `0` is dropped, enlarging the family. -/
def orbitStripFree (δ : ℕ → ℕ) (c : ℕ) (t : Finset (ℕ × ℕ)) : Prop :=
  (∀ p ∈ t, (p.1, p.2 + 1) ∉ t) ∧
    ∀ p ∈ t, p.1 + 1 < c → (p.1 + 1, p.2 + δ p.1) ∉ t

instance decidableOrbitStripFree (δ : ℕ → ℕ) (c : ℕ) (t : Finset (ℕ × ℕ)) :
    Decidable (orbitStripFree δ c t) := by
  unfold orbitStripFree; infer_instance

/-- The family of independent sets of the orbit strip. -/
def orbitStrips (δ : ℕ → ℕ) (c L : ℕ) : Finset (Finset (ℕ × ℕ)) :=
  (orbitStripVert c L).powerset.filter (orbitStripFree δ c)

theorem mem_orbitStrips {δ : ℕ → ℕ} {c L : ℕ} {t : Finset (ℕ × ℕ)} :
    t ∈ orbitStrips δ c L ↔
      t ⊆ orbitStripVert c L ∧ orbitStripFree δ c t := by
  simp [orbitStrips]

/-- The level twist of the `m`-shift leaving orbit rail `i`: `0` when
`orbitRep i + m ≤ s` (no wrap) and `1` when it wraps down by `s`. -/
def orbitTwist (m s r : ℤ) (i : ℕ) : ℕ :=
  if orbitRep m s r i + m ≤ s then 0 else 1

/-- The successor rail in terms of the twist:
`orbitRep (i+1) = orbitRep i + m - s·twist`. -/
theorem orbitRep_succ_twist (hm : 1 ≤ m) (hms : m < s) (i : ℕ) :
    orbitRep m s r (i + 1) =
      orbitRep m s r i + m - s * (orbitTwist m s r i : ℤ) := by
  rw [orbitRep_succ hm hms i]
  unfold orbitTwist
  by_cases h : orbitRep m s r i + m ≤ s
  · rw [ite_eq_left h, ite_eq_left h, Nat.cast_zero, mul_zero, sub_zero]
  · rw [ite_eq_right h, ite_eq_right h, Nat.cast_one, mul_one]

/-- **Per-orbit strip bound.**  `shiftFree2 m s` subsets of the orbit's
rail union inject (via `orbitIdx`) into the independent sets of the
`orbitLen × L` strip with `L = ((n - 1)/s).toNat`, the maximum rail
length.  The wrap edge is ignored (it only enlarges the family). -/
theorem card_powerset_filter_shiftFree2_orbitCls_le {n : ℕ} {m s r : ℤ}
    (hm : 1 ≤ m) (hms : m < s) :
    (((orbit m s r).biUnion (cls n s)).powerset.filter
        (shiftFree2 m s)).card ≤
      (orbitStrips (orbitTwist m s r) (orbitLen m s)
        (((n : ℤ) - 1) / s).toNat).card := by
  have hs : 1 ≤ s := by omega
  refine Finset.card_le_card_of_injOn (Finset.image (orbitIdx n m s r)) ?_ ?_
  · intro T hT
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset] at hT
    obtain ⟨hTU, hsm, hss⟩ := hT
    rw [Finset.mem_coe, mem_orbitStrips]
    refine ⟨?_, ⟨?_, ?_⟩⟩
    · -- the image lies in the `orbitLen × L` vertex set
      rintro ⟨i, k⟩ hp
      rw [Finset.mem_image] at hp
      obtain ⟨x, hxT, hxeq⟩ := hp
      rw [mem_orbitStripVert]
      have hxU := hTU hxT
      rw [Finset.mem_biUnion] at hxU
      obtain ⟨ρ, hρ, hxρ⟩ := hxU
      have hρIcc := orbit_subset_Icc hs m r hρ
      have hrx : ρ = (x - 1) % s + 1 := cls_residue_eq hs hρIcc hxρ
      obtain ⟨kx, hkx, hxe⟩ := cls_mem_iff.mp hxρ
      have hfst : i = orbitPos m s r ρ := by
        have e := congrArg Prod.fst hxeq
        unfold orbitIdx at e
        rw [← hrx] at e
        exact e.symm
      have hsnd : k = ((x - ρ - s) / s).toNat := by
        have e := congrArg Prod.snd hxeq
        unfold orbitIdx at e
        rw [← hrx] at e
        exact e.symm
      constructor
      · rw [hfst]
        exact (orbitPos_spec hm hs hρ).1
      · rw [hsnd]
        have elvl : (x - ρ - s) / s = (kx : ℤ) := by
          rw [hxe, show ρ + s + s * (kx : ℤ) - ρ - s = (kx : ℤ) * s from by ring]
          exact Int.mul_ediv_cancel _ (by omega)
        rw [elvl, Int.toNat_natCast]
        have hle : ((n : ℤ) - ρ) / s ≤ ((n : ℤ) - 1) / s := by
          apply Int.ediv_le_ediv (by omega : 0 < s)
          rw [Finset.mem_Icc] at hρIcc
          omega
        exact lt_of_lt_of_le hkx (Int.toNat_le_toNat hle)
    · -- vertical: `(i, k+1)` comes from `x + s`, excluded by `shiftFree s`
      rintro p hp hC
      rw [Finset.mem_image] at hp hC
      obtain ⟨x, hxT, hpx⟩ := hp
      obtain ⟨y, hyT, hpy⟩ := hC
      have hxU := hTU hxT
      have hyU := hTU hyT
      rw [Finset.mem_biUnion] at hxU hyU
      obtain ⟨ρx, hρx, hxρ⟩ := hxU
      obtain ⟨ρy, hρy, hyρ⟩ := hyU
      have hρxIcc := orbit_subset_Icc hs m r hρx
      have hρyIcc := orbit_subset_Icc hs m r hρy
      have hrx : ρx = (x - 1) % s + 1 := cls_residue_eq hs hρxIcc hxρ
      have hry : ρy = (y - 1) % s + 1 := cls_residue_eq hs hρyIcc hyρ
      obtain ⟨kx, -, hxe⟩ := cls_mem_iff.mp hxρ
      obtain ⟨ky, -, hye⟩ := cls_mem_iff.mp hyρ
      have hfstx : p.1 = orbitPos m s r ρx := by
        have e := congrArg Prod.fst hpx
        unfold orbitIdx at e
        rw [← hrx] at e
        exact e.symm
      have hfsty : orbitPos m s r ρy = p.1 := by
        have e := congrArg Prod.fst hpy
        unfold orbitIdx at e
        rw [← hry] at e
        exact e
      have hsndx : p.2 = ((x - ρx - s) / s).toNat := by
        have e := congrArg Prod.snd hpx
        unfold orbitIdx at e
        rw [← hrx] at e
        exact e.symm
      have hsndy : ((y - ρy - s) / s).toNat = p.2 + 1 := by
        have e := congrArg Prod.snd hpy
        unfold orbitIdx at e
        rw [← hry] at e
        exact e
      have hpos : orbitPos m s r ρy = orbitPos m s r ρx :=
        hfsty.trans hfstx
      have hρ : ρy = ρx := by
        have e1 := (orbitPos_spec hm hs hρy).2
        have e2 := (orbitPos_spec hm hs hρx).2
        rw [← e1, ← e2, hpos]
      have elvlx : (x - ρx - s) / s = (kx : ℤ) := by
        rw [hxe, show ρx + s + s * (kx : ℤ) - ρx - s = (kx : ℤ) * s from by ring]
        exact Int.mul_ediv_cancel _ (by omega)
      have elvly : (y - ρy - s) / s = (ky : ℤ) := by
        rw [hye, show ρy + s + s * (ky : ℤ) - ρy - s = (ky : ℤ) * s from by ring]
        exact Int.mul_ediv_cancel _ (by omega)
      have hkx' : p.2 = kx := by
        rw [hsndx, elvlx, Int.toNat_natCast]
      have hky' : ky = p.2 + 1 := by
        have e := hsndy
        rw [elvly, Int.toNat_natCast] at e
        exact e
      have hyeq : y = x + s := by
        rw [hye, hxe, hρ, hky', ← hkx']
        push_cast
        ring
      rw [hyeq] at hyT
      exact hss x hxT hyT
    · -- horizontal: `(i+1, k + δ i)` comes from `x + m`, excluded by
      -- `shiftFree m`; the wrap edge `i + 1 = c` is not constrained
      rintro p hp hpc hC
      rw [Finset.mem_image] at hp hC
      obtain ⟨x, hxT, hpx⟩ := hp
      obtain ⟨y, hyT, hpy⟩ := hC
      have hxU := hTU hxT
      have hyU := hTU hyT
      rw [Finset.mem_biUnion] at hxU hyU
      obtain ⟨ρx, hρx, hxρ⟩ := hxU
      obtain ⟨ρy, hρy, hyρ⟩ := hyU
      have hρxIcc := orbit_subset_Icc hs m r hρx
      have hρyIcc := orbit_subset_Icc hs m r hρy
      have hrx : ρx = (x - 1) % s + 1 := cls_residue_eq hs hρxIcc hxρ
      have hry : ρy = (y - 1) % s + 1 := cls_residue_eq hs hρyIcc hyρ
      obtain ⟨kx, -, hxe⟩ := cls_mem_iff.mp hxρ
      obtain ⟨ky, -, hye⟩ := cls_mem_iff.mp hyρ
      have hfstx : p.1 = orbitPos m s r ρx := by
        have e := congrArg Prod.fst hpx
        unfold orbitIdx at e
        rw [← hrx] at e
        exact e.symm
      have hfsty : orbitPos m s r ρy = p.1 + 1 := by
        have e := congrArg Prod.fst hpy
        unfold orbitIdx at e
        rw [← hry] at e
        exact e
      have hsndx : p.2 = ((x - ρx - s) / s).toNat := by
        have e := congrArg Prod.snd hpx
        unfold orbitIdx at e
        rw [← hrx] at e
        exact e.symm
      have hsndy : ((y - ρy - s) / s).toNat =
          p.2 + orbitTwist m s r p.1 := by
        have e := congrArg Prod.snd hpy
        unfold orbitIdx at e
        rw [← hry] at e
        exact e
      -- `ρy = orbitRep (p.1 + 1) = ρx + m - s·twist`
      have hρy1 : ρy = orbitRep m s r (p.1 + 1) := by
        have e := (orbitPos_spec hm hs hρy).2
        rw [hfsty] at e
        exact e.symm
      have hρx1 : orbitRep m s r p.1 = ρx := by
        have e := (orbitPos_spec hm hs hρx).2
        rw [← hfstx] at e
        exact e
      have htwist : ρy = ρx + m - s * (orbitTwist m s r p.1 : ℤ) := by
        rw [hρy1, orbitRep_succ_twist hm hms p.1, hρx1]
      have elvlx : (x - ρx - s) / s = (kx : ℤ) := by
        rw [hxe, show ρx + s + s * (kx : ℤ) - ρx - s = (kx : ℤ) * s from by ring]
        exact Int.mul_ediv_cancel _ (by omega)
      have elvly : (y - ρy - s) / s = (ky : ℤ) := by
        rw [hye, show ρy + s + s * (ky : ℤ) - ρy - s = (ky : ℤ) * s from by ring]
        exact Int.mul_ediv_cancel _ (by omega)
      have hkx' : p.2 = kx := by
        rw [hsndx, elvlx, Int.toNat_natCast]
      have hky' : ky = p.2 + orbitTwist m s r p.1 := by
        have e := hsndy
        rw [elvly, Int.toNat_natCast] at e
        exact e
      have hyeq : y = x + m := by
        rw [hye, hxe, htwist, hky', ← hkx']
        push_cast
        ring
      rw [hyeq] at hyT
      exact hsm x hxT hyT
  · -- `T ↦ T.image orbitIdx` is injective on subsets of the orbit union
    intro T₁ hT₁ T₂ hT₂ h
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset] at hT₁ hT₂
    ext x
    constructor
    · intro hx
      have hxU : x ∈ (orbit m s r).biUnion (cls n s) := hT₁.1 hx
      have hmem : orbitIdx n m s r x ∈ T₂.image (orbitIdx n m s r) := by
        rw [← h]
        exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
      obtain ⟨y, hyT, hyeq⟩ := Finset.mem_image.mp hmem
      have hyU : y ∈ (orbit m s r).biUnion (cls n s) := hT₂.1 hyT
      have hxy : x = y := orbitIdx_injOn hm hms hxU hyU hyeq.symm
      rwa [hxy]
    · intro hx
      have hxU : x ∈ (orbit m s r).biUnion (cls n s) := hT₂.1 hx
      have hmem : orbitIdx n m s r x ∈ T₁.image (orbitIdx n m s r) := by
        rw [h]
        exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
      obtain ⟨y, hyT, hyeq⟩ := Finset.mem_image.mp hmem
      have hyU : y ∈ (orbit m s r).biUnion (cls n s) := hT₁.1 hyT
      have hxy : x = y := orbitIdx_injOn hm hms hxU hyU hyeq.symm
      rwa [hxy]

end JSP000728
