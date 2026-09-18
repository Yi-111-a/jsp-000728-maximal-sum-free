import JSPProblem.OrbitDecomp
import JSPProblem.Ladder
import JSPProblem.LadderSharp
import JSPProblem.NoConsec
import JSPProblem.TwoMin
import Mathlib.Data.Finset.Powerset
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith

/-!
# JSP-000728 — closed-form count of the orbit strips

Discharges the conditional bound `card_powerset_filter_shiftFree2_Icc_le_orbitProd`:
the independent sets of an orbit strip `orbitStrips δ c L` are counted by
peeling off rail pairs `{0, 1}, {2, 3}, …`.  On the leading pair the twisted
edge `(0, k) → (1, k + δ 0)` becomes a **flat rung** after shearing rail `0`
up by `δ 0` levels (`pairShear`), so the pair projection lands in
`ladSets (L + δ 0)`; the two-step induction then gives

  `(orbitStrips δ c L).card ≤
      (∏ j ∈ range (c/2), (ladSets (L + δ (2j))).card) * fib (L+2) ^ (c%2)`

(`orbitStrips_card_le_ladProd_fib`).  For twists bounded by `1` — which covers
`orbitTwist` — this collapses to the uniform closed bound
`a(L+1)^{⌊c/2⌋} · F_{L+2}^{c%2}` (`orbitStrips_card_le`).

Combining with `card_powerset_filter_shiftFree2_orbitCls_le` and
`card_powerset_filter_shiftFree2_Icc_le_orbitProd` gives the closed orbit
bound `card ≤ B^{gcd s m}` with
`B = a(L+1)^{⌊c/2⌋} · F_{L+2}^{c%2}`
(`card_powerset_filter_shiftFree2_Icc_le_orbitPow`), where the number of
distinct orbits is computed as `gcd s m` (`orbit_image_card`).  Finally,
`ladSets_card_le_pell_pow` upgrades the result to the real-valued
`(1 + √2)`-power form (`card_powerset_filter_shiftFree2_Icc_le_realPow`),
a per-vertex rate tending to `√(1+√2) ≈ 1.5538`.
-/

namespace JSP000728

/-! ### The rail-pair shear -/

/-- The two-rail shear: rail `0` is lifted `d` levels so that the twisted
strip edge `(0, k) → (1, k + d)` becomes a flat ladder rung
`(false, k+d) ↔ (true, k+d)`. -/
def pairShear (d : ℕ) (p : ℕ × ℕ) : Bool × ℕ :=
  (decide (p.1 = 1), p.2 + (1 - p.1) * d)

/-- The shear is injective on rails `{0, 1}`. -/
theorem pairShear_injOn (d : ℕ) :
    Set.InjOn (pairShear d) {p : ℕ × ℕ | p.1 < 2} := by
  rintro ⟨i, k⟩ hi ⟨i', k'⟩ hi' h
  have hi2 : i < 2 := hi
  have hi2' : i' < 2 := hi'
  have e1 : decide (i = 1) = decide (i' = 1) := congrArg Prod.fst h
  have e2 : k + (1 - i) * d = k' + (1 - i') * d := congrArg Prod.snd h
  have eii : i = i' := by
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;>
      rcases (by omega : i' = 0 ∨ i' = 1) with rfl | rfl
    · rfl
    · exact absurd e1 (by decide)
    · exact absurd e1 (by decide)
    · rfl
  subst eii
  have ekk : k = k' := by omega
  subst ekk
  rfl
theorem pairShear_image_subset_ladVert {d L : ℕ} {t : Finset (ℕ × ℕ)}
    (ht : t ⊆ orbitStripVert 2 L) :
    t.image (pairShear d) ⊆ ladVert (L + d) := by
  intro q hq
  rw [Finset.mem_image] at hq
  obtain ⟨⟨i, k⟩, hp, rfl⟩ := hq
  have hv := ht hp
  rw [mem_orbitStripVert] at hv
  obtain ⟨hi, hk⟩ := hv
  rw [mem_ladVert]
  show k + (1 - i) * d < L + d
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> simp <;> omega

/-- The sheared image of a strip-free rail pair is ladder-free: strip
verticals give ladder verticals and the twisted edge gives the rung. -/
theorem ladFree_image_pairShear {δ : ℕ → ℕ} {L : ℕ} {t : Finset (ℕ × ℕ)}
    (hsub : t ⊆ orbitStripVert 2 L) (hfree : orbitStripFree δ 2 t) :
    ladFree (t.image (pairShear (δ 0))) := by
  obtain ⟨hvert, hedge⟩ := hfree
  refine ⟨?_, ?_⟩
  · -- no rail-successor `(q.1, q.2 + 1)`
    intro q hq hC
    rw [Finset.mem_image] at hq hC
    obtain ⟨⟨i, k⟩, hp, rfl⟩ := hq
    obtain ⟨⟨i', k'⟩, hp', h'⟩ := hC
    have hvi := hsub hp
    have hvi' := hsub hp'
    rw [mem_orbitStripVert] at hvi hvi'
    have e1 : decide (i' = 1) = decide (i = 1) := congrArg Prod.fst h'
    have e2 : k' + (1 - i') * δ 0 = k + (1 - i) * δ 0 + 1 :=
      congrArg Prod.snd h'
    have eii : i' = i := by
      rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;>
        rcases (by omega : i' = 0 ∨ i' = 1) with rfl | rfl
      · rfl
      · exact absurd e1 (by decide)
      · exact absurd e1 (by decide)
      · rfl
    rw [eii] at e2 hp'
    have ekk : k' = k + 1 := by omega
    rw [ekk] at hp'
    exact hvert (i, k) hp hp'
  · -- no rung-mate `(!q.1, q.2)`
    intro q hq hC
    rw [Finset.mem_image] at hq hC
    obtain ⟨⟨i, k⟩, hp, rfl⟩ := hq
    obtain ⟨⟨i', k'⟩, hp', h'⟩ := hC
    have hvi := hsub hp
    have hvi' := hsub hp'
    rw [mem_orbitStripVert] at hvi hvi'
    have e1 : decide (i' = 1) = !decide (i = 1) := congrArg Prod.fst h'
    have e2 : k' + (1 - i') * δ 0 = k + (1 - i) * δ 0 := congrArg Prod.snd h'
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;>
      rcases (by omega : i' = 0 ∨ i' = 1) with rfl | rfl
    · exact absurd e1 (by decide)
    · -- `(0,k) ∈ t` forces `(1, k + δ 0) ∉ t`
      have ek : k' = k + δ 0 := by omega
      subst ek
      exact hedge (0, k) hp (by norm_num) hp'
    · -- `(1,k) ∈ t` forces `(0, k - δ 0) ∉ t`
      have ek : k' + δ 0 = k := by omega
      have hno : (0 + 1, k' + δ 0) ∉ t := hedge (0, k') hp' (by norm_num)
      rw [ek] at hno
      exact hno hp
    · exact absurd e1 (by decide)

/-- **The rail-pair bound.**  The `c = 2` strip injects via the shear into
the `2 × (L + δ 0)` ladder. -/
theorem orbitStrips_two_card_le (δ : ℕ → ℕ) (L : ℕ) :
    (orbitStrips δ 2 L).card ≤ (ladSets (L + δ 0)).card := by
  refine Finset.card_le_card_of_injOn
    (fun t => t.image (pairShear (δ 0))) ?_ ?_
  · intro t ht
    rw [Finset.mem_coe, mem_orbitStrips] at ht
    rw [Finset.mem_coe, mem_ladSets]
    exact ⟨pairShear_image_subset_ladVert ht.1,
      ladFree_image_pairShear ht.1 ht.2⟩
  · intro t₁ ht₁ t₂ ht₂ h
    rw [Finset.mem_coe, mem_orbitStrips] at ht₁ ht₂
    have h' : t₁.image (pairShear (δ 0)) = t₂.image (pairShear (δ 0)) := h
    ext ⟨i, k⟩
    constructor
    · intro hp
      have hmem : pairShear (δ 0) (i, k) ∈ t₂.image (pairShear (δ 0)) := by
        rw [← h']
        exact Finset.mem_image.mpr ⟨(i, k), hp, rfl⟩
      obtain ⟨q, hq, hqeq⟩ := Finset.mem_image.mp hmem
      have heq : (i, k) = q := pairShear_injOn _
        (show (i, k).1 < 2 from (mem_orbitStripVert.mp (ht₁.1 hp)).1)
        (show q.1 < 2 from (mem_orbitStripVert.mp (ht₂.1 hq)).1) hqeq.symm
      rwa [heq]
    · intro hp
      have hmem : pairShear (δ 0) (i, k) ∈ t₁.image (pairShear (δ 0)) := by
        rw [h']
        exact Finset.mem_image.mpr ⟨(i, k), hp, rfl⟩
      obtain ⟨q, hq, hqeq⟩ := Finset.mem_image.mp hmem
      have heq : (i, k) = q := pairShear_injOn _
        (show (i, k).1 < 2 from (mem_orbitStripVert.mp (ht₂.1 hp)).1)
        (show q.1 < 2 from (mem_orbitStripVert.mp (ht₁.1 hq)).1) hqeq.symm
      rwa [heq]

/-! ### Peeling off a rail pair -/

/-- Split off the first two rails of a strip set: the low part
(`t.filter (·.1 < 2)`) and the high part re-indexed by `i ↦ i - 2`. -/
def stripSplit (t : Finset (ℕ × ℕ)) : Finset (ℕ × ℕ) × Finset (ℕ × ℕ) :=
  (t.filter fun p => p.1 < 2,
    (t.filter fun p => 2 ≤ p.1).image fun p => (p.1 - 2, p.2))

/-- The low part is an element of the `c = 2` strip. -/
theorem stripSplit_fst_mem {δ : ℕ → ℕ} {c L : ℕ} {t : Finset (ℕ × ℕ)}
    (ht : t ∈ orbitStrips δ c L) :
    (stripSplit t).1 ∈ orbitStrips δ 2 L := by
  rw [mem_orbitStrips] at ht ⊢
  obtain ⟨hsub, hvert, hedge⟩ := ht
  refine ⟨?_, ⟨?_, ?_⟩⟩
  · rintro ⟨i, k⟩ hp
    have hp' : (i, k) ∈ t.filter (fun p => p.1 < 2) := hp
    rw [Finset.mem_filter] at hp'
    have hv := hsub hp'.1
    rw [mem_orbitStripVert] at hv ⊢
    exact ⟨hp'.2, hv.2⟩
  · rintro ⟨i, k⟩ hp hC
    have hp' : (i, k) ∈ t.filter (fun p => p.1 < 2) := hp
    have hC' : (i, k + 1) ∈ t.filter (fun p => p.1 < 2) := hC
    rw [Finset.mem_filter] at hp' hC'
    exact hvert (i, k) hp'.1 hC'.1
  · rintro ⟨i, k⟩ hp hi2 hC
    have hp' : (i, k) ∈ t.filter (fun p => p.1 < 2) := hp
    have hC' : (i + 1, k + δ i) ∈ t.filter (fun p => p.1 < 2) := hC
    rw [Finset.mem_filter] at hp' hC'
    have hv := hsub hC'.1
    rw [mem_orbitStripVert] at hv
    exact hedge (i, k) hp'.1 hv.1 hC'.1

/-- The re-indexed high part is an element of the `c - 2` strip with the
shifted twist `i ↦ δ (i + 2)`. -/
theorem stripSplit_snd_mem {δ : ℕ → ℕ} {c L : ℕ} {t : Finset (ℕ × ℕ)}
    (ht : t ∈ orbitStrips δ c L) :
    (stripSplit t).2 ∈ orbitStrips (fun i => δ (i + 2)) (c - 2) L := by
  rw [mem_orbitStrips] at ht ⊢
  obtain ⟨hsub, hvert, hedge⟩ := ht
  refine ⟨?_, ⟨?_, ?_⟩⟩
  · rintro ⟨i, k⟩ hp
    have hp' : (i, k) ∈ (t.filter fun p => 2 ≤ p.1).image
        (fun p => (p.1 - 2, p.2)) := hp
    rw [Finset.mem_image] at hp'
    obtain ⟨⟨j, ℓ⟩, hpj, hje⟩ := hp'
    rw [Finset.mem_filter] at hpj
    have hv := hsub hpj.1
    rw [mem_orbitStripVert] at hv ⊢
    have e1 : j - 2 = i := (Prod.ext_iff.mp hje).1
    have e2 : ℓ = k := (Prod.ext_iff.mp hje).2
    have hj2 : 2 ≤ j := hpj.2
    refine ⟨?_, ?_⟩
    · omega
    · rw [← e2]; exact hv.2
  · rintro ⟨i, k⟩ hp hC
    have hp' : (i, k) ∈ (t.filter fun p => 2 ≤ p.1).image
        (fun p => (p.1 - 2, p.2)) := hp
    have hC' : (i, k + 1) ∈ (t.filter fun p => 2 ≤ p.1).image
        (fun p => (p.1 - 2, p.2)) := hC
    rw [Finset.mem_image] at hp' hC'
    obtain ⟨⟨j, ℓ⟩, hpj, hje⟩ := hp'
    obtain ⟨⟨j', ℓ'⟩, hpj', hje'⟩ := hC'
    rw [Finset.mem_filter] at hpj hpj'
    have e1 : j - 2 = i := (Prod.ext_iff.mp hje).1
    have e2 : ℓ = k := (Prod.ext_iff.mp hje).2
    have e3 : j' - 2 = i := (Prod.ext_iff.mp hje').1
    have e4 : ℓ' = k + 1 := (Prod.ext_iff.mp hje').2
    have hj2 : 2 ≤ j := hpj.2
    have hj2' : 2 ≤ j' := hpj'.2
    have hjj : j' = j := by omega
    have hll : ℓ' = ℓ + 1 := by omega
    have hmem : (j, ℓ + 1) ∈ t := by
      have e : (j', ℓ') = (j, ℓ + 1) := by rw [hjj, hll]
      rw [e] at hpj'
      exact hpj'.1
    exact hvert (j, ℓ) hpj.1 hmem
  · rintro ⟨i, k⟩ hp hi2 hC
    have hp' : (i, k) ∈ (t.filter fun p => 2 ≤ p.1).image
        (fun p => (p.1 - 2, p.2)) := hp
    have hC' : (i + 1, k + (fun i => δ (i + 2)) i) ∈
        (t.filter fun p => 2 ≤ p.1).image
          (fun p => (p.1 - 2, p.2)) := hC
    rw [Finset.mem_image] at hp' hC'
    obtain ⟨⟨j, ℓ⟩, hpj, hje⟩ := hp'
    obtain ⟨⟨j', ℓ'⟩, hpj', hje'⟩ := hC'
    rw [Finset.mem_filter] at hpj hpj'
    have e1 : j - 2 = i := (Prod.ext_iff.mp hje).1
    have e2 : ℓ = k := (Prod.ext_iff.mp hje).2
    have e3 : j' - 2 = i + 1 := (Prod.ext_iff.mp hje').1
    have e4 : ℓ' = k + δ (i + 2) := (Prod.ext_iff.mp hje').2
    have hj2 : 2 ≤ j := hpj.2
    have hj2' : 2 ≤ j' := hpj'.2
    have hjj : j' = j + 1 := by omega
    have hij : i + 2 = j := by omega
    have e4' : ℓ' = k + δ (i + 2) := e4
    rw [hij] at e4'
    have hll : ℓ' = ℓ + δ j := e4'.trans (by rw [e2])
    have hc : j + 1 < c := by omega
    have hmem : (j + 1, ℓ + δ j) ∈ t := by
      have e : (j', ℓ') = (j + 1, ℓ + δ j) := by rw [hjj, hll]
      rw [e] at hpj'
      exact hpj'.1
    exact hedge (j, ℓ) hpj.1 hc hmem

/-- **Pair-peeling bound.**  Removing the first two rails factors the
strip count: `strips(δ, c) ≤ strips(δ, 2) · strips(δ(·+2), c-2)`. -/
theorem orbitStrips_card_peel (δ : ℕ → ℕ) (c L : ℕ) :
    (orbitStrips δ c L).card ≤
      (orbitStrips δ 2 L).card *
        (orbitStrips (fun i => δ (i + 2)) (c - 2) L).card := by
  rw [← Finset.card_product]
  refine Finset.card_le_card_of_injOn stripSplit ?_ ?_
  · intro t ht
    rw [Finset.mem_coe, Finset.mem_product]
    exact ⟨stripSplit_fst_mem ht, stripSplit_snd_mem ht⟩
  · intro t₁ ht₁ t₂ ht₂ h
    rw [Finset.mem_coe, mem_orbitStrips] at ht₁ ht₂
    have hfst : (t₁.filter fun p => p.1 < 2) =
        t₂.filter fun p => p.1 < 2 := congrArg Prod.fst h
    have hsnd : (t₁.filter fun p => 2 ≤ p.1).image
        (fun p => (p.1 - 2, p.2)) =
        (t₂.filter fun p => 2 ≤ p.1).image (fun p => (p.1 - 2, p.2)) :=
      congrArg Prod.snd h
    ext ⟨i, k⟩
    constructor
    · intro hp
      rcases lt_or_ge i 2 with hi | hi
      · have hmem : (i, k) ∈ t₂.filter (fun p => p.1 < 2) := by
          rw [← hfst]
          exact Finset.mem_filter.mpr ⟨hp, hi⟩
        exact (Finset.mem_filter.mp hmem).1
      · have hmem : (i - 2, k) ∈ (t₂.filter fun p => 2 ≤ p.1).image
            (fun p => (p.1 - 2, p.2)) := by
          rw [← hsnd]
          exact Finset.mem_image.mpr
            ⟨(i, k), Finset.mem_filter.mpr ⟨hp, hi⟩, rfl⟩
        obtain ⟨⟨j, ℓ⟩, hj, hje⟩ := Finset.mem_image.mp hmem
        rw [Finset.mem_filter] at hj
        have e1 : j - 2 = i - 2 := (Prod.ext_iff.mp hje).1
        have e2 : ℓ = k := (Prod.ext_iff.mp hje).2
        have hj2 : 2 ≤ j := hj.2
        have ejj : j = i := by omega
        have ell : ℓ = k := e2
        have e : (j, ℓ) = (i, k) := by rw [ejj, ell]
        rw [e] at hj
        exact hj.1
    · intro hp
      rcases lt_or_ge i 2 with hi | hi
      · have hmem : (i, k) ∈ t₁.filter (fun p => p.1 < 2) := by
          rw [hfst]
          exact Finset.mem_filter.mpr ⟨hp, hi⟩
        exact (Finset.mem_filter.mp hmem).1
      · have hmem : (i - 2, k) ∈ (t₁.filter fun p => 2 ≤ p.1).image
            (fun p => (p.1 - 2, p.2)) := by
          rw [hsnd]
          exact Finset.mem_image.mpr
            ⟨(i, k), Finset.mem_filter.mpr ⟨hp, hi⟩, rfl⟩
        obtain ⟨⟨j, ℓ⟩, hj, hje⟩ := Finset.mem_image.mp hmem
        rw [Finset.mem_filter] at hj
        have e1 : j - 2 = i - 2 := (Prod.ext_iff.mp hje).1
        have e2 : ℓ = k := (Prod.ext_iff.mp hje).2
        have hj2 : 2 ≤ j := hj.2
        have ejj : j = i := by omega
        have ell : ℓ = k := e2
        have e : (j, ℓ) = (i, k) := by rw [ejj, ell]
        rw [e] at hj
        exact hj.1

/-! ### Base cases -/

/-- The `c = 0` strip is just `{∅}`. -/
theorem orbitStrips_zero (δ : ℕ → ℕ) (L : ℕ) :
    orbitStrips δ 0 L = {∅} := by
  ext t
  rw [mem_orbitStrips]
  have h0 : orbitStripVert 0 L = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    rintro ⟨i, k⟩
    rw [mem_orbitStripVert]
    omega
  rw [h0, Finset.subset_empty]
  constructor
  · rintro ⟨rfl, -⟩
    exact Finset.mem_singleton_self _
  · intro h
    rw [Finset.mem_singleton] at h
    subst h
    refine ⟨rfl, fun p hp => absurd hp (Finset.notMem_empty _),
      fun p hp _ => absurd hp (Finset.notMem_empty _)⟩

/-- The `c = 1` strip is a no-consecutive path: `t ↦ t.image Prod.snd`
injects it into `ncSets L`. -/
theorem orbitStrips_one_card_le (δ : ℕ → ℕ) (L : ℕ) :
    (orbitStrips δ 1 L).card ≤ (ncSets L).card := by
  refine Finset.card_le_card_of_injOn (fun t => t.image Prod.snd) ?_ ?_
  · intro t ht
    rw [Finset.mem_coe, mem_orbitStrips] at ht
    obtain ⟨hsub, hvert, -⟩ := ht
    rw [Finset.mem_coe, mem_ncSets]
    refine ⟨?_, ?_⟩
    · intro k hk
      rw [Finset.mem_image] at hk
      obtain ⟨⟨i, k'⟩, hp, rfl⟩ := hk
      have hv := hsub hp
      rw [mem_orbitStripVert] at hv
      rw [Finset.mem_range]
      exact hv.2
    · intro k hk hC
      rw [Finset.mem_image] at hk hC
      obtain ⟨⟨i, k'⟩, hp, he⟩ := hk
      obtain ⟨⟨i', k''⟩, hp', he'⟩ := hC
      have hv := hsub hp
      have hv' := hsub hp'
      rw [mem_orbitStripVert] at hv hv'
      have hi : i = 0 := by omega
      have hi' : i' = 0 := by omega
      have ek : k' = k := he
      have ek' : k'' = k + 1 := he'
      have hmem : (i, k + 1) ∈ t := by
        have e : (i', k'') = (i, k + 1) := by rw [hi', ek', hi]
        rwa [e] at hp'
      rw [ek] at hp
      exact hvert (i, k) hp hmem
  · intro t₁ ht₁ t₂ ht₂ h
    have h' : t₁.image Prod.snd = t₂.image Prod.snd := h
    rw [Finset.mem_coe, mem_orbitStrips] at ht₁ ht₂
    ext ⟨i, k⟩
    constructor
    · intro hp
      have hv := ht₁.1 hp
      rw [mem_orbitStripVert] at hv
      have hi : i = 0 := by omega
      subst hi
      have hmem : k ∈ t₂.image Prod.snd := by
        rw [← h']
        exact Finset.mem_image.mpr ⟨(0, k), hp, rfl⟩
      obtain ⟨⟨i', k'⟩, hp', he⟩ := Finset.mem_image.mp hmem
      have hv' := ht₂.1 hp'
      rw [mem_orbitStripVert] at hv'
      have ek : k' = k := he
      have hi' : i' = 0 := by omega
      have e : (i', k') = (0, k) := by rw [hi', ek]
      rwa [e] at hp'
    · intro hp
      have hv := ht₂.1 hp
      rw [mem_orbitStripVert] at hv
      have hi : i = 0 := by omega
      subst hi
      have hmem : k ∈ t₁.image Prod.snd := by
        rw [h']
        exact Finset.mem_image.mpr ⟨(0, k), hp, rfl⟩
      obtain ⟨⟨i', k'⟩, hp', he⟩ := Finset.mem_image.mp hmem
      have hv' := ht₁.1 hp'
      rw [mem_orbitStripVert] at hv'
      have ek : k' = k := he
      have hi' : i' = 0 := by omega
      have e : (i', k') = (0, k) := by rw [hi', ek]
      rwa [e] at hp'

/-! ### The strip count -/

/-- **Twist-sensitive strip count.**  Pairing the rails
`(0,1), (2,3), …` gives a `ladSets (L + δ (2j))` factor per pair; an odd
trailing rail contributes a Fibonacci `ncSets` factor. -/
theorem orbitStrips_card_le_ladProd_fib (L : ℕ) (δ : ℕ → ℕ) (c : ℕ) :
    (orbitStrips δ c L).card ≤
      (∏ j ∈ Finset.range (c / 2), (ladSets (L + δ (2 * j))).card) *
        Nat.fib (L + 2) ^ (c % 2) := by
  induction c using Nat.twoStepInduction generalizing δ with
  | zero =>
      rw [orbitStrips_zero]
      simp
  | one =>
      have h1 := orbitStrips_one_card_le δ L
      rw [ncSets_card] at h1
      refine h1.trans_eq ?_
      simp
  | more k ih ih1 =>
      have hpeel := orbitStrips_card_peel δ (k + 2) L
      rw [show k + 2 - 2 = k from rfl] at hpeel
      have hih := ih (fun i => δ (i + 2))
      have hdiv : (k + 2) / 2 = k / 2 + 1 := by omega
      have hmod : (k + 2) % 2 = k % 2 := by omega
      have hprod : (∏ j ∈ Finset.range (k / 2),
          (ladSets (L + (fun i => δ (i + 2)) (2 * j))).card) =
          ∏ j ∈ Finset.range (k / 2),
            (ladSets (L + δ (2 * (j + 1)))).card := by
        apply Finset.prod_congr rfl
        intro j _
        congr 1
      calc (orbitStrips δ (k + 2) L).card
          ≤ (orbitStrips δ 2 L).card *
              (orbitStrips (fun i => δ (i + 2)) k L).card := hpeel
        _ ≤ (ladSets (L + δ 0)).card *
              ((∏ j ∈ Finset.range (k / 2),
                  (ladSets (L + δ (2 * (j + 1)))).card) *
                Nat.fib (L + 2) ^ (k % 2)) :=
            Nat.mul_le_mul (orbitStrips_two_card_le δ L)
              (hih.trans (Nat.mul_le_mul (le_of_eq hprod) le_rfl))
        _ = (∏ j ∈ Finset.range ((k + 2) / 2),
                (ladSets (L + δ (2 * j))).card) *
              Nat.fib (L + 2) ^ ((k + 2) % 2) := by
            rw [hdiv, hmod, Finset.prod_range_succ', mul_left_comm,
              ← mul_assoc]

/-- `ladSets` is monotone in the ladder length. -/
theorem ladSets_mono_of_le {a b : ℕ} (h : a ≤ b) : ladSets a ⊆ ladSets b := by
  intro t ht
  rw [mem_ladSets] at ht ⊢
  refine ⟨?_, ht.2⟩
  rintro ⟨c, j⟩ hp
  have hv := ht.1 hp
  rw [mem_ladVert] at hv ⊢
  omega

/-- **Uniform strip count** for twists bounded by `1` (e.g. `orbitTwist`):
`a(L+1)^{⌊c/2⌋} · F_{L+2}^{c\%2}`. -/
theorem orbitStrips_card_le (δ : ℕ → ℕ) (hδ : ∀ i, δ i ≤ 1) (c L : ℕ) :
    (orbitStrips δ c L).card ≤
      (ladSets (L + 1)).card ^ (c / 2) * Nat.fib (L + 2) ^ (c % 2) := by
  refine (orbitStrips_card_le_ladProd_fib L δ c).trans ?_
  have hprod : (∏ j ∈ Finset.range (c / 2),
      (ladSets (L + δ (2 * j))).card) ≤
      (ladSets (L + 1)).card ^ (c / 2) := by
    have hrw : (ladSets (L + 1)).card ^ (c / 2) =
        ∏ _j ∈ Finset.range (c / 2), (ladSets (L + 1)).card := by
      rw [Finset.prod_const, Finset.card_range]
    rw [hrw]
    apply Finset.prod_le_prod
    intro j _
    apply Finset.card_le_card
    apply ladSets_mono_of_le
    have := hδ (2 * j)
    omega
  exact Nat.mul_le_mul hprod le_rfl

/-- The orbit twist only takes the values `0` and `1`. -/
theorem orbitTwist_le_one (m s r : ℤ) (i : ℕ) : orbitTwist m s r i ≤ 1 := by
  unfold orbitTwist
  split <;> norm_num

/-! ### Per-orbit and global closed bounds -/

/-- **Per-orbit closed bound.**  `shiftFree2 m s` subsets of the `r`-orbit's
rail union are at most `a(L+1)^{⌊c/2⌋} · F_{L+2}^{c\%2}`, where
`c = orbitLen m s` and `L = ((n-1)/s).toNat`. -/
theorem card_powerset_filter_shiftFree2_orbitCls_le_closed {n : ℕ} {m s r : ℤ}
    (hm : 1 ≤ m) (hms : m < s) :
    (((orbit m s r).biUnion (cls n s)).powerset.filter
        (shiftFree2 m s)).card ≤
      (ladSets ((((n : ℤ) - 1) / s).toNat + 1)).card ^ (orbitLen m s / 2) *
        Nat.fib ((((n : ℤ) - 1) / s).toNat + 2) ^ (orbitLen m s % 2) :=
  (card_powerset_filter_shiftFree2_orbitCls_le hm hms).trans
    (orbitStrips_card_le (orbitTwist m s r)
      (fun i => orbitTwist_le_one m s r i) (orbitLen m s) _)

/-- The number of distinct `+m` orbits on the `s` rails is `gcd s m`:
the orbits partition `Icc 1 s` into classes of size `orbitLen m s`, and
`gcd · orbitLen = s`. -/
theorem orbit_image_card (hm : 1 ≤ m) (hs : 1 ≤ s) :
    ((Finset.Icc 1 s).image (orbit m s)).card = Int.gcd s m := by
  have hcover : ((Finset.Icc 1 s).image (orbit m s)).biUnion id =
      Finset.Icc 1 s := by
    apply le_antisymm
    · rw [Finset.biUnion_subset]
      intro O hO
      rw [Finset.mem_image] at hO
      obtain ⟨r, hr, rfl⟩ := hO
      exact orbit_subset_Icc hs m r
    · intro r hr
      rw [Finset.mem_biUnion]
      exact ⟨orbit m s r, Finset.mem_image.mpr ⟨r, hr, rfl⟩,
        orbit_self_mem hs hr⟩
  have hcard : (((Finset.Icc 1 s).image (orbit m s)).biUnion id).card =
      s.toNat := by
    rw [hcover, Int.card_Icc]
    congr 1
    omega
  rw [Finset.card_biUnion (orbit_image_pairwiseDisjoint hm hs)] at hcard
  have hsum : ∑ O ∈ (Finset.Icc 1 s).image (orbit m s), (id O).card =
      ((Finset.Icc 1 s).image (orbit m s)).card * orbitLen m s := by
    calc ∑ O ∈ (Finset.Icc 1 s).image (orbit m s), (id O).card
        = ∑ _O ∈ (Finset.Icc 1 s).image (orbit m s), orbitLen m s :=
          Finset.sum_congr rfl fun O hO => by
            rw [Finset.mem_image] at hO
            obtain ⟨r, hr, rfl⟩ := hO
            exact orbit_card hm hs r
      _ = ((Finset.Icc 1 s).image (orbit m s)).card * orbitLen m s := by
          rw [Finset.sum_const, smul_eq_mul]
  rw [hsum] at hcard
  have hgs : Int.gcd s m * orbitLen m s = s.toNat := by
    have h := gcd_mul_orbitLen (m := m) hs
    have h2 : ((Int.gcd s m * orbitLen m s : ℕ) : ℤ) = s := by
      rw [Nat.cast_mul]
      exact h
    have h3 := congrArg Int.toNat h2
    rwa [Int.toNat_natCast] at h3
  have e : ((Finset.Icc 1 s).image (orbit m s)).card * orbitLen m s =
      Int.gcd s m * orbitLen m s := hcard.trans hgs.symm
  exact Nat.mul_right_cancel (orbitLen_pos hm hs) e

/-- **Closed orbit-power bound.**  The `B O` hypothesis of
`card_powerset_filter_shiftFree2_Icc_le_orbitProd` is discharged uniformly,
so the product over the distinct orbits collapses to a `gcd s m`-th power. -/
theorem card_powerset_filter_shiftFree2_Icc_le_orbitPow {n : ℕ} {m s : ℤ}
    (hm : 1 ≤ m) (hms : m < s) :
    ((Finset.Icc (s + 1) (n : ℤ)).powerset.filter (shiftFree2 m s)).card ≤
      ((ladSets ((((n : ℤ) - 1) / s).toNat + 1)).card ^ (orbitLen m s / 2) *
        Nat.fib ((((n : ℤ) - 1) / s).toNat + 2) ^ (orbitLen m s % 2)) ^
        Int.gcd s m := by
  have hs : 1 ≤ s := by omega
  have hB : ∀ O ∈ (Finset.Icc 1 s).image (orbit m s),
      ((O.biUnion (cls n s)).powerset.filter (shiftFree2 m s)).card ≤
        (ladSets ((((n : ℤ) - 1) / s).toNat + 1)).card ^ (orbitLen m s / 2) *
          Nat.fib ((((n : ℤ) - 1) / s).toNat + 2) ^ (orbitLen m s % 2) := by
    intro O hO
    rw [Finset.mem_image] at hO
    obtain ⟨r, hr, rfl⟩ := hO
    exact card_powerset_filter_shiftFree2_orbitCls_le_closed hm hms
  calc ((Finset.Icc (s + 1) (n : ℤ)).powerset.filter (shiftFree2 m s)).card
      ≤ ∏ O ∈ (Finset.Icc 1 s).image (orbit m s),
          ((ladSets ((((n : ℤ) - 1) / s).toNat + 1)).card ^
              (orbitLen m s / 2) *
            Nat.fib ((((n : ℤ) - 1) / s).toNat + 2) ^ (orbitLen m s % 2)) :=
        card_powerset_filter_shiftFree2_Icc_le_orbitProd hm hms hB
    _ = ((ladSets ((((n : ℤ) - 1) / s).toNat + 1)).card ^
            (orbitLen m s / 2) *
          Nat.fib ((((n : ℤ) - 1) / s).toNat + 2) ^ (orbitLen m s % 2)) ^
          ((Finset.Icc 1 s).image (orbit m s)).card := Finset.prod_const _
    _ = ((ladSets ((((n : ℤ) - 1) / s).toNat + 1)).card ^
            (orbitLen m s / 2) *
          Nat.fib ((((n : ℤ) - 1) / s).toNat + 2) ^ (orbitLen m s % 2)) ^
          Int.gcd s m := by rw [orbit_image_card hm hs]

/-- **Real-valued form.**  With `a(L+1) ≤ 5/4·(1+√2)^{L+1}`
(`ladSets_card_le_pell_pow`) and `F_{L+2} ≤ 2^{L+1}`
(`fib_add_two_le_two_pow`), the count is at most
`(5/4·(1+√2)^{L+1})^{g·⌊c/2⌋} · (2^{L+1})^{g·(c\%2)}` — a per-vertex rate
tending to `√(1+√2) ≈ 1.5538` as `L → ∞`. -/
theorem card_powerset_filter_shiftFree2_Icc_le_realPow {n : ℕ} {m s : ℤ}
    (hm : 1 ≤ m) (hms : m < s) :
    (((Finset.Icc (s + 1) (n : ℤ)).powerset.filter (shiftFree2 m s)).card : ℝ) ≤
      (5 / 4 * (1 + Real.sqrt 2) ^ ((((n : ℤ) - 1) / s).toNat + 1)) ^
          (orbitLen m s / 2 * Int.gcd s m) *
        ((2 : ℝ) ^ ((((n : ℤ) - 1) / s).toNat + 1)) ^
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
      (2 : ℝ) ^ ((((n : ℤ) - 1) / s).toNat + 1) := by
    have h := fib_add_two_le_two_pow (((n : ℤ) - 1) / s).toNat
    have h' : Nat.fib ((((n : ℤ) - 1) / s).toNat + 2) ≤
        2 ^ ((((n : ℤ) - 1) / s).toNat + 1) := h
    exact_mod_cast h'
  have hA0 : (0 : ℝ) ≤ (ladSets ((((n : ℤ) - 1) / s).toNat + 1)).card :=
    Nat.cast_nonneg _
  have hF0 : (0 : ℝ) ≤ Nat.fib ((((n : ℤ) - 1) / s).toNat + 2) :=
    Nat.cast_nonneg _
  have hB0 : (0 : ℝ) ≤ 5 / 4 * (1 + Real.sqrt 2) ^
      ((((n : ℤ) - 1) / s).toNat + 1) := le_trans hA0 hA
  have h20 : (0 : ℝ) ≤ (2 : ℝ) ^ ((((n : ℤ) - 1) / s).toNat + 1) :=
    le_trans hF0 hF
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
          ((2 : ℝ) ^ ((((n : ℤ) - 1) / s).toNat + 1)) ^
            (orbitLen m s % 2 * Int.gcd s m) :=
        mul_le_mul (pow_le_pow_left₀ hA0 hA _) (pow_le_pow_left₀ hF0 hF _)
          (pow_nonneg hF0 _) (pow_nonneg hB0 _)

end JSP000728
