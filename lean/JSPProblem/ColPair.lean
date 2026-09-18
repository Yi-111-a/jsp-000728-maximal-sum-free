import JSPProblem.TwoMin
import JSPProblem.TwoMinBound
import JSPProblem.NoConsec

/-!
# JSP-000728 — column-block bounds for `shiftFree2`

Within a "column" `Icc a (a + s - 1)` of length `s`, the `s`-shift maps
every element outside the column, so only the `m`-matching matters: the
`s - m` disjoint pairs `{x, x + m}` (`x ∈ Icc a (a + s - m - 1)`) each
contribute at most `3` admissible subsets, and the `2m - s` leftover
elements `Icc (a + s - m) (a + m - 1)` contribute a factor `2` each
(`card_powerset_filter_shiftFree2_col_le`).

Within a "double column" `Icc a (a + 2*s - 1)` of length `2s`, the blocks
`Q_x = {x, x+m, x+s, x+s+m}` (`x ∈ Icc a (a + s - m - 1)`) each carry a
4-cycle of forbidden distances (the `m`-edges `x—x+m`, `x+s—x+s+m` and the
`s`-edges `x—x+s`, `x+m—x+s+m`), whose independent sets number `7`
(`card_powerset_filter_shiftFree2_quad_le`); the `2m - s` leftover pairs
`{y, y + s}` contribute `3` each
(`card_powerset_filter_shiftFree2_colPair_le`).

`card_powerset_filter_shiftFree2_Icc_le_colBlocks` assembles the
double-column bound over `Icc (s + 1) n`.
-/

namespace JSP000728

/-- A two-element block `{x, x + d}` sharing one of the forbidden
distances (`d = m` or `d = s`) has only three admissible subsets:
`∅`, `{x}`, `{x + d}` — the full pair is excluded by the `d`-shift. -/
theorem powerset_filter_shiftFree2_pair_subset {m s d x : ℤ}
    (hd : d = m ∨ d = s) :
    ({x, x + d} : Finset ℤ).powerset.filter (shiftFree2 m s) ⊆
      {∅, {x}, {x + d}} := by
  intro t ht
  rw [Finset.mem_filter, Finset.mem_powerset] at ht
  obtain ⟨htsub, hsf⟩ := ht
  rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton]
  by_cases hx : x ∈ t
  · by_cases hxd : x + d ∈ t
    · rcases hd with rfl | rfl
      · exact absurd hxd (hsf.1 x hx)
      · exact absurd hxd (hsf.2 x hx)
    · refine Or.inr (Or.inl ?_)
      apply Finset.eq_singleton_iff_unique_mem.mpr
      refine ⟨hx, ?_⟩
      intro y hy
      have hy2 := htsub hy
      rw [Finset.mem_insert, Finset.mem_singleton] at hy2
      rcases hy2 with rfl | rfl
      · rfl
      · exact absurd hy hxd
  · by_cases hxd : x + d ∈ t
    · refine Or.inr (Or.inr ?_)
      apply Finset.eq_singleton_iff_unique_mem.mpr
      refine ⟨hxd, ?_⟩
      intro y hy
      have hy2 := htsub hy
      rw [Finset.mem_insert, Finset.mem_singleton] at hy2
      rcases hy2 with rfl | rfl
      · exact absurd hy hx
      · rfl
    · refine Or.inl ?_
      rw [Finset.eq_empty_iff_forall_notMem]
      intro y hy
      have hy2 := htsub hy
      rw [Finset.mem_insert, Finset.mem_singleton] at hy2
      rcases hy2 with rfl | rfl
      · exact hx hy
      · exact hxd hy

/-- The pair block `{x, x + d}` contributes at most `3`. -/
theorem card_powerset_filter_shiftFree2_pair_le {m s d x : ℤ}
    (hd : d = m ∨ d = s) :
    (({x, x + d} : Finset ℤ).powerset.filter (shiftFree2 m s)).card ≤ 3 := by
  refine (Finset.card_le_card
    (powerset_filter_shiftFree2_pair_subset hd)).trans ?_
  calc ({∅, {x}, {x + d}} : Finset (Finset ℤ)).card
      ≤ ({{x}, {x + d}} : Finset (Finset ℤ)).card + 1 :=
        Finset.card_insert_le _ _
    _ ≤ (({{x + d}} : Finset (Finset ℤ)).card + 1) + 1 :=
        Nat.add_le_add_right (Finset.card_insert_le _ _) 1
    _ = 3 := by rw [Finset.card_singleton]

/-- **The 4-cycle bound.**  On the block
`Q = {x, x+m, x+s, x+s+m}` the internal `m`-edges `x—x+m`,
`x+s—x+s+m` and the `s`-edges `x—x+s`, `x+m—x+s+m` form a 4-cycle, whose
independent sets number `7`.  Splitting `Q` into the `m`-pair
`A = {x, x+m}` and `B = {x+s, x+s+m}` gives `3 × 3` candidate halves, and
the two `s`-edges rule out the combinations `({x}, {x+s})` and
`({x+m}, {x+s+m})`, leaving `9 - 2 = 7`. -/
theorem card_powerset_filter_shiftFree2_quad_le {m s x : ℤ}
    (hm : 1 ≤ m) (hms : m < s) :
    (({x, x + m, x + s, x + s + m} : Finset ℤ).powerset.filter
        (shiftFree2 m s)).card ≤ 7 := by
  have hQ : ({x, x + m, x + s, x + s + m} : Finset ℤ) ⊆
      {x, x + m} ∪ {x + s, x + s + m} := by
    intro y hy
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert,
      Finset.mem_singleton] at hy
    rw [Finset.mem_union]
    rcases hy with rfl | rfl | rfl | rfl
    · exact Or.inl (Finset.mem_insert_self _ _)
    · exact Or.inl (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    · exact Or.inr (Finset.mem_insert_self _ _)
    · exact Or.inr (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have hA : ({x, x + m} : Finset ℤ).powerset.filter (shiftFree2 m s) ⊆
      {∅, {x}, {x + m}} :=
    powerset_filter_shiftFree2_pair_subset (Or.inl rfl)
  have hB : ({x + s, x + s + m} : Finset ℤ).powerset.filter
      (shiftFree2 m s) ⊆ {∅, {x + s}, {x + s + m}} :=
    powerset_filter_shiftFree2_pair_subset (Or.inl rfl)
  have hSA : ({∅, {x}, {x + m}} : Finset (Finset ℤ)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by
          intro h
          rw [Finset.mem_insert, Finset.mem_singleton] at h
          rcases h with h | h
          · exact (Finset.singleton_ne_empty x) h.symm
          · exact (Finset.singleton_ne_empty _) h.symm),
      Finset.card_insert_of_notMem (by
          intro h
          rw [Finset.mem_singleton] at h
          exact absurd (Finset.singleton_inj.mp h) (by omega)),
      Finset.card_singleton]
  have hSB : ({∅, {x + s}, {x + s + m}} : Finset (Finset ℤ)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by
          intro h
          rw [Finset.mem_insert, Finset.mem_singleton] at h
          rcases h with h | h
          · exact (Finset.singleton_ne_empty _) h.symm
          · exact (Finset.singleton_ne_empty _) h.symm),
      Finset.card_insert_of_notMem (by
          intro h
          rw [Finset.mem_singleton] at h
          exact absurd (Finset.singleton_inj.mp h) (by omega)),
      Finset.card_singleton]
  have h7 : (((({∅, {x}, {x + m}} : Finset (Finset ℤ)) ×ˢ
          ({∅, {x + s}, {x + s + m}} : Finset (Finset ℤ))).erase
        (({x}, {x + s}) : Finset ℤ × Finset ℤ)).erase
        (({x + m}, {x + s + m}) : Finset ℤ × Finset ℤ)).card = 7 := by
    have hp1 : (({x}, {x + s}) : Finset ℤ × Finset ℤ) ∈
        ({∅, {x}, {x + m}} : Finset (Finset ℤ)) ×ˢ
          ({∅, {x + s}, {x + s + m}} : Finset (Finset ℤ)) :=
      Finset.mem_product.mpr
        ⟨Finset.mem_insert_of_mem (Finset.mem_insert_self _ _),
          Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)⟩
    have hp2 : (({x + m}, {x + s + m}) : Finset ℤ × Finset ℤ) ∈
        (({∅, {x}, {x + m}} : Finset (Finset ℤ)) ×ˢ
          ({∅, {x + s}, {x + s + m}} : Finset (Finset ℤ))).erase
          (({x}, {x + s}) : Finset ℤ × Finset ℤ) :=
      Finset.mem_erase.mpr
        ⟨fun h => absurd (Finset.singleton_inj.mp (congrArg Prod.fst h))
            (by omega),
          Finset.mem_product.mpr
            ⟨Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
                (Finset.mem_singleton_self _)),
              Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
                (Finset.mem_singleton_self _))⟩⟩
    rw [Finset.card_erase_of_mem hp2, Finset.card_erase_of_mem hp1,
      Finset.card_product, hSA, hSB]
  have hmain : (({x, x + m, x + s, x + s + m} : Finset ℤ).powerset.filter
        (shiftFree2 m s)).card ≤
      (((({∅, {x}, {x + m}} : Finset (Finset ℤ)) ×ˢ
          ({∅, {x + s}, {x + s + m}} : Finset (Finset ℤ))).erase
        (({x}, {x + s}) : Finset ℤ × Finset ℤ)).erase
        (({x + m}, {x + s + m}) : Finset ℤ × Finset ℤ)).card := by
    refine Finset.card_le_card_of_injOn
      (fun t => (t ∩ {x, x + m}, t ∩ {x + s, x + s + m})) ?_ ?_
    · intro t ht
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset] at ht
      obtain ⟨htQ, hsf⟩ := ht
      have htA : t ∩ {x, x + m} ∈
          ({∅, {x}, {x + m}} : Finset (Finset ℤ)) :=
        hA (Finset.mem_filter.mpr
          ⟨Finset.mem_powerset.mpr Finset.inter_subset_right,
            hsf.mono Finset.inter_subset_left⟩)
      have htB : t ∩ {x + s, x + s + m} ∈
          ({∅, {x + s}, {x + s + m}} : Finset (Finset ℤ)) :=
        hB (Finset.mem_filter.mpr
          ⟨Finset.mem_powerset.mpr Finset.inter_subset_right,
            hsf.mono Finset.inter_subset_left⟩)
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr ⟨?_, ?_⟩⟩
      · intro h
        have e1 : t ∩ {x, x + m} = {x + m} := congrArg Prod.fst h
        have e2 : t ∩ {x + s, x + s + m} = {x + s + m} :=
          congrArg Prod.snd h
        have hxm : x + m ∈ t :=
          (Finset.mem_inter.mp (e1.symm ▸ Finset.mem_singleton_self _)).1
        have hxsm : x + s + m ∈ t :=
          (Finset.mem_inter.mp (e2.symm ▸ Finset.mem_singleton_self _)).1
        have e : x + m + s = x + s + m := by ring
        rw [← e] at hxsm
        exact hsf.2 (x + m) hxm hxsm
      · intro h
        have e1 : t ∩ {x, x + m} = {x} := congrArg Prod.fst h
        have e2 : t ∩ {x + s, x + s + m} = {x + s} := congrArg Prod.snd h
        have hx : x ∈ t :=
          (Finset.mem_inter.mp (e1.symm ▸ Finset.mem_singleton_self _)).1
        have hxs : x + s ∈ t :=
          (Finset.mem_inter.mp (e2.symm ▸ Finset.mem_singleton_self _)).1
        exact hsf.2 x hx hxs
      · exact Finset.mem_product.mpr ⟨htA, htB⟩
    · intro t ht u hu h
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset] at ht hu
      have e1 : t ∩ {x, x + m} = u ∩ {x, x + m} := congrArg Prod.fst h
      have e2 : t ∩ {x + s, x + s + m} = u ∩ {x + s, x + s + m} :=
        congrArg Prod.snd h
      calc t = t ∩ {x, x + m} ∪ t ∩ {x + s, x + s + m} := by
            rw [← Finset.inter_union_distrib_left,
              Finset.inter_eq_left.mpr (ht.1.trans hQ)]
        _ = u ∩ {x, x + m} ∪ u ∩ {x + s, x + s + m} := by rw [e1, e2]
        _ = u := by
            rw [← Finset.inter_union_distrib_left,
              Finset.inter_eq_left.mpr (hu.1.trans hQ)]
  exact hmain.trans (le_of_eq h7)

/-- **Single-column bound.**  `Icc a (a + s - 1)` is covered by the `s - m`
disjoint `m`-pairs `{x, x + m}` (`x ∈ Icc a (a + s - m - 1)`) plus the
`2m - s` leftover singles `Icc (a + s - m) (a + m - 1)`, giving
`3^(s-m) · 2^(2m-s)`. -/
theorem card_powerset_filter_shiftFree2_col_le {n : ℕ} {m s a : ℤ}
    (hm : 1 ≤ m) (hms : m < s) :
    ((Finset.Icc a (a + s - 1)).powerset.filter (shiftFree2 m s)).card ≤
      3 ^ (s - m).toNat * 2 ^ (2 * m - s).toNat := by
  have hcov : Finset.Icc a (a + s - 1) ⊆
      (Finset.Icc a (a + s - m - 1) ∪ Finset.Icc (a + m) (a + s - 1)) ∪
        Finset.Icc (a + s - m) (a + m - 1) := by
    intro z hz
    rw [Finset.mem_Icc] at hz
    simp only [Finset.mem_union, Finset.mem_Icc]
    omega
  have hT1 : ((Finset.Icc a (a + s - m - 1) ∪
        Finset.Icc (a + m) (a + s - 1)).powerset.filter
        (shiftFree2 m s)).card ≤ 3 ^ (s - m).toNat := by
    have hc1 : Finset.Icc a (a + s - m - 1) ∪
        Finset.Icc (a + m) (a + s - 1) ⊆
        (Finset.Icc a (a + s - m - 1)).biUnion (fun x => {x, x + m}) := by
      intro z hz
      rw [Finset.mem_union, Finset.mem_Icc, Finset.mem_Icc] at hz
      rw [Finset.mem_biUnion]
      rcases hz with h | h
      · exact ⟨z, Finset.mem_Icc.mpr h, Finset.mem_insert_self _ _⟩
      · exact ⟨z - m, Finset.mem_Icc.mpr ⟨by omega, by omega⟩,
          Finset.mem_insert_of_mem (Finset.mem_singleton.mpr (by ring))⟩
    calc ((Finset.Icc a (a + s - m - 1) ∪
            Finset.Icc (a + m) (a + s - 1)).powerset.filter
          (shiftFree2 m s)).card
        ≤ ∏ x ∈ Finset.Icc a (a + s - m - 1),
            (({x, x + m} : Finset ℤ).powerset.filter
              (shiftFree2 m s)).card :=
          card_powerset_filter_shiftFree2_le_prod _ _ _ hc1
      _ ≤ ∏ x ∈ Finset.Icc a (a + s - m - 1), 3 :=
          Finset.prod_le_prod fun x _ =>
            card_powerset_filter_shiftFree2_pair_le (Or.inl rfl)
      _ = 3 ^ (s - m).toNat := by
          rw [Finset.prod_const, Int.card_Icc]
          congr 1
          omega
  have hT2 : ((Finset.Icc (a + s - m) (a + m - 1)).powerset.filter
        (shiftFree2 m s)).card ≤ 2 ^ (2 * m - s).toNat := by
    calc ((Finset.Icc (a + s - m) (a + m - 1)).powerset.filter
            (shiftFree2 m s)).card
        ≤ (Finset.Icc (a + s - m) (a + m - 1)).powerset.card :=
          Finset.card_le_card (Finset.filter_subset _ _)
      _ = 2 ^ (Finset.Icc (a + s - m) (a + m - 1)).card :=
          Finset.card_powerset _
      _ = 2 ^ (2 * m - s).toNat := by
          rw [Int.card_Icc]
          congr 1
          omega
  exact (card_powerset_filter_shiftFree2_le_mul hcov).trans
    (Nat.mul_le_mul hT1 hT2)

/-- **Double-column bound.**  `Icc a (a + 2*s - 1)` is covered by the
`s - m` quad blocks `Q_x = {x, x+m, x+s, x+s+m}` (each contributing `7`)
plus the `2m - s` leftover `s`-pairs `{y, y+s}`
(`y ∈ Icc (a+s-m) (a+m-1)`, each contributing `3`), giving
`7^(s-m) · 3^(2m-s)`. -/
theorem card_powerset_filter_shiftFree2_colPair_le {n : ℕ} {m s a : ℤ}
    (hm : 1 ≤ m) (hms : m < s) :
    ((Finset.Icc a (a + 2 * s - 1)).powerset.filter (shiftFree2 m s)).card ≤
      7 ^ (s - m).toNat * 3 ^ (2 * m - s).toNat := by
  have hcov : Finset.Icc a (a + 2 * s - 1) ⊆
      (Finset.Icc a (a + s - m - 1) ∪
        (Finset.Icc (a + m) (a + s - 1) ∪
          (Finset.Icc (a + s) (a + 2 * s - m - 1) ∪
            Finset.Icc (a + m + s) (a + 2 * s - 1)))) ∪
      (Finset.Icc (a + s - m) (a + m - 1) ∪
        Finset.Icc (a + 2 * s - m) (a + m + s - 1)) := by
    intro z hz
    rw [Finset.mem_Icc] at hz
    simp only [Finset.mem_union, Finset.mem_Icc]
    omega
  have hT1 : ((Finset.Icc a (a + s - m - 1) ∪
        (Finset.Icc (a + m) (a + s - 1) ∪
          (Finset.Icc (a + s) (a + 2 * s - m - 1) ∪
            Finset.Icc (a + m + s) (a + 2 * s - 1)))).powerset.filter
        (shiftFree2 m s)).card ≤ 7 ^ (s - m).toNat := by
    have hc1 : Finset.Icc a (a + s - m - 1) ∪
        (Finset.Icc (a + m) (a + s - 1) ∪
          (Finset.Icc (a + s) (a + 2 * s - m - 1) ∪
            Finset.Icc (a + m + s) (a + 2 * s - 1))) ⊆
        (Finset.Icc a (a + s - m - 1)).biUnion
          (fun x => {x, x + m, x + s, x + s + m}) := by
      intro z hz
      simp only [Finset.mem_union, Finset.mem_Icc] at hz
      rw [Finset.mem_biUnion]
      rcases hz with h | h | h | h
      · exact ⟨z, Finset.mem_Icc.mpr h, Finset.mem_insert_self _ _⟩
      · refine ⟨z - m, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
        exact Finset.mem_insert.mpr (Or.inr
          (Finset.mem_insert.mpr (Or.inl (by ring))))
      · refine ⟨z - s, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
        exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr
          (Or.inr (Finset.mem_insert.mpr (Or.inl (by ring))))))
      · refine ⟨z - s - m, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
        exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr
          (Or.inr (Finset.mem_insert.mpr
            (Or.inr (Finset.mem_singleton.mpr (by ring)))))))
    calc ((Finset.Icc a (a + s - m - 1) ∪
            (Finset.Icc (a + m) (a + s - 1) ∪
              (Finset.Icc (a + s) (a + 2 * s - m - 1) ∪
                Finset.Icc (a + m + s) (a + 2 * s - 1)))).powerset.filter
          (shiftFree2 m s)).card
        ≤ ∏ x ∈ Finset.Icc a (a + s - m - 1),
            (({x, x + m, x + s, x + s + m} : Finset ℤ).powerset.filter
              (shiftFree2 m s)).card :=
          card_powerset_filter_shiftFree2_le_prod _ _ _ hc1
      _ ≤ ∏ x ∈ Finset.Icc a (a + s - m - 1), 7 :=
          Finset.prod_le_prod fun x _ =>
            card_powerset_filter_shiftFree2_quad_le hm hms
      _ = 7 ^ (s - m).toNat := by
          rw [Finset.prod_const, Int.card_Icc]
          congr 1
          omega
  have hT2 : ((Finset.Icc (a + s - m) (a + m - 1) ∪
        Finset.Icc (a + 2 * s - m) (a + m + s - 1)).powerset.filter
        (shiftFree2 m s)).card ≤ 3 ^ (2 * m - s).toNat := by
    have hc2 : Finset.Icc (a + s - m) (a + m - 1) ∪
        Finset.Icc (a + 2 * s - m) (a + m + s - 1) ⊆
        (Finset.Icc (a + s - m) (a + m - 1)).biUnion
          (fun y => {y, y + s}) := by
      intro z hz
      rw [Finset.mem_union, Finset.mem_Icc, Finset.mem_Icc] at hz
      rw [Finset.mem_biUnion]
      rcases hz with h | h
      · exact ⟨z, Finset.mem_Icc.mpr h, Finset.mem_insert_self _ _⟩
      · exact ⟨z - s, Finset.mem_Icc.mpr ⟨by omega, by omega⟩,
          Finset.mem_insert_of_mem (Finset.mem_singleton.mpr (by ring))⟩
    calc ((Finset.Icc (a + s - m) (a + m - 1) ∪
            Finset.Icc (a + 2 * s - m) (a + m + s - 1)).powerset.filter
          (shiftFree2 m s)).card
        ≤ ∏ y ∈ Finset.Icc (a + s - m) (a + m - 1),
            (({y, y + s} : Finset ℤ).powerset.filter
              (shiftFree2 m s)).card :=
          card_powerset_filter_shiftFree2_le_prod _ _ _ hc2
      _ ≤ ∏ y ∈ Finset.Icc (a + s - m) (a + m - 1), 3 :=
          Finset.prod_le_prod fun y _ =>
            card_powerset_filter_shiftFree2_pair_le (Or.inr rfl)
      _ = 3 ^ (2 * m - s).toNat := by
          rw [Finset.prod_const, Int.card_Icc]
          congr 1
          omega
  exact (card_powerset_filter_shiftFree2_le_mul hcov).trans
    (Nat.mul_le_mul hT1 hT2)

/-- **Assembled bound.**  `Icc (s + 1) n` is covered by `K` consecutive
double columns `Icc (s + 1 + 2*s*j) (s + 1 + 2*s*j + 2*s - 1)` for
`j ∈ range K`, each contributing `7^(s-m) · 3^(2m-s)`. -/
theorem card_powerset_filter_shiftFree2_Icc_le_colBlocks {n : ℕ} {m s : ℤ}
    (hm : 1 ≤ m) (hms : m < s) (K : ℕ)
    (hK : (n : ℤ) ≤ s + 2 * s * (K : ℤ)) :
    ((Finset.Icc (s + 1) (n : ℤ)).powerset.filter (shiftFree2 m s)).card ≤
      (7 ^ (s - m).toNat * 3 ^ (2 * m - s).toNat) ^ K := by
  have hs2 : (0 : ℤ) < 2 * s := by omega
  have hcov : Finset.Icc (s + 1) (n : ℤ) ⊆ (Finset.range K).biUnion
      (fun j : ℕ => Finset.Icc (s + 1 + 2 * s * (j : ℤ))
        (s + 1 + 2 * s * (j : ℤ) + 2 * s - 1)) := by
    intro z hz
    rw [Finset.mem_Icc] at hz
    rw [Finset.mem_biUnion]
    set w := z - s - 1 with hw
    have hw0 : 0 ≤ w := by omega
    have hwn : w ≤ (n : ℤ) - s - 1 := by omega
    have hj0 : 0 ≤ w / (2 * s) := Int.ediv_nonneg hw0 hs2.le
    have hje : w / (2 * s) * (2 * s) ≤ w :=
      Int.ediv_mul_le w (by omega : (2 * s) ≠ 0)
    have hlt : w / (2 * s) < (K : ℤ) := by
      by_contra hcon
      have hle : (K : ℤ) * (2 * s) ≤ w / (2 * s) * (2 * s) :=
        mul_le_mul_of_nonneg_right (not_lt.mp hcon) hs2.le
      have hK2 : (K : ℤ) * (2 * s) = 2 * s * (K : ℤ) := by ring
      omega
    refine ⟨(w / (2 * s)).toNat, ?_, ?_⟩
    · rw [Finset.mem_range, Int.toNat_lt hj0,
        Int.ediv_lt_iff_lt_mul hs2, mul_comm ((K : ℤ)) (2 * s)]
      omega
    · rw [Finset.mem_Icc]
      have hjz : (((w / (2 * s)).toNat : ℕ) : ℤ) = w / (2 * s) :=
        Int.toNat_of_nonneg hj0
      rw [hjz]
      have hmod : w = 2 * s * (w / (2 * s)) + w % (2 * s) :=
        (Int.mul_ediv_add_emod w (2 * s)).symm
      have hmod0 : 0 ≤ w % (2 * s) := Int.emod_nonneg _ (by omega)
      have hmodlt : w % (2 * s) < 2 * s := Int.emod_lt_of_pos _ hs2
      constructor <;> omega
  calc ((Finset.Icc (s + 1) (n : ℤ)).powerset.filter (shiftFree2 m s)).card
      ≤ ∏ j ∈ Finset.range K,
          ((Finset.Icc (s + 1 + 2 * s * (j : ℤ))
            (s + 1 + 2 * s * (j : ℤ) + 2 * s - 1)).powerset.filter
            (shiftFree2 m s)).card :=
        card_powerset_filter_shiftFree2_le_prod _ _ _ hcov
    _ ≤ ∏ j ∈ Finset.range K,
          (7 ^ (s - m).toNat * 3 ^ (2 * m - s).toNat) :=
        Finset.prod_le_prod fun j _ =>
          card_powerset_filter_shiftFree2_colPair_le (n := n) hm hms
    _ = (7 ^ (s - m).toNat * 3 ^ (2 * m - s).toNat) ^ K := by
        rw [Finset.prod_const, Finset.card_range]

end JSP000728
