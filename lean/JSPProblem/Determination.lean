import JSPProblem.Basic

/-!
# JSP-000728 — (non-)determination of maximal sum-free sets by fingerprints

This file proves that a *fixed-threshold* lower-half fingerprint does **not**
determine a maximal sum-free set, and pins down the exact boundary where
determination does hold.

* `exists_not_determined_by_lower_half` — at `n = 5` the maximal sum-free
  sets `{2,3}` and `{2,5}` share the same trace `{2}` on `{1,2}` but are
  distinct.  Fixed-threshold fingerprints therefore have fibers of size
  `≥ 2`, so they cannot be used to *count* maximal sum-free sets: the BLST
  fingerprint must instead be `M`-dependent.
* `fiber_card_le` / `fiber_card_le_two_pow` — the fiber over a lower-half
  fingerprint `S` injects into the powerset of the upper interval
  `{k+1,…,n}`, hence has size at most `2 ^ (n - k)`.
* `determined_by_all_but_last` — at the boundary `k = n - 1` determination
  *does* hold: two maximal sum-free sets of `{1,…,n}` agreeing on
  `{1,…,n-1}` are equal.  Determination is thus a boundary phenomenon.
-/

namespace JSP000728

/-- A subset of `{1,…,n}` splits at any threshold `k` into its lower trace
on `{1,…,k}` and its upper trace on `{k+1,…,n}`. -/
theorem inter_Icc_union_inter_Ioc {n : ℕ} {M : Finset ℤ}
    (hM : M ⊆ interval n) (k : ℕ) :
    M ∩ Finset.Icc 1 (k : ℤ) ∪ M ∩ Finset.Ioc (k : ℤ) (n : ℤ) = M := by
  ext x
  simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_Icc,
    Finset.mem_Ioc]
  constructor
  · rintro (⟨hxM, -, -⟩ | ⟨hxM, -, -⟩) <;> exact hxM
  · intro hxM
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp (hM hxM)
    by_cases hxk : x ≤ (k : ℤ)
    · exact Or.inl ⟨hxM, h1, hxk⟩
    · exact Or.inr ⟨hxM, not_le.mp hxk, h2⟩

/-- **The fingerprint obstruction.**  There is an instance where the
lower-half fingerprint does not determine the maximal sum-free set: at
`n = 5`, `k = 2 = ⌊n/2⌋`, the sets `{2,3}` and `{2,5}` are distinct
maximal sum-free sets whose traces on `{1,2}` coincide (both are `{2}`). -/
theorem exists_not_determined_by_lower_half :
    ∃ n k : ℕ, n / 2 ≤ k ∧ k < n ∧
      ∃ M₁ M₂ : Finset ℤ, M₁ ∈ maxSumFreeSets n ∧ M₂ ∈ maxSumFreeSets n ∧
        M₁ ≠ M₂ ∧
          M₁ ∩ Finset.Icc 1 (k : ℤ) = M₂ ∩ Finset.Icc 1 (k : ℤ) :=
  ⟨5, 2, by decide, by decide,
    {2, 3}, {2, 5}, by decide, by decide, by decide, by decide⟩

/-- **Fiber bound.**  The maximal sum-free sets of `{1,…,n}` extending a
fixed lower-half fingerprint `S` on `{1,…,k}` are determined by their upper
traces, so their number is at most `2 ^ |{k+1,…,n}|`. -/
theorem fiber_card_le (n k : ℕ) (S : Finset ℤ) :
    ((maxSumFreeSets n).filter
      fun M => M ∩ Finset.Icc 1 (k : ℤ) = S).card ≤
        2 ^ (Finset.Ioc (k : ℤ) (n : ℤ)).card := by
  classical
  calc ((maxSumFreeSets n).filter
        fun M => M ∩ Finset.Icc 1 (k : ℤ) = S).card
      ≤ ((Finset.Ioc (k : ℤ) (n : ℤ)).powerset).card := by
        refine Finset.card_le_card_of_injOn
          (fun M => M ∩ Finset.Ioc (k : ℤ) (n : ℤ)) ?_ ?_
        · intro M _
          exact Finset.mem_powerset.mpr Finset.inter_subset_right
        · intro M₁ hM₁ M₂ hM₂ hIoc
          rw [Finset.mem_coe, Finset.mem_filter] at hM₁ hM₂
          obtain ⟨hM₁max, hM₁fp⟩ := hM₁
          obtain ⟨hM₂max, hM₂fp⟩ := hM₂
          have hs1 :=
            inter_Icc_union_inter_Ioc (mem_maxSumFreeSets.mp hM₁max).1 k
          have hs2 :=
            inter_Icc_union_inter_Ioc (mem_maxSumFreeSets.mp hM₂max).1 k
          dsimp only at hIoc
          rw [← hs1, ← hs2, hM₁fp, hM₂fp, hIoc]
    _ = 2 ^ (Finset.Ioc (k : ℤ) (n : ℤ)).card := Finset.card_powerset _

/-- Numeric form of `fiber_card_le`: a fiber over a lower-half fingerprint
has at most `2 ^ (n - k)` elements. -/
theorem fiber_card_le_two_pow (n k : ℕ) (S : Finset ℤ) :
    ((maxSumFreeSets n).filter
      fun M => M ∩ Finset.Icc 1 (k : ℤ) = S).card ≤ 2 ^ (n - k) := by
  have hcard : (Finset.Ioc (k : ℤ) (n : ℤ)).card = n - k := by
    rw [Int.card_Ioc]
    omega
  rw [← hcard]
  exact fiber_card_le n k S

/-- **Determination at the boundary.**  Two maximal sum-free sets of
`{1,…,n}` that agree on `{1,…,n-1}` are equal: the only element left
undecided by the fingerprint is `n` itself, and maximality forces the
membership of `n` to agree.  Indeed, if `n ∈ A` but `n ∉ B`, maximality of
`B` produces `u, v ∈ insert n B` with `u + v ∈ insert n B`; positivity kills
every case except `u + v = n` with `u, v ∈ B ⊆ {1,…,n-1}`, which transfers
to `A` and contradicts sum-freeness of `A`. -/
theorem determined_by_all_but_last {n : ℕ} {M₁ M₂ : Finset ℤ}
    (h₁ : M₁ ∈ maxSumFreeSets n) (h₂ : M₂ ∈ maxSumFreeSets n)
    (h : M₁ ∩ Finset.Icc 1 ((n : ℤ) - 1) =
      M₂ ∩ Finset.Icc 1 ((n : ℤ) - 1)) :
    M₁ = M₂ := by
  obtain ⟨hsub1, hsf1, hmax1⟩ := mem_maxSumFreeSets.mp h₁
  obtain ⟨hsub2, hsf2, hmax2⟩ := mem_maxSumFreeSets.mp h₂
  -- Symmetric core: `n ∈ A` forces `n ∈ B`.
  have hsymm : ∀ {A B : Finset ℤ}, IsMaxSumFree n A → IsMaxSumFree n B →
      A ∩ Finset.Icc 1 ((n : ℤ) - 1) = B ∩ Finset.Icc 1 ((n : ℤ) - 1) →
      (n : ℤ) ∈ A → (n : ℤ) ∈ B := by
    intro A B hA hB hAB hnA
    by_contra hnB
    have hn1 : (1 : ℤ) ≤ (n : ℤ) := (Finset.mem_Icc.mp (hA.1 hnA)).1
    have hnI : (n : ℤ) ∈ interval n := Finset.mem_Icc.mpr ⟨hn1, le_refl _⟩
    have hnot : ¬ IsSumFree (insert (n : ℤ) B) := hB.2.2 _ hnI hnB
    have hex : ∃ u ∈ insert (n : ℤ) B, ∃ v ∈ insert (n : ℤ) B,
        u + v ∈ insert (n : ℤ) B := by
      unfold IsSumFree at hnot
      push Not at hnot
      exact hnot
    obtain ⟨u, hu, v, hv, huv⟩ := hex
    have hbound : ∀ w ∈ B, (1 : ℤ) ≤ w ∧ w ≤ (n : ℤ) :=
      fun w hw => Finset.mem_Icc.mp (hB.1 hw)
    have htrans : ∀ w ∈ B, w ≤ (n : ℤ) - 1 → w ∈ A := by
      intro w hwB hwle
      have hw : w ∈ B ∩ Finset.Icc 1 ((n : ℤ) - 1) :=
        Finset.mem_inter.mpr
          ⟨hwB, Finset.mem_Icc.mpr ⟨(hbound w hwB).1, hwle⟩⟩
      rw [← hAB] at hw
      exact (Finset.mem_inter.mp hw).1
    rw [Finset.mem_insert] at hu hv huv
    rcases hu with rfl | huB <;> rcases hv with rfl | hvB <;>
      rcases huv with hsum | hmem
    · omega
    · have hb := hbound _ hmem; omega
    · have hb := hbound v hvB; omega
    · have hb := hbound v hvB; have hb2 := hbound _ hmem; omega
    · have hb := hbound u huB; omega
    · have hb := hbound u huB; have hb2 := hbound _ hmem; omega
    · -- the non-degenerate obstruction: `u + v = n` with `u, v ∈ B`;
      -- both summands lie below `n`, transfer to `A`, and `u + v = n ∈ A`
      -- contradicts sum-freeness of `A`.
      have hbu := hbound u huB
      have hbv := hbound v hvB
      have huA : u ∈ A := htrans u huB (by omega)
      have hvA : v ∈ A := htrans v hvB (by omega)
      have hnA' : u + v ∈ A := by rw [hsum]; exact hnA
      exact (hA.2.1 u huA v hvA) hnA'
    · exact (hB.2.1 u huB v hvB) hmem
  ext x
  constructor
  · intro hxM1
    have hxb := Finset.mem_Icc.mp (hsub1 hxM1)
    by_cases hxsmall : x ≤ (n : ℤ) - 1
    · exact (Finset.mem_inter.mp
        (h ▸ Finset.mem_inter.mpr
          ⟨hxM1, Finset.mem_Icc.mpr ⟨hxb.1, hxsmall⟩⟩)).1
    · have hxn : x = (n : ℤ) := by omega
      subst hxn
      exact hsymm ⟨hsub1, hsf1, hmax1⟩ ⟨hsub2, hsf2, hmax2⟩ h hxM1
  · intro hxM2
    have hxb := Finset.mem_Icc.mp (hsub2 hxM2)
    by_cases hxsmall : x ≤ (n : ℤ) - 1
    · exact (Finset.mem_inter.mp
        (h.symm ▸ Finset.mem_inter.mpr
          ⟨hxM2, Finset.mem_Icc.mpr ⟨hxb.1, hxsmall⟩⟩)).1
    · have hxn : x = (n : ℤ) := by omega
      subst hxn
      exact hsymm ⟨hsub2, hsf2, hmax2⟩ ⟨hsub1, hsf1, hmax1⟩ h.symm hxM2

end JSP000728
