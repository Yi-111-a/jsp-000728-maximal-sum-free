import JSPProblem.ContainerReduction
import JSPProblem.MaxCard
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# JSP-000728 — the removal lemma and the container/fingerprint hypotheses

This file decomposes the remaining mathematical gap in the BLST18 upper bound
`f(n) ≤ 2 ^ ((1/4 + o(1)) · n)` into two named hypotheses and proves the
conditional implications.

* `SchurRemoval` — the *arithmetic removal lemma* (Green; Ruzsa–Szemerédi
  style): a subset of `{1,…,n}` containing at most `δ n²` Schur triples can be
  made sum-free by deleting at most `ε n` elements.
* `ContainerExistence` — the Green / Balogh–Morris–Samotij container lemma:
  eventually there is a family `F` of containers covering all sum-free subsets
  of `{1,…,n}` with `F.card ≤ 2^{ε n}` and each `C ∈ F` containing at most
  `δ n²` Schur triples.
* `eventualRatioUpper_half_of_removal_containers` — the two hypotheses above
  already give `f(n) ≤ 2^{(1/2 + o(1)) n}`, i.e. `EventualRatioUpper (1/2)`:
  each container splits as `C = T ∪ (C ∖ T)` with `T` sum-free (hence
  `2 * T.card ≤ n + 1` by `two_mul_card_le_of_isSumFree`) and
  `(C ∖ T).card ≤ (ε/4) · n`, so `C.card ≤ (n+1)/2 + (ε/4) · n` and the
  counting `f(n) ≤ F.card · 2^{C.card}` of `sumFreeCount_le_of_good` applies.
* `FingerprintBound` — the sharp BLST18 per-container maximal-set count: each
  container houses at most `2^{(1/4 + ε) n}` maximal sum-free sets.
* `maxContainerBound_of_containerExistence_fingerprint` — container existence
  plus the fingerprint bound directly yields the `MaxContainerBound`
  hypothesis of `ContainerReduction.lean` (the removal lemma is *not* needed
  here, since the containers cover the maximal sets themselves).
* `sharpAsymptotic_of_containerExistence_fingerprint` — the conditional
  BLST18 headline `log₂ f(n) / n → 1/4`.

All hypotheses are honest unproven `Prop`s; every implication in this file is
fully proved.
-/

namespace JSP000728

/-- **Schur removal lemma** (hypothesis): for every `ε > 0` there is a
`δ > 0` such that, eventually, every `s ⊆ {1,…,n}` with at most `δ n²` Schur
triples contains a sum-free subset `t` obtained by deleting at most `ε n`
elements. -/
def SchurRemoval : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n : ℕ in Filter.atTop,
    ∀ s : Finset ℤ, s ⊆ interval n → (schurTripleCount s : ℝ) ≤ δ * (n : ℝ) ^ 2 →
      ∃ t : Finset ℤ, t ⊆ s ∧ IsSumFree t ∧ ((s \ t).card : ℝ) ≤ ε * (n : ℝ)

/-- **Container existence** (hypothesis): the Green/BMS container lemma.  For
every `ε, δ > 0`, eventually there is a container family `F` for `{1,…,n}`
with `F.card ≤ 2^{ε n}` such that every container contains at most `δ n²`
Schur triples. -/
def ContainerExistence : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in Filter.atTop,
    ∃ F : Finset (Finset ℤ), IsContainerFamily n F ∧
      (F.card : ℝ) ≤ 2 ^ (ε * (n : ℝ)) ∧
      ∀ C ∈ F, (schurTripleCount C : ℝ) ≤ δ * (n : ℝ) ^ 2

/-- **Conditional constant-`1/2` bound.**  Container existence plus the Schur
removal lemma give `f(n) ≤ 2^{(1/2 + o(1)) n}`.

Proof sketch: fix `ε > 0` and take `δ` from `SchurRemoval (ε/4)`.  Applying
`ContainerExistence (ε/4) δ` yields, eventually, a family `F` with
`F.card ≤ 2^{(ε/4) n}` whose members each contain at most `δ n²` Schur
triples.  Removing at most `(ε/4) n` elements of a container `C` leaves a
sum-free `T ⊆ {1,…,n}`, so `2 * T.card ≤ n + 1` and hence
`C.card ≤ (n + 1)/2 + (ε/4) n`.  The family is therefore a good container
family with `K = ⌈(n+1)/2 + (ε/4) n⌉₊`, giving
`f(n) ≤ 2^{(ε/4) n} · 2^{(1/2 + ε/4) n + O(1)}`, i.e.
`log₂ f(n)/n ≤ 1/2 + ε` once `n ≥ 3/ε`. -/
theorem eventualRatioUpper_half_of_removal_containers
    (hCE : ContainerExistence) (hSR : SchurRemoval) :
    EventualRatioUpper (1 / 2) := by
  intro ε hε
  have hε4 : 0 < ε / 4 := by linarith
  obtain ⟨δ, hδ, hrem⟩ := hSR (ε / 4) hε4
  have hcont := hCE (ε / 4) hε4 δ hδ
  filter_upwards [hrem, hcont, Filter.eventually_ge_atTop ⌈3 / ε⌉₊]
    with n hremn hcontn hnN
  obtain ⟨F, hFfam, hFcard, hFtr⟩ := hcontn
  have hnR : (0 : ℝ) < (n : ℝ) := by
    have hNpos : 0 < ⌈3 / ε⌉₊ := Nat.ceil_pos.mpr (by positivity)
    exact_mod_cast hNpos.trans_le hnN
  -- The size cap on containers: `K = ⌈(n+1)/2 + (ε/4) n⌉₊`.
  set x : ℝ := ((n : ℝ) + 1) / 2 + (ε / 4) * (n : ℝ) with hx
  set K : ℕ := ⌈x⌉₊ with hK
  have hxnonneg : 0 ≤ x := by
    rw [hx]
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    exact add_nonneg (by linarith) (mul_nonneg (by linarith) hn0)
  have hgood : IsGoodContainerFamily n F K := by
    refine ⟨hFfam, fun C hC => ?_⟩
    obtain ⟨t, htC, htf, hsd⟩ := hremn C (hFfam.1 C hC) (hFtr C hC)
    have htI : t ⊆ interval n := htC.trans (hFfam.1 C hC)
    have h2t : (2 : ℝ) * (t.card : ℝ) ≤ (n : ℝ) + 1 := by
      exact_mod_cast two_mul_card_le_of_isSumFree htI htf
    have hsplit : (C.card : ℝ) ≤ (t.card : ℝ) + ((C \ t).card : ℝ) := by
      have h := Finset.card_union_le t (C \ t)
      rw [Finset.union_sdiff_of_subset htC] at h
      exact_mod_cast h
    have hCx : (C.card : ℝ) ≤ x := by rw [hx]; linarith
    exact Nat.cast_le.mp (hCx.trans (Nat.le_ceil x))
  have hcountℕ : maxSumFreeCount n ≤ F.card * 2 ^ K :=
    maxSumFreeCount_le_of_good hgood
  have h2pos : (0 : ℝ) < 2 := by norm_num
  -- Real-valued count: `f(n) ≤ 2^{(ε/4) n} · 2^{x + 1}`.
  have hcount : (maxSumFreeCount n : ℝ) ≤ (F.card : ℝ) * (2 : ℝ) ^ (K : ℝ) := by
    calc (maxSumFreeCount n : ℝ)
        ≤ (F.card : ℝ) * (2 : ℝ) ^ (K : ℕ) := by exact_mod_cast hcountℕ
      _ = (F.card : ℝ) * (2 : ℝ) ^ (K : ℝ) := by rw [Real.rpow_natCast]
  have hKle : (K : ℝ) ≤ x + 1 := (Nat.ceil_lt_add_one hxnonneg).le
  have hpow : (2 : ℝ) ^ (K : ℝ) ≤ (2 : ℝ) ^ (x + 1) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hKle
  have hmul : (F.card : ℝ) * (2 : ℝ) ^ (K : ℝ) ≤
      (2 : ℝ) ^ ((ε / 4) * (n : ℝ)) * (2 : ℝ) ^ (x + 1) :=
    mul_le_mul hFcard hpow (Real.rpow_nonneg h2pos.le _)
      (Real.rpow_nonneg h2pos.le _)
  have hexp : (ε / 4) * (n : ℝ) + (x + 1) =
      (1 / 2 + ε / 2) * (n : ℝ) + 3 / 2 := by
    rw [hx]; ring
  have hbound : (maxSumFreeCount n : ℝ) ≤
      (2 : ℝ) ^ ((1 / 2 + ε / 2) * (n : ℝ) + 3 / 2) := by
    calc (maxSumFreeCount n : ℝ)
        ≤ (2 : ℝ) ^ ((ε / 4) * (n : ℝ)) * (2 : ℝ) ^ (x + 1) :=
          hcount.trans hmul
      _ = (2 : ℝ) ^ ((ε / 4) * (n : ℝ) + (x + 1)) := by
          rw [← Real.rpow_add h2pos]
      _ = (2 : ℝ) ^ ((1 / 2 + ε / 2) * (n : ℝ) + 3 / 2) := by rw [hexp]
  -- Take `log₂` and divide by `n ≥ 3/ε`.
  have hpos : (0 : ℝ) < (maxSumFreeCount n : ℝ) := by
    exact_mod_cast maxSumFreeCount_pos n
  have hlog : Real.logb 2 (maxSumFreeCount n : ℝ) ≤
      (1 / 2 + ε / 2) * (n : ℝ) + 3 / 2 := by
    calc Real.logb 2 (maxSumFreeCount n : ℝ)
        ≤ Real.logb 2 ((2 : ℝ) ^ ((1 / 2 + ε / 2) * (n : ℝ) + 3 / 2)) :=
          (Real.logb_le_logb (by norm_num) hpos
            (Real.rpow_pos_of_pos h2pos _)).mpr hbound
      _ = (1 / 2 + ε / 2) * (n : ℝ) + 3 / 2 :=
          Real.logb_rpow h2pos (by norm_num : (2 : ℝ) ≠ 1)
  have htail : (3 / 2) / (n : ℝ) ≤ ε / 2 := by
    have hn3 : (3 : ℝ) / ε ≤ (n : ℝ) :=
      (Nat.le_ceil _).trans (Nat.cast_le.mpr hnN)
    have h3 : (3 : ℝ) ≤ (n : ℝ) * ε := (div_le_iff₀ hε).mp hn3
    rw [div_le_iff₀ hnR]
    have heq : (ε / 2) * (n : ℝ) = (n : ℝ) * ε / 2 := by ring
    rw [heq]; linarith
  calc Real.logb 2 (maxSumFreeCount n : ℝ) / (n : ℝ)
      ≤ ((1 / 2 + ε / 2) * (n : ℝ) + 3 / 2) / (n : ℝ) :=
        div_le_div_of_nonneg_right hlog hnR.le
    _ = (1 / 2 + ε / 2) + (3 / 2) / (n : ℝ) := by
        rw [add_div, mul_div_cancel_right₀ _ hnR.ne']
    _ ≤ 1 / 2 + ε := by linarith [htail]

/-- **Fingerprint bound** (hypothesis): the BLST18 per-container maximal-set
count.  For every `ε > 0`, eventually every `C ⊆ {1,…,n}` houses at most
`2^{(1/4 + ε) n}` maximal sum-free sets. -/
def FingerprintBound : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in Filter.atTop,
    ∀ C : Finset ℤ, C ⊆ interval n →
      (((maxSumFreeSets n).filter (· ⊆ C)).card : ℝ) ≤
        2 ^ ((1 / 4 + ε) * (n : ℝ))

/-- **Container existence + fingerprint bound ⇒ `MaxContainerBound`.**  The
container family already covers every maximal sum-free set (each is itself a
sum-free subset of `{1,…,n}`), and the fingerprint bound caps the per-container
count; the removal lemma is not needed at this level. -/
theorem maxContainerBound_of_containerExistence_fingerprint
    (hCE : ContainerExistence) (hFB : FingerprintBound) :
    MaxContainerBound := by
  intro ε hε
  filter_upwards [hCE ε hε 1 (by norm_num : (0 : ℝ) < 1), hFB ε hε]
    with n hcont hfp
  obtain ⟨F, hFfam, hFcard, -⟩ := hcont
  refine ⟨F, hFcard, fun M hM => ?_, fun C hC => hfp C (hFfam.1 C hC)⟩
  obtain ⟨hsub, hsf, -⟩ := mem_maxSumFreeSets.mp hM
  exact hFfam.2 M hsub hsf

/-- **Conditional BLST18 headline.**  Container existence plus the
fingerprint bound imply `log₂ f(n) / n → 1/4`. -/
theorem sharpAsymptotic_of_containerExistence_fingerprint
    (hCE : ContainerExistence) (hFB : FingerprintBound) : SharpAsymptotic :=
  sharpAsymptotic_of_maxContainerBound
    (maxContainerBound_of_containerExistence_fingerprint hCE hFB)

end JSP000728
