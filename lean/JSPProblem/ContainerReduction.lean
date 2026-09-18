import JSPProblem.AsymptoticReduction
import JSPProblem.Containers
import JSPProblem.BlstCounting

/-!
# JSP-000728 — the container hypothesis implies the sharp asymptotic

This file closes the last step of the BLST18 reduction *conditionally*.  The
hard mathematical input of Balogh–Liu–Sharifzadeh–Treglown (the Green/BMS
container lemma together with the BLST18 fingerprint counting) is packaged as
the hypothesis `MaxContainerBound`: for every `ε > 0`, eventually there is a
family `F` of containers covering all maximal sum-free subsets of `{1,…,n}`,
with exponentially few containers (`F.card ≤ 2 ^ (ε n)`) each housing at most
`2 ^ ((1/4 + ε) n)` maximal sum-free sets.

From that hypothesis we derive, by pure counting and real-analysis glue,

* `maxSumFreeCount_le_of_containerCover` — a cover by `F.card` containers each
  housing at most `B` maximal sum-free sets forces `f(n) ≤ F.card · B`;
* `eventualRatioUpper_of_maxContainerBound` — `f(n) ≤ 2^{ε n} · 2^{(1/4+ε)n}
  = 2^{(1/4 + 2ε) n}`, so `log₂ f(n)/n ≤ 1/4 + 2ε` eventually;
* `sharpAsymptotic_of_maxContainerBound` — the BLST18 headline
  `log₂ f(n)/n → 1/4`, via `sharpAsymptotic_of_eventualRatioUpper`.

No new mathematics is proved here: this is the Filters/`Real.logb`/`Real.rpow`
glue that turns the per-container counting hypothesis into the asymptotic.
-/

namespace JSP000728

/-- BLST18 container-method hypothesis, packaged at the level of maximal
sum-free sets: for every ε > 0, eventually there is a family F of containers
covering all maximal sum-free subsets of {1,…,n}, with exponentially few
containers (≤ 2^{ε n}) each housing at most 2^{(1/4 + ε) n} maximal sum-free
sets. This is the precise content of Green's container lemma + the BLST18
fingerprint counting, stated as a hypothesis. -/
def MaxContainerBound : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in Filter.atTop,
    ∃ F : Finset (Finset ℤ),
      (F.card : ℝ) ≤ 2 ^ (ε * (n : ℝ)) ∧
      (∀ M ∈ maxSumFreeSets n, ∃ C ∈ F, M ⊆ C) ∧
      ∀ C ∈ F, (((maxSumFreeSets n).filter (· ⊆ C)).card : ℝ) ≤
        2 ^ ((1/4 + ε) * (n : ℝ))

/-- **Counting at a fixed `n`.**  If every maximal sum-free `M ⊆ {1,…,n}` is
contained in some container `C ∈ F`, and each `C ∈ F` houses at most `B`
maximal sum-free sets, then `f(n) ≤ F.card · B`.

The proof covers `maxSumFreeSets n` by the union over `C ∈ F` of the maximal
sum-free sets contained in `C`; the counting is kept in `ℕ` until the final
sum bound, which is evaluated in `ℝ`. -/
theorem maxSumFreeCount_le_of_containerCover {n : ℕ} {F : Finset (Finset ℤ)}
    {B : ℝ} (hcov : ∀ M ∈ maxSumFreeSets n, ∃ C ∈ F, M ⊆ C)
    (hB : ∀ C ∈ F,
      (((maxSumFreeSets n).filter (· ⊆ C)).card : ℝ) ≤ B) :
    (maxSumFreeCount n : ℝ) ≤ F.card * B := by
  classical
  have hsub : maxSumFreeSets n ⊆
      F.biUnion fun C => (maxSumFreeSets n).filter (· ⊆ C) := by
    intro M hM
    obtain ⟨C, hCF, hMC⟩ := hcov M hM
    rw [Finset.mem_biUnion]
    exact ⟨C, hCF, Finset.mem_filter.mpr ⟨hM, hMC⟩⟩
  have hnat : maxSumFreeCount n ≤
      ∑ C ∈ F, ((maxSumFreeSets n).filter (· ⊆ C)).card :=
    (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  have hreal : (maxSumFreeCount n : ℝ) ≤
      ∑ C ∈ F, (((maxSumFreeSets n).filter (· ⊆ C)).card : ℝ) := by
    exact_mod_cast hnat
  calc (maxSumFreeCount n : ℝ)
      ≤ ∑ C ∈ F, (((maxSumFreeSets n).filter (· ⊆ C)).card : ℝ) := hreal
    _ ≤ ∑ _C ∈ F, B := Finset.sum_le_sum fun C hC => hB C hC
    _ = (F.card : ℝ) * B := by rw [Finset.sum_const, nsmul_eq_mul]

/-- **The container hypothesis implies the missing upper bound.**  Applying
`MaxContainerBound` at `ε = δ/2` gives, eventually,
`f(n) ≤ 2^{(δ/2) n} · 2^{(1/4 + δ/2) n} = 2^{(1/4 + δ) n}`; taking `log₂`
and dividing by the (eventually positive) `n` yields
`log₂ f(n)/n ≤ 1/4 + δ`. -/
theorem eventualRatioUpper_of_maxContainerBound (h : MaxContainerBound) :
    EventualRatioUpper (1 / 4) := by
  intro δ hδ
  have hδ2 : 0 < δ / 2 := by linarith
  have hb : (1 : ℝ) < 2 := by norm_num
  have h2pos : (0 : ℝ) < 2 := by norm_num
  filter_upwards [h (δ / 2) hδ2, Filter.eventually_ge_atTop 1] with n hn hn1
  obtain ⟨F, hFcard, hcov, hper⟩ := hn
  have hcount := maxSumFreeCount_le_of_containerCover hcov hper
  have hfact : (F.card : ℝ) * (2 : ℝ) ^ ((1 / 4 + δ / 2) * (n : ℝ)) ≤
      (2 : ℝ) ^ (δ / 2 * (n : ℝ)) * (2 : ℝ) ^ ((1 / 4 + δ / 2) * (n : ℝ)) :=
    mul_le_mul hFcard le_rfl
      (Real.rpow_nonneg h2pos.le _) (Real.rpow_nonneg h2pos.le _)
  have hexp : δ / 2 * (n : ℝ) + (1 / 4 + δ / 2) * (n : ℝ) =
      (1 / 4 + δ) * (n : ℝ) := by ring
  have hbound : (maxSumFreeCount n : ℝ) ≤
      (2 : ℝ) ^ ((1 / 4 + δ) * (n : ℝ)) := by
    calc (maxSumFreeCount n : ℝ)
        ≤ (2 : ℝ) ^ (δ / 2 * (n : ℝ)) *
            (2 : ℝ) ^ ((1 / 4 + δ / 2) * (n : ℝ)) :=
          hcount.trans hfact
      _ = (2 : ℝ) ^ ((1 / 4 + δ) * (n : ℝ)) := by
          rw [← Real.rpow_add h2pos, hexp]
  have hpos : (0 : ℝ) < (maxSumFreeCount n : ℝ) := by
    exact_mod_cast maxSumFreeCount_pos n
  have hlog : Real.logb 2 (maxSumFreeCount n : ℝ) ≤ (1 / 4 + δ) * (n : ℝ) := by
    calc Real.logb 2 (maxSumFreeCount n : ℝ)
        ≤ Real.logb 2 ((2 : ℝ) ^ ((1 / 4 + δ) * (n : ℝ))) :=
          (Real.logb_le_logb hb hpos
            (Real.rpow_pos_of_pos h2pos _)).mpr hbound
      _ = (1 / 4 + δ) * (n : ℝ) :=
          Real.logb_rpow h2pos (by norm_num : (2 : ℝ) ≠ 1)
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  calc Real.logb 2 (maxSumFreeCount n : ℝ) / (n : ℝ)
      ≤ ((1 / 4 + δ) * (n : ℝ)) / (n : ℝ) :=
        div_le_div_of_nonneg_right hlog hnpos.le
    _ = 1 / 4 + δ := mul_div_cancel_right₀ _ hnpos.ne'

/-- **Conditional BLST18 headline.**  The container-method hypothesis
`MaxContainerBound` implies `SharpAsymptotic`: `log₂ f(n)/n → 1/4`. -/
theorem sharpAsymptotic_of_maxContainerBound (h : MaxContainerBound) :
    SharpAsymptotic :=
  sharpAsymptotic_of_eventualRatioUpper
    (eventualRatioUpper_of_maxContainerBound h)

end JSP000728
