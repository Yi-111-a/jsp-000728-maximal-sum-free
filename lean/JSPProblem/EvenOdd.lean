import JSPProblem.Basic
import JSPProblem.Odds
import JSPProblem.Extremal
import JSPProblem.PairBound

/-!
# JSP-000728 — the even/odd parity decomposition of maximal sum-free sets

Structural input toward the BLST dichotomy (every maximal sum-free subset of
`{1,…,n}` is "near-odd" or "near-upper-half"): this file splits maximal
sum-free sets by the parity of their elements.

* `evenPartSets n`, `oddPartSets n` — the all-even / all-odd maximal sets.
* `oddPartSets_eq_singleton` — `odds n` is the unique all-odd maximal set.
* `halve` — halving an all-even set; injective on all-even finsets, and it
  preserves and reflects sum-freeness (`isSumFree_halve_iff`) and maximality
  (`halve_mem_maxSumFreeSets`).  Hence `(evenPartSets n).card ≤
  maxSumFreeCount (n / 2)`, and composing with the pair bound gives
  `(evenPartSets n).card ≤ 2 * 3 ^ ((n / 2) / 2)`.
* `mixedPartSets n`, `maxSumFreeSets_subset_union`,
  `maxSumFreeCount_le_decomp` — every maximal set is all-odd, all-even or
  mixed, so `f(n) ≤ 1 + f(n/2) + #mixed`.
-/

namespace JSP000728

/-- Maximal sum-free subsets of `{1,…,n}` all of whose elements are even. -/
def evenPartSets (n : ℕ) : Finset (Finset ℤ) :=
  (maxSumFreeSets n).filter fun M => ∀ x ∈ M, Even x

/-- Maximal sum-free subsets of `{1,…,n}` all of whose elements are odd. -/
def oddPartSets (n : ℕ) : Finset (Finset ℤ) :=
  (maxSumFreeSets n).filter fun M => ∀ x ∈ M, Odd x

theorem mem_evenPartSets {n : ℕ} {M : Finset ℤ} :
    M ∈ evenPartSets n ↔ IsMaxSumFree n M ∧ ∀ x ∈ M, Even x := by
  rw [evenPartSets, Finset.mem_filter, mem_maxSumFreeSets]

theorem mem_oddPartSets {n : ℕ} {M : Finset ℤ} :
    M ∈ oddPartSets n ↔ IsMaxSumFree n M ∧ ∀ x ∈ M, Odd x := by
  rw [oddPartSets, Finset.mem_filter, mem_maxSumFreeSets]

/-- Every element of an all-odd maximal set lies in `odds n`, so uniqueness
(`eq_odds_of_isMaxSumFree_subset`) forces the set to be `odds n`. -/
theorem oddPartSets_eq_singleton (n : ℕ) : oddPartSets n = {odds n} := by
  ext M
  rw [mem_oddPartSets, Finset.mem_singleton]
  constructor
  · rintro ⟨hM, hodd⟩
    exact eq_odds_of_isMaxSumFree_subset hM fun x hx =>
      mem_odds.mpr ⟨hM.1 hx, Int.odd_iff.mp (hodd x hx)⟩
  · rintro rfl
    exact ⟨odds_isMaxSumFree n, fun x hx =>
      Int.odd_iff.mpr (mem_odds.mp hx).2⟩

theorem card_oddPartSets (n : ℕ) : (oddPartSets n).card = 1 := by
  rw [oddPartSets_eq_singleton, Finset.card_singleton]

/-- Halving, as an operation on finsets of integers. -/
def halve (s : Finset ℤ) : Finset ℤ := s.image (· / 2)

theorem mem_halve {s : Finset ℤ} {y : ℤ} :
    y ∈ halve s ↔ ∃ x ∈ s, x / 2 = y :=
  Finset.mem_image

/-- Halving is injective on even integers. -/
theorem injOn_halve_even : Set.InjOn (· / 2) {x : ℤ | Even x} := by
  intro x hx y hy hxy
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  change (a + a) / 2 = (b + b) / 2 at hxy
  omega

/-- Halving an inserted element: `halve (insert x s) = insert (x/2) (halve s)`. -/
theorem halve_insert (x : ℤ) (s : Finset ℤ) :
    halve (insert x s) = insert (x / 2) (halve s) :=
  Finset.image_insert _ _ _

/-- Halving preserves and reflects sum-freeness on all-even sets:
halves of evens preserve sums in both directions. -/
theorem isSumFree_halve_iff {M : Finset ℤ} (hpar : ∀ x ∈ M, Even x) :
    IsSumFree (halve M) ↔ IsSumFree M := by
  constructor
  · intro hsf x hx y hy hxy
    have h1 : x / 2 ∈ halve M := Finset.mem_image.mpr ⟨x, hx, rfl⟩
    have h2 : y / 2 ∈ halve M := Finset.mem_image.mpr ⟨y, hy, rfl⟩
    have h3 : x / 2 + y / 2 ∈ halve M := by
      have h4 : (x + y) / 2 ∈ halve M :=
        Finset.mem_image.mpr ⟨x + y, hxy, rfl⟩
      obtain ⟨a, rfl⟩ := hpar x hx
      obtain ⟨b, rfl⟩ := hpar y hy
      have h5 : (a + a + (b + b)) / 2 = (a + a) / 2 + (b + b) / 2 := by omega
      rwa [h5] at h4
    exact hsf _ h1 _ h2 h3
  · intro hsf u hu v hv huv
    obtain ⟨x, hx, hux⟩ := Finset.mem_image.mp hu
    obtain ⟨y, hy, hvy⟩ := Finset.mem_image.mp hv
    obtain ⟨z, hz, hzw⟩ := Finset.mem_image.mp huv
    obtain ⟨a, rfl⟩ := hpar x hx
    obtain ⟨b, rfl⟩ := hpar y hy
    obtain ⟨c, rfl⟩ := hpar z hz
    -- `hux : (a+a)/2 = u`, `hvy : (b+b)/2 = v`, `hzw : (c+c)/2 = u + v`,
    -- so `a + a + (b + b) = c + c`.
    have hab : a + a + (b + b) = c + c := by omega
    exact hsf _ hx _ hy (by rwa [hab])

/-- Halving sends an all-even maximal sum-free subset of `{1,…,n}` to a
maximal sum-free subset of `{1,…,n/2}`. -/
theorem halve_mem_maxSumFreeSets {n : ℕ} {M : Finset ℤ}
    (hM : M ∈ maxSumFreeSets n) (hpar : ∀ x ∈ M, Even x) :
    halve M ∈ maxSumFreeSets (n / 2) := by
  obtain ⟨hsub, hsf, hmax⟩ := mem_maxSumFreeSets.mp hM
  rw [mem_maxSumFreeSets]
  refine ⟨?_, (isSumFree_halve_iff hpar).mpr hsf, ?_⟩
  · -- `halve M ⊆ interval (n/2)`: even `x ∈ [1,n]` gives `x/2 ∈ [1,⌊n/2⌋]`.
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    have hxI := Finset.mem_Icc.mp (hsub hx)
    obtain ⟨a, rfl⟩ := hpar x hx
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · -- Maximality: for `y ∈ interval (n/2) \ halve M`, the element `2y` of
    -- `interval n` is absent from `M`, so `insert (2y) M` is not sum-free;
    -- halving the obstruction shows `insert y (halve M)` is not sum-free.
    intro y hyI hyM hsf'
    have hyI' := Finset.mem_Icc.mp hyI
    have h2yI : 2 * y ∈ interval n :=
      Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    have h2yM : 2 * y ∉ M := fun hmem =>
      hyM (Finset.mem_image.mpr ⟨2 * y, hmem, by omega⟩)
    have hpar' : ∀ x ∈ insert (2 * y) M, Even x := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact ⟨y, two_mul y⟩
      · exact hpar x hx
    have hmain : IsSumFree (insert (2 * y) M) := by
      rw [← isSumFree_halve_iff hpar', halve_insert]
      have h2 : (2 * y) / 2 = y := by omega
      rw [h2]
      exact hsf'
    exact hmax _ h2yI h2yM hmain

/-- `halve` is injective on all-even finsets. -/
theorem halve_injOn_even {M₁ M₂ : Finset ℤ} (h₁ : ∀ x ∈ M₁, Even x)
    (h₂ : ∀ x ∈ M₂, Even x) (h : halve M₁ = halve M₂) : M₁ = M₂ := by
  ext x
  constructor
  · intro hx
    have hxd : x / 2 ∈ halve M₂ := by
      have hx1 : x / 2 ∈ halve M₁ := Finset.mem_image.mpr ⟨x, hx, rfl⟩
      rwa [h] at hx1
    obtain ⟨x', hx', hxx⟩ := Finset.mem_image.mp hxd
    have hxeq : x = x' :=
      injOn_halve_even (h₁ x hx) (h₂ x' hx') hxx.symm
    rwa [hxeq]
  · intro hx
    have hxd : x / 2 ∈ halve M₁ := by
      have hx2 : x / 2 ∈ halve M₂ := Finset.mem_image.mpr ⟨x, hx, rfl⟩
      rwa [← h] at hx2
    obtain ⟨x', hx', hxx⟩ := Finset.mem_image.mp hxd
    have hxeq : x = x' :=
      injOn_halve_even (h₂ x hx) (h₁ x' hx') hxx.symm
    rwa [hxeq]

/-- `halve` injects `evenPartSets n` into `maxSumFreeSets (n/2)`. -/
theorem card_evenPartSets_le (n : ℕ) :
    (evenPartSets n).card ≤ maxSumFreeCount (n / 2) := by
  apply Finset.card_le_card_of_injOn halve
  · intro M hM
    obtain ⟨hmax, hpar⟩ := mem_evenPartSets.mp hM
    exact halve_mem_maxSumFreeSets (mem_maxSumFreeSets.mpr hmax) hpar
  · intro M₁ h₁ M₂ h₂ h
    exact halve_injOn_even (mem_evenPartSets.mp h₁).2
      (mem_evenPartSets.mp h₂).2 h

/-- Composing with the pair bound: `(evenPartSets n).card ≤ 2·3^{(n/2)/2}`. -/
theorem card_evenPartSets_le_two_mul_three_pow (n : ℕ) :
    (evenPartSets n).card ≤ 2 * 3 ^ ((n / 2) / 2) :=
  (card_evenPartSets_le n).trans (maxSumFreeCount_le_two_mul_three_pow (n / 2))

/-- The "mixed" maximal sum-free sets: those containing both an even and an
odd element. -/
def mixedPartSets (n : ℕ) : Finset (Finset ℤ) :=
  (maxSumFreeSets n).filter
    fun M => (∃ x ∈ M, Even x) ∧ ∃ x ∈ M, Odd x

theorem mem_mixedPartSets {n : ℕ} {M : Finset ℤ} :
    M ∈ mixedPartSets n ↔
      IsMaxSumFree n M ∧ (∃ x ∈ M, Even x) ∧ ∃ x ∈ M, Odd x := by
  rw [mixedPartSets, Finset.mem_filter, mem_maxSumFreeSets]

/-- Every maximal sum-free set is all-odd, all-even, or mixed. -/
theorem maxSumFreeSets_subset_union (n : ℕ) :
    maxSumFreeSets n ⊆ oddPartSets n ∪ evenPartSets n ∪ mixedPartSets n := by
  intro M hM
  rw [Finset.mem_union, Finset.mem_union]
  by_cases he : ∀ x ∈ M, Even x
  · exact Or.inl (Or.inr (mem_evenPartSets.mpr ⟨mem_maxSumFreeSets.mp hM, he⟩))
  · by_cases ho : ∀ x ∈ M, Odd x
    · exact Or.inl (Or.inl
        (mem_oddPartSets.mpr ⟨mem_maxSumFreeSets.mp hM, ho⟩))
    · apply Or.inr
      rw [mem_mixedPartSets]
      refine ⟨mem_maxSumFreeSets.mp hM, ?_, ?_⟩
      · push Not at ho
        obtain ⟨x, hx, hno⟩ := ho
        exact ⟨x, hx, Int.not_odd_iff_even.mp hno⟩
      · push Not at he
        obtain ⟨x, hx, hne⟩ := he
        exact ⟨x, hx, Int.not_even_iff_odd.mp hne⟩

/-- The counting decomposition: `f(n) ≤ 1 + f(n/2) + #mixed`. -/
theorem maxSumFreeCount_le_decomp (n : ℕ) :
    maxSumFreeCount n ≤
      1 + maxSumFreeCount (n / 2) + (mixedPartSets n).card := by
  have hcard := Finset.card_le_card (maxSumFreeSets_subset_union n)
  have hu1 := Finset.card_union_le
    (oddPartSets n ∪ evenPartSets n) (mixedPartSets n)
  have hu2 := Finset.card_union_le (oddPartSets n) (evenPartSets n)
  have hodd := card_oddPartSets n
  have heven := card_evenPartSets_le n
  simp only [maxSumFreeCount] at hcard heven ⊢
  omega

end JSP000728
