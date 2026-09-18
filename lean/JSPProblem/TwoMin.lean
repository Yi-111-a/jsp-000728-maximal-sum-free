import JSPProblem.NoConsec
import JSPProblem.MinDecomp
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Int.Interval

/-!
# JSP-000728 — the second-minimum refinement

The minimum decomposition (`minClass`) can be refined once more: a maximal
sum-free set `M` with minimum `m` either equals `{m}` or has a second-least
element `s`.  Since `M` is sum-free it avoids *both* translates
`x ↦ x + m` and `x ↦ x + s`, so `M \ {m, s}` is a subset of `Icc (s + 1) n`
carrying two independent translate constraints (`shiftFree2`).

* `secondMinClass n m s` : members of `minClass n m` whose second-least
  element is `s`; the boundary value `s = m` encodes the subsingleton case
  `M ⊆ {m}`, so `minClass n m` is *exactly* the disjoint union over
  `s ∈ Icc m n` (`minClass_eq_biUnion_secondMinClass`,
  `disjoint_secondMinClass`, `minClass_card_eq_sum_secondMinClass`).
* `subset_of_mem_secondMinClass`, `erase_erase_subset_Icc`,
  `shiftFree2_erase_min_of_mem_secondMinClass` : the structure
  `M ⊆ {m, s} ∪ Icc (s + 1) n` with the tail double-shift-free, and
  `secondMinClass_card_le_shiftFree2` : the class injects into the
  double-shift-free subsets of `Icc (s + 1) n`.
* `secondMinClass_two_mul` : the "clean case" `s = 2m` is in fact *void* —
  `m, 2m ∈ M` would give the Schur triple `m + m = 2m`, so the class is
  empty and its improved count is `0`
  (`secondMinClass_two_mul_card_bound`).
* `gap3`/`g3Sets` : subsets of `range L` with all gaps `≥ 3`, counted by
  `a(L+3) = a(L+2) + a(L)` with `a(0)=1, a(1)=2, a(3)=3`
  (`g3Sets_card_add_three`).  The hoped-for bound `a(L)·2^L ≤ 3^L` fails
  for `2 ≤ L ≤ 11`; it first holds at `L = 12`
  (`g3Sets_card_mul_two_pow_le_of_twelve_le`), while uniformly one has the
  `4/3`-lossy `3·a(L)·2^L ≤ 4·3^L` (`g3Sets_card_mul_two_pow_le`).
* `shiftFree2 m s` : shift-free for both `m` and `s`, with the product
  bound `card_powerset_filter_shiftFree2_le_prod`.  For `s = 2m`, the
  double-shift-free subsets of a length-`L` progression are exactly the
  gap-≥3 sets (`card_powerset_filter_shiftFree2_prog`), so over
  `Icc (m + 1) n` one gets `card · 2^{n−m} ≤ (4/3)^m · 3^{n−m}`
  (`card_powerset_filter_shiftFree2_Icc_mul_le`).
-/

namespace JSP000728

/-- The class of maximal sum-free `M ⊆ {1,…,n}` with minimum `m` whose
second-least element is `s`: `s ∈ M` and every other element is `≥ s`.
The boundary value `s = m` encodes the subsingleton case `M ⊆ {m}`. -/
def secondMinClass (n : ℕ) (m s : ℤ) : Finset (Finset ℤ) :=
  (minClass n m).filter fun M =>
    s ∈ M ∧ (∀ x ∈ M, x = m ∨ s ≤ x) ∧ (s = m → M ⊆ {m})

theorem mem_secondMinClass {n : ℕ} {M : Finset ℤ} {m s : ℤ} :
    M ∈ secondMinClass n m s ↔
      M ∈ minClass n m ∧ s ∈ M ∧ (∀ x ∈ M, x = m ∨ s ≤ x) ∧
        (s = m → M ⊆ {m}) :=
  Finset.mem_filter

/-- **Second-minimum decomposition.**  Every `M ∈ minClass n m` either is a
subsingleton `{m}` (class `s = m`) or has a second-least element
`s ∈ Icc m n`; hence `minClass n m` is the union of the second-minimum
classes over `s ∈ Icc m n`. -/
theorem minClass_eq_biUnion_secondMinClass {n : ℕ} {m : ℤ} :
    minClass n m = (Finset.Icc m (n : ℤ)).biUnion (secondMinClass n m) := by
  ext M
  rw [Finset.mem_biUnion]
  constructor
  · intro hM
    rw [mem_minClass] at hM
    obtain ⟨hmax, hmM, hmin⟩ := hM
    have hMmax : IsMaxSumFree n M := mem_maxSumFreeSets.mp hmax
    have hmI := Finset.mem_Icc.mp (hMmax.1 hmM)
    by_cases hsub : M ⊆ {m}
    · refine ⟨m, Finset.mem_Icc.mpr ⟨le_refl m, hmI.2⟩, ?_⟩
      rw [mem_secondMinClass]
      exact ⟨mem_minClass.mpr ⟨hmax, hmM, hmin⟩, hmM,
        fun x hx => Or.inr (hmin x hx), fun _ => hsub⟩
    · obtain ⟨x₀, hx₀M, hx₀⟩ := Finset.not_subset.mp hsub
      have hx₀' : x₀ ≠ m := fun h => hx₀ (Finset.mem_singleton.mpr h)
      have hne : (M.erase m).Nonempty :=
        ⟨x₀, Finset.mem_erase.mpr ⟨hx₀', hx₀M⟩⟩
      refine ⟨(M.erase m).min' hne, ?_, ?_⟩
      · have hsmem := Finset.min'_mem (M.erase m) hne
        obtain ⟨-, hsM⟩ := Finset.mem_erase.mp hsmem
        have hsI := Finset.mem_Icc.mp (hMmax.1 hsM)
        rw [Finset.mem_Icc]
        exact ⟨hmin _ hsM, hsI.2⟩
      · rw [mem_secondMinClass]
        refine ⟨mem_minClass.mpr ⟨hmax, hmM, hmin⟩,
          Finset.mem_of_mem_erase (Finset.min'_mem _ hne), ?_, ?_⟩
        · intro x hx
          rcases eq_or_ne x m with rfl | hxm
          · exact Or.inl rfl
          · exact Or.inr
              (Finset.min'_le _ _ (Finset.mem_erase.mpr ⟨hxm, hx⟩))
        · intro hsm
          exact absurd hsm
            (Finset.mem_erase.mp (Finset.min'_mem _ hne)).1
  · rintro ⟨s, -, hM⟩
    exact (mem_secondMinClass.mp hM).1

/-- Distinct second-minimum classes are disjoint: `s` is determined by `M`
as the least element above `m`. -/
theorem disjoint_secondMinClass {n : ℕ} {m : ℤ} :
    (↑(Finset.Icc m (n : ℤ)) : Set ℤ).PairwiseDisjoint
      (secondMinClass n m) := by
  intro s₁ _ s₂ _ hne
  show Disjoint (secondMinClass n m s₁) (secondMinClass n m s₂)
  rw [Finset.disjoint_left]
  rintro M hM₁ hM₂
  obtain ⟨-, hs₁M, hlb₁, hsg₁⟩ := mem_secondMinClass.mp hM₁
  obtain ⟨-, hs₂M, hlb₂, hsg₂⟩ := mem_secondMinClass.mp hM₂
  rcases eq_or_ne m s₁ with rfl | hs₁m
  · rcases eq_or_ne m s₂ with rfl | hs₂m
    · exact hne rfl
    · exact hs₂m (Finset.mem_singleton.mp (hsg₁ rfl hs₂M)).symm
  · rcases eq_or_ne m s₂ with rfl | hs₂m
    · exact hs₁m (Finset.mem_singleton.mp (hsg₂ rfl hs₁M)).symm
    · exact hne (le_antisymm
        ((hlb₁ s₂ hs₂M).resolve_left (fun h => hs₂m h.symm))
        ((hlb₂ s₁ hs₁M).resolve_left (fun h => hs₁m h.symm)))

/-- `|minClass n m|` is the sum over `s ∈ Icc m n` of the second-minimum
class sizes. -/
theorem minClass_card_eq_sum_secondMinClass {n : ℕ} {m : ℤ} :
    (minClass n m).card =
      ∑ s ∈ Finset.Icc m (n : ℤ), (secondMinClass n m s).card := by
  rw [minClass_eq_biUnion_secondMinClass,
    Finset.card_biUnion disjoint_secondMinClass]

/-- Shift-freeness from a single member: `x, s ∈ M` forces `x + s ∉ M`. -/
theorem not_mem_add_of_isSumFree {M : Finset ℤ} (hsf : IsSumFree M)
    {s x : ℤ} (hs : s ∈ M) (hx : x ∈ M) : x + s ∉ M :=
  hsf x hx s hs

/-- The second translate constraint: members of `secondMinClass n m s`
avoid the shift `x ↦ x + s`. -/
theorem not_mem_add_of_mem_secondMinClass {n : ℕ} {m s : ℤ} {M : Finset ℤ}
    (hM : M ∈ secondMinClass n m s) {x : ℤ} (hx : x ∈ M) : x + s ∉ M := by
  obtain ⟨hmin, hsM, -, -⟩ := mem_secondMinClass.mp hM
  obtain ⟨hmax, -, -⟩ := mem_minClass.mp hmin
  exact (mem_maxSumFreeSets.mp hmax).2.1 x hx s hsM

/-- Structural form: `M ⊆ {m, s} ∪ Icc (s + 1) n`. -/
theorem subset_of_mem_secondMinClass {n : ℕ} {m s : ℤ} {M : Finset ℤ}
    (hM : M ∈ secondMinClass n m s) :
    M ⊆ insert m (insert s (Finset.Icc (s + 1) (n : ℤ))) := by
  obtain ⟨hmin, -, hlb, -⟩ := mem_secondMinClass.mp hM
  obtain ⟨hmax, -, -⟩ := mem_minClass.mp hmin
  have hsub := (mem_maxSumFreeSets.mp hmax).1
  intro x hx
  rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_Icc]
  rcases hlb x hx with rfl | hle
  · exact Or.inl rfl
  · rcases eq_or_ne x s with rfl | hne
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr ⟨by omega, (Finset.mem_Icc.mp (hsub hx)).2⟩)

/-- The tail `M \ {m, s}` lies inside `Icc (s + 1) n`. -/
theorem erase_erase_subset_Icc {n : ℕ} {m s : ℤ} {M : Finset ℤ}
    (hM : M ∈ secondMinClass n m s) :
    (M.erase m).erase s ⊆ Finset.Icc (s + 1) (n : ℤ) := by
  obtain ⟨hmin, -, hlb, -⟩ := mem_secondMinClass.mp hM
  obtain ⟨hmax, -, -⟩ := mem_minClass.mp hmin
  have hsub := (mem_maxSumFreeSets.mp hmax).1
  intro x hx
  obtain ⟨hxs, hx⟩ := Finset.mem_erase.mp hx
  obtain ⟨hxm, hxM⟩ := Finset.mem_erase.mp hx
  have hle : s ≤ x := (hlb x hxM).resolve_left hxm
  rw [Finset.mem_Icc]
  exact ⟨by omega, (Finset.mem_Icc.mp (hsub hxM)).2⟩

/-- `M \ {m}` is shift-free for both `m` and `s`. -/
theorem shiftFree2_erase_min_of_mem_secondMinClass {n : ℕ} {m s : ℤ}
    {M : Finset ℤ} (hM : M ∈ secondMinClass n m s) :
    shiftFree m (M.erase m) ∧ shiftFree s (M.erase m) := by
  obtain ⟨hmin, hsM, -, -⟩ := mem_secondMinClass.mp hM
  obtain ⟨hmax, hmM, -⟩ := mem_minClass.mp hmin
  have hsf := (mem_maxSumFreeSets.mp hmax).2.1
  refine ⟨fun x hx hC => ?_, fun x hx hC => ?_⟩
  · rw [Finset.mem_erase] at hx hC
    exact hsf x hx.2 m hmM hC.2
  · rw [Finset.mem_erase] at hx hC
    exact hsf x hx.2 s hsM hC.2

/-- Double shift-freeness: `x ∈ t` excludes both `x + m` and `x + s`. -/
def shiftFree2 (m s : ℤ) (t : Finset ℤ) : Prop :=
  shiftFree m t ∧ shiftFree s t

instance decidableShiftFree2 (m s : ℤ) (t : Finset ℤ) :
    Decidable (shiftFree2 m s t) := by
  unfold shiftFree2; infer_instance

theorem shiftFree2.mono {m s : ℤ} {t u : Finset ℤ} (h : shiftFree2 m s u)
    (htu : t ⊆ u) : shiftFree2 m s t :=
  ⟨h.1.mono htu, h.2.mono htu⟩

/-- Deleting `m` and `s` injects `secondMinClass n m s` into the
double-shift-free subsets of `Icc (s + 1) n`. -/
theorem secondMinClass_card_le_shiftFree2 {n : ℕ} {m s : ℤ} :
    (secondMinClass n m s).card ≤
      ((Finset.Icc (s + 1) (n : ℤ)).powerset.filter (shiftFree2 m s)).card := by
  refine Finset.card_le_card_of_injOn (fun M => (M.erase m).erase s) ?_ ?_
  · intro M hM
    have hsub := erase_erase_subset_Icc (Finset.mem_coe.mp hM)
    rw [Finset.mem_coe, mem_secondMinClass] at hM
    obtain ⟨hmin, hsM, -, -⟩ := hM
    obtain ⟨hmax, hmM, -⟩ := mem_minClass.mp hmin
    have hMmax := mem_maxSumFreeSets.mp hmax
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset]
    refine ⟨hsub, ?_, ?_⟩
    · intro x hx hC
      obtain ⟨-, hx⟩ := Finset.mem_erase.mp hx
      obtain ⟨hxm, hxM⟩ := Finset.mem_erase.mp hx
      obtain ⟨-, hC⟩ := Finset.mem_erase.mp hC
      obtain ⟨-, hCM⟩ := Finset.mem_erase.mp hC
      exact hMmax.2.1 x hxM m hmM hCM
    · intro x hx hC
      obtain ⟨-, hx⟩ := Finset.mem_erase.mp hx
      obtain ⟨hxm, hxM⟩ := Finset.mem_erase.mp hx
      obtain ⟨-, hC⟩ := Finset.mem_erase.mp hC
      obtain ⟨-, hCM⟩ := Finset.mem_erase.mp hC
      exact hMmax.2.1 x hxM s hsM hCM
  · intro M₁ hM₁ M₂ hM₂ h
    rw [Finset.mem_coe, mem_secondMinClass] at hM₁ hM₂
    obtain ⟨hmin₁, hs₁, -, hsg₁⟩ := hM₁
    obtain ⟨hmin₂, hs₂, -, hsg₂⟩ := hM₂
    have hm₁ := (mem_minClass.mp hmin₁).2.1
    have hm₂ := (mem_minClass.mp hmin₂).2.1
    by_cases hsm : s = m
    · have e1 : M₁ = {m} := Finset.eq_singleton_iff_unique_mem.mpr
        ⟨hm₁, fun x hx => Finset.mem_singleton.mp (hsg₁ hsm hx)⟩
      have e2 : M₂ = {m} := Finset.eq_singleton_iff_unique_mem.mpr
        ⟨hm₂, fun x hx => Finset.mem_singleton.mp (hsg₂ hsm hx)⟩
      rw [e1, e2]
    · have hs₁' : s ∈ M₁.erase m := Finset.mem_erase.mpr ⟨hsm, hs₁⟩
      have hs₂' : s ∈ M₂.erase m := Finset.mem_erase.mpr ⟨hsm, hs₂⟩
      have e1 : insert s ((M₁.erase m).erase s) = M₁.erase m :=
        Finset.insert_erase hs₁'
      have e2 : insert s ((M₂.erase m).erase s) = M₂.erase m :=
        Finset.insert_erase hs₂'
      calc M₁ = insert m (M₁.erase m) := (Finset.insert_erase hm₁).symm
        _ = insert m (insert s ((M₁.erase m).erase s)) := by rw [e1]
        _ = insert m (insert s ((M₂.erase m).erase s)) := by
              have h' : (M₁.erase m).erase s = (M₂.erase m).erase s := h
              rw [h']
        _ = insert m (M₂.erase m) := by rw [e2]
        _ = M₂ := Finset.insert_erase hm₂

/-- **The `s = 2m` case is void.**  `m ∈ M` and `2m ∈ M` would give the
Schur triple `m + m = 2m` inside the sum-free set `M`, so the second
element can never be `2m`. -/
theorem secondMinClass_two_mul (n : ℕ) (m : ℤ) :
    secondMinClass n m (2 * m) = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro M hM
  obtain ⟨hmin, hsM, -, -⟩ := mem_secondMinClass.mp hM
  obtain ⟨hmax, hmM, -⟩ := mem_minClass.mp hmin
  have hsf := (mem_maxSumFreeSets.mp hmax).2.1
  rw [two_mul] at hsM
  exact hsf m hmM m hmM hsM

theorem secondMinClass_two_mul_card (n : ℕ) (m : ℤ) :
    (secondMinClass n m (2 * m)).card = 0 := by
  rw [secondMinClass_two_mul, Finset.card_empty]

/-- The improved count for `s = 2m`: the class is empty, so the promised
bound holds trivially (with room to spare). -/
theorem secondMinClass_two_mul_card_bound (n : ℕ) (m : ℤ) :
    (secondMinClass n m (2 * m)).card * 2 ^ ((n : ℤ) - m).toNat ≤
      4 * 3 ^ ((n : ℤ) - m).toNat := by
  rw [secondMinClass_two_mul_card]
  simp

/-- A finset of naturals whose elements are pairwise at distance `≥ 3`:
`x ∈ t` forces `x + 1 ∉ t` and `x + 2 ∉ t`. -/
def gap3 (t : Finset ℕ) : Prop := ∀ x ∈ t, x + 1 ∉ t ∧ x + 2 ∉ t

instance decidableGap3 (t : Finset ℕ) : Decidable (gap3 t) := by
  unfold gap3; infer_instance

/-- The family of gap-≥3 subsets of `Finset.range L`. -/
def g3Sets (L : ℕ) : Finset (Finset ℕ) :=
  (Finset.range L).powerset.filter gap3

theorem mem_g3Sets {L : ℕ} {t : Finset ℕ} :
    t ∈ g3Sets L ↔ t ⊆ Finset.range L ∧ gap3 t := by
  simp [g3Sets]

/-- Subsets `t ⊆ range (L+2)` whose insertion of `L+2` stays gap-≥3 are
exactly the gap-≥3 subsets of `range L`: `L + 2` excludes `L` and `L + 1`. -/
theorem g3Sets_insert_filter (L : ℕ) :
    (Finset.range (L + 2)).powerset.filter
        (fun t => gap3 (insert (L + 2) t)) = g3Sets L := by
  ext t
  rw [Finset.mem_filter, Finset.mem_powerset, mem_g3Sets]
  constructor
  · rintro ⟨ht, hg⟩
    refine ⟨?_, ?_⟩
    · intro x hx
      have hxlt : x < L + 2 := Finset.mem_range.mp (ht hx)
      rw [Finset.mem_range]
      rcases lt_or_ge x L with h | h
      · exact h
      · rcases (show L = x ∨ L + 1 = x by omega) with rfl | rfl
        · exact absurd (Finset.mem_insert_self (L + 2) t)
            (hg L (Finset.mem_insert_of_mem hx)).2
        · exact absurd (Finset.mem_insert_self (L + 2) t)
            (hg (L + 1) (Finset.mem_insert_of_mem hx)).1
    · intro x hx
      obtain ⟨h1, h2⟩ := hg x (Finset.mem_insert_of_mem hx)
      exact ⟨fun h => h1 (Finset.mem_insert_of_mem h),
        fun h => h2 (Finset.mem_insert_of_mem h)⟩
  · rintro ⟨ht, hg⟩
    refine ⟨?_, ?_⟩
    · intro x hx
      have := Finset.mem_range.mp (ht hx)
      exact Finset.mem_range.mpr (by omega)
    · intro x hx
      rw [Finset.mem_insert] at hx
      rcases hx with rfl | hx
      · refine ⟨?_, ?_⟩
        · intro hC
          rw [Finset.mem_insert] at hC
          rcases hC with h | h
          · omega
          · have := Finset.mem_range.mp (ht h); omega
        · intro hC
          rw [Finset.mem_insert] at hC
          rcases hC with h | h
          · omega
          · have := Finset.mem_range.mp (ht h); omega
      · have hxlt : x < L := Finset.mem_range.mp (ht hx)
        obtain ⟨h1, h2⟩ := hg x hx
        refine ⟨?_, ?_⟩
        · intro hC
          rw [Finset.mem_insert] at hC
          rcases hC with h | h
          · omega
          · exact h1 h
        · intro hC
          rw [Finset.mem_insert] at hC
          rcases hC with h | h
          · omega
          · exact h2 h

/-- The three-step recursion for `g3Sets`: subsets of `range (L+3)` either
avoid `L+2` (subsets of `range (L+2)`) or contain it (insertions into
subsets of `range L`). -/
theorem g3Sets_add_three (L : ℕ) :
    g3Sets (L + 3) =
      g3Sets (L + 2) ∪ (g3Sets L).image (insert (L + 2)) := by
  unfold g3Sets
  rw [Finset.range_add_one, Finset.powerset_insert, Finset.filter_union,
    Finset.filter_image, g3Sets_insert_filter]
  rfl

/-- `|g3Sets (L+3)| = |g3Sets (L+2)| + |g3Sets L|`. -/
theorem g3Sets_card_add_three (L : ℕ) :
    (g3Sets (L + 3)).card = (g3Sets (L + 2)).card + (g3Sets L).card := by
  have hd : Disjoint (g3Sets (L + 2)) ((g3Sets L).image (insert (L + 2))) := by
    rw [Finset.disjoint_left]
    intro s hs hsB
    rw [Finset.mem_image] at hsB
    obtain ⟨t, -, rfl⟩ := hsB
    rw [mem_g3Sets] at hs
    have := Finset.mem_range.mp (hs.1 (Finset.mem_insert_self (L + 2) t))
    omega
  rw [g3Sets_add_three, Finset.card_union_of_disjoint hd]
  congr 1
  apply Finset.card_image_of_injOn
  intro t₁ ht₁ t₂ ht₂ h
  rw [Finset.mem_coe, mem_g3Sets] at ht₁ ht₂
  have h1 : L + 2 ∉ t₁ := by
    intro hmem
    have := Finset.mem_range.mp (ht₁.1 hmem)
    omega
  have h2 : L + 2 ∉ t₂ := by
    intro hmem
    have := Finset.mem_range.mp (ht₂.1 hmem)
    omega
  have e := congrArg (Finset.erase · (L + 2)) h
  rwa [Finset.erase_insert h1, Finset.erase_insert h2] at e

theorem g3Sets_zero : g3Sets 0 = {∅} := by
  ext t
  rw [mem_g3Sets, Finset.range_zero, Finset.subset_empty, Finset.mem_singleton]
  refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
  subst h
  intro x hx
  exact absurd hx (Finset.notMem_empty _)

theorem g3Sets_one : g3Sets 1 = {∅, {0}} := by
  ext t
  rw [mem_g3Sets, Finset.range_one, Finset.subset_singleton_iff,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨h, -⟩
    exact h
  · rintro (rfl | rfl)
    · exact ⟨Or.inl rfl, fun x hx => absurd hx (Finset.notMem_empty _)⟩
    · refine ⟨Or.inr rfl, fun x hx => ?_⟩
      rw [Finset.mem_singleton] at hx
      subst hx
      constructor <;> decide

theorem g3Sets_two : g3Sets 2 = {∅, {0}, {1}} := by
  ext t
  rw [mem_g3Sets, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨ht, hg⟩
    have hsub : ∀ x ∈ t, x = 0 ∨ x = 1 := by
      intro x hx
      have := Finset.mem_range.mp (ht hx)
      omega
    by_cases h0 : (0 : ℕ) ∈ t
    · by_cases h1 : (1 : ℕ) ∈ t
      · exact absurd h1 (hg 0 h0).1
      · refine Or.inr (Or.inl ?_)
        rw [Finset.eq_singleton_iff_unique_mem]
        exact ⟨h0, fun x hx =>
          (hsub x hx).resolve_right (fun h => h1 (h ▸ hx))⟩
    · by_cases h1 : (1 : ℕ) ∈ t
      · refine Or.inr (Or.inr ?_)
        rw [Finset.eq_singleton_iff_unique_mem]
        exact ⟨h1, fun x hx =>
          (hsub x hx).resolve_left (fun h => h0 (h ▸ hx))⟩
      · refine Or.inl ?_
        rw [Finset.eq_empty_iff_forall_notMem]
        intro x hx
        rcases hsub x hx with rfl | rfl
        · exact h0 hx
        · exact h1 hx
  · rintro (rfl | rfl | rfl)
    · exact ⟨Finset.empty_subset _, fun x hx =>
        absurd hx (Finset.notMem_empty _)⟩
    · refine ⟨?_, ?_⟩
      · intro x hx
        rw [Finset.mem_singleton] at hx
        subst hx
        exact Finset.mem_range.mpr (by norm_num)
      · intro x hx
        rw [Finset.mem_singleton] at hx
        subst hx
        constructor <;> decide
    · refine ⟨?_, ?_⟩
      · intro x hx
        rw [Finset.mem_singleton] at hx
        subst hx
        exact Finset.mem_range.mpr (by norm_num)
      · intro x hx
        rw [Finset.mem_singleton] at hx
        subst hx
        constructor <;> decide

/-- Base counts: `a(0) = 1`. -/
theorem g3Sets_card_zero : (g3Sets 0).card = 1 := by
  rw [g3Sets_zero, Finset.card_singleton]

/-- Base counts: `a(1) = 2`. -/
theorem g3Sets_card_one : (g3Sets 1).card = 2 := by
  rw [g3Sets_one, Finset.card_pair (by simp)]

/-- Base counts: `a(2) = 3`. -/
theorem g3Sets_card_two : (g3Sets 2).card = 3 := by
  rw [g3Sets_two, Finset.card_insert_of_notMem (by decide),
    Finset.card_insert_of_notMem (by decide), Finset.card_singleton]

/-- **Uniform rational bound.**  `3·a(L)·2^L ≤ 4·3^L` for all `L`, i.e.
`a(L) ≤ (4/3)·(3/2)^L`: the three-step induction
`3a(L+3)2^{L+3} = 2·(3a(L+2)2^{L+2}) + 8·(3a(L)2^L) ≤ 8·3^{L+2} + 32·3^L
= 104·3^L ≤ 108·3^L = 4·3^{L+3}`. -/
theorem g3Sets_card_mul_two_pow_le (L : ℕ) :
    3 * ((g3Sets L).card * 2 ^ L) ≤ 4 * 3 ^ L := by
  suffices h : ∀ L : ℕ, 3 * ((g3Sets L).card * 2 ^ L) ≤ 4 * 3 ^ L ∧
      3 * ((g3Sets (L + 1)).card * 2 ^ (L + 1)) ≤ 4 * 3 ^ (L + 1) ∧
      3 * ((g3Sets (L + 2)).card * 2 ^ (L + 2)) ≤ 4 * 3 ^ (L + 2) from (h L).1
  intro L
  induction L with
  | zero =>
      refine ⟨?_, ?_, ?_⟩
      · rw [g3Sets_card_zero]; norm_num
      · show 3 * ((g3Sets 1).card * 2 ^ 1) ≤ 4 * 3 ^ 1
        rw [g3Sets_card_one]; norm_num
      · show 3 * ((g3Sets 2).card * 2 ^ 2) ≤ 4 * 3 ^ 2
        rw [g3Sets_card_two]; norm_num
  | succ L ih =>
      obtain ⟨ih0, ih1, ih2⟩ := ih
      refine ⟨ih1, ih2, ?_⟩
      show 3 * ((g3Sets (L + 3)).card * 2 ^ (L + 3)) ≤ 4 * 3 ^ (L + 3)
      calc 3 * ((g3Sets (L + 3)).card * 2 ^ (L + 3))
          = 2 * (3 * ((g3Sets (L + 2)).card * 2 ^ (L + 2))) +
              8 * (3 * ((g3Sets L).card * 2 ^ L)) := by
            rw [g3Sets_card_add_three, pow_add, pow_add]; ring
        _ ≤ 2 * (4 * 3 ^ (L + 2)) + 8 * (4 * 3 ^ L) :=
            add_le_add (Nat.mul_le_mul (le_refl 2) ih2)
              (Nat.mul_le_mul (le_refl 8) ih0)
        _ = 104 * 3 ^ L := by rw [pow_add]; ring
        _ ≤ 4 * 3 ^ (L + 3) := by
            rw [pow_add]
            calc 104 * 3 ^ L ≤ 108 * 3 ^ L :=
                Nat.mul_le_mul (show (104 : ℕ) ≤ 108 by norm_num) (le_refl _)
              _ = 4 * (3 ^ L * 3 ^ 3) := by ring

/-- **Clean rational bound (long classes).**  `a(L)·2^L ≤ 3^L` holds once
`L ≥ 12` (it fails for `2 ≤ L ≤ 11`): the step
`a(L+3)·2^{L+3} = 2·a(L+2)·2^{L+2} + 8·a(L)·2^L ≤ 2·3^{L+2} + 8·3^L
= 26·3^L ≤ 27·3^L`. -/
theorem g3Sets_card_mul_two_pow_le_of_twelve_le {L : ℕ} (hL : 12 ≤ L) :
    (g3Sets L).card * 2 ^ L ≤ 3 ^ L := by
  suffices h : ∀ k : ℕ,
      (g3Sets (k + 12)).card * 2 ^ (k + 12) ≤ 3 ^ (k + 12) ∧
      (g3Sets (k + 13)).card * 2 ^ (k + 13) ≤ 3 ^ (k + 13) ∧
      (g3Sets (k + 14)).card * 2 ^ (k + 14) ≤ 3 ^ (k + 14) by
    have hk := (h (L - 12)).1
    rwa [Nat.sub_add_cancel hL] at hk
  intro k
  induction k with
  | zero =>
      refine ⟨?_, ?_, ?_⟩
      · norm_num [g3Sets_card_add_three, g3Sets_card_zero, g3Sets_card_one,
          g3Sets_card_two]
      · norm_num [g3Sets_card_add_three, g3Sets_card_zero, g3Sets_card_one,
          g3Sets_card_two]
      · norm_num [g3Sets_card_add_three, g3Sets_card_zero, g3Sets_card_one,
          g3Sets_card_two]
  | succ k ih =>
      obtain ⟨ih0, ih1, ih2⟩ := ih
      refine ⟨ih1, ih2, ?_⟩
      show (g3Sets (k + 15)).card * 2 ^ (k + 15) ≤ 3 ^ (k + 15)
      have hrec : (g3Sets (k + 15)).card =
          (g3Sets (k + 14)).card + (g3Sets (k + 12)).card :=
        g3Sets_card_add_three (k + 12)
      calc (g3Sets (k + 15)).card * 2 ^ (k + 15)
          = 2 * ((g3Sets (k + 14)).card * 2 ^ (k + 14)) +
              8 * ((g3Sets (k + 12)).card * 2 ^ (k + 12)) := by
            rw [hrec, show k + 15 = k + 12 + 3 from rfl, pow_add,
              show k + 14 = k + 12 + 2 from rfl, pow_add]
            ring
        _ ≤ 2 * 3 ^ (k + 14) + 8 * 3 ^ (k + 12) :=
            add_le_add (Nat.mul_le_mul (le_refl 2) ih2)
              (Nat.mul_le_mul (le_refl 8) ih0)
        _ = 26 * 3 ^ (k + 12) := by
            rw [show k + 14 = k + 12 + 2 from rfl, pow_add]; ring
        _ ≤ 3 ^ (k + 15) := by
            have hpow : (3 : ℕ) ^ (k + 15) = 27 * 3 ^ (k + 12) := by
              rw [show k + 15 = k + 12 + 3 from rfl, pow_add]; ring
            rw [hpow]
            exact Nat.mul_le_mul (show (26 : ℕ) ≤ 27 by norm_num) (le_refl _)

/-- **Binary factorisation for `shiftFree2`.** -/
theorem card_powerset_filter_shiftFree2_le_mul {m s : ℤ} {T T₁ T₂ : Finset ℤ}
    (hT : T ⊆ T₁ ∪ T₂) :
    (T.powerset.filter (shiftFree2 m s)).card ≤
      (T₁.powerset.filter (shiftFree2 m s)).card *
        (T₂.powerset.filter (shiftFree2 m s)).card := by
  rw [← Finset.card_product]
  refine Finset.card_le_card_of_injOn (fun t => (t ∩ T₁, t ∩ T₂)) ?_ ?_
  · intro t ht
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset] at ht
    rw [Finset.mem_coe, Finset.mem_product, Finset.mem_filter,
      Finset.mem_powerset, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨⟨Finset.inter_subset_right, ht.2.mono Finset.inter_subset_left⟩,
      ⟨Finset.inter_subset_right, ht.2.mono Finset.inter_subset_left⟩⟩
  · intro t ht u hu h
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset] at ht hu
    have e1 : t ∩ T₁ = u ∩ T₁ := congrArg Prod.fst h
    have e2 : t ∩ T₂ = u ∩ T₂ := congrArg Prod.snd h
    calc t = t ∩ T₁ ∪ t ∩ T₂ := by
          rw [← Finset.inter_union_distrib_left,
            Finset.inter_eq_left.mpr (ht.1.trans hT)]
      _ = u ∩ T₁ ∪ u ∩ T₂ := by rw [e1, e2]
      _ = u := by
          rw [← Finset.inter_union_distrib_left,
            Finset.inter_eq_left.mpr (hu.1.trans hT)]

/-- **Product bound for `shiftFree2`.** -/
theorem card_powerset_filter_shiftFree2_le_prod {m s : ℤ} {ι : Type*}
    [DecidableEq ι] (R : Finset ι) (C : ι → Finset ℤ) (T : Finset ℤ)
    (hT : T ⊆ R.biUnion C) :
    (T.powerset.filter (shiftFree2 m s)).card ≤
      ∏ r ∈ R, ((C r).powerset.filter (shiftFree2 m s)).card := by
  suffices h : ∀ (R : Finset ι) (T : Finset ℤ), T ⊆ R.biUnion C →
      (T.powerset.filter (shiftFree2 m s)).card ≤
        ∏ r ∈ R, ((C r).powerset.filter (shiftFree2 m s)).card from h R T hT
  intro R
  induction R using Finset.induction with
  | empty =>
    intro T hT
    rw [Finset.biUnion_empty, Finset.subset_empty] at hT
    subst hT
    rw [Finset.prod_empty]
    calc ((∅ : Finset ℤ).powerset.filter (shiftFree2 m s)).card
        ≤ (Finset.powerset (∅ : Finset ℤ)).card :=
          Finset.card_le_card (Finset.filter_subset _ _)
      _ = 1 := by rw [Finset.powerset_empty, Finset.card_singleton]
  | insert a s ha ih =>
    intro T hT
    rw [Finset.biUnion_insert] at hT
    refine (card_powerset_filter_shiftFree2_le_mul hT).trans ?_
    rw [Finset.prod_insert ha]
    exact Nat.mul_le_mul le_rfl (ih _ Finset.Subset.rfl)

/-- Shift-free for `m` and `2m` inside a step-`m` progression is gap-≥3 in
the index: `x + m` is index-distance `1` and `x + 2m` index-distance `2`. -/
theorem card_powerset_filter_shiftFree2_prog {m : ℤ} (hm : 0 < m) (a : ℤ)
    (L : ℕ) :
    ((prog m a L).powerset.filter (shiftFree2 m (2 * m))).card =
      (g3Sets L).card := by
  rw [prog_eq_image]
  set g : ℕ → ℤ := fun k => a + m * (k : ℤ) with hg_def
  have hg : Function.Injective g := by
    intro k₁ k₂ h
    simp only [hg_def] at h
    have h1 : m * (k₁ : ℤ) = m * (k₂ : ℤ) := add_left_cancel h
    have h2 : (k₁ : ℤ) = (k₂ : ℤ) := mul_left_cancel₀ (ne_of_gt hm) h1
    exact_mod_cast h2
  have hstep : ∀ k : ℕ, g k + m = g (k + 1) := by
    intro k
    simp only [hg_def]
    push_cast
    ring
  have hstep2 : ∀ k : ℕ, g k + 2 * m = g (k + 2) := by
    intro k
    simp only [hg_def]
    push_cast
    ring
  have hset : ((Finset.range L).image g).powerset.filter
        (shiftFree2 m (2 * m)) =
      (g3Sets L).image (fun t => t.image g) := by
    ext u
    rw [Finset.mem_filter, Finset.mem_powerset]
    constructor
    · rintro ⟨hu, hsf1, hsf2⟩
      refine Finset.mem_image.mpr
        ⟨(Finset.range L).filter fun k => g k ∈ u, ?_, ?_⟩
      · rw [mem_g3Sets]
        refine ⟨Finset.filter_subset _ _, ?_⟩
        intro k hk
        rw [Finset.mem_filter] at hk
        refine ⟨?_, ?_⟩
        · intro hC
          rw [Finset.mem_filter] at hC
          have h1 : g (k + 1) ∉ u := by
            have h2 := hsf1 (g k) hk.2
            rwa [hstep k] at h2
          exact h1 hC.2
        · intro hC
          rw [Finset.mem_filter] at hC
          have h1 : g (k + 2) ∉ u := by
            have h2 := hsf2 (g k) hk.2
            rwa [hstep2 k] at h2
          exact h1 hC.2
      · ext x
        rw [Finset.mem_image]
        constructor
        · intro hx
          obtain ⟨k, hk, rfl⟩ := hx
          exact (Finset.mem_filter.mp hk).2
        · intro hx
          obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp (hu hx)
          exact ⟨k, Finset.mem_filter.mpr ⟨hk, hx⟩, rfl⟩
    · intro h
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp h
      rw [mem_g3Sets] at ht
      refine ⟨Finset.image_subset_image ht.1, ?_, ?_⟩
      · intro x hx
        obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
        rw [hstep k]
        intro h
        obtain ⟨k', hk', hkk'⟩ := Finset.mem_image.mp h
        have : k' = k + 1 := hg hkk'
        exact (ht.2 k hk).1 (this ▸ hk')
      · intro x hx
        obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
        rw [hstep2 k]
        intro h
        obtain ⟨k', hk', hkk'⟩ := Finset.mem_image.mp h
        have : k' = k + 2 := hg hkk'
        exact (ht.2 k hk).2 (this ▸ hk')
  rw [hset, Finset.card_image_of_injective _ (Finset.image_injective hg)]

/-- The double-shift-free count of a residue class. -/
theorem card_powerset_filter_shiftFree2_cls {n : ℕ} {m r : ℤ} (hm : 1 ≤ m) :
    ((cls n m r).powerset.filter (shiftFree2 m (2 * m))).card =
      (g3Sets (((n : ℤ) - r) / m).toNat).card :=
  card_powerset_filter_shiftFree2_prog (by omega) (r + m) _

/-- Double-shift-free subsets of `Icc (m + 1) n` are at most the product
over residue classes of their gap-≥3 counts. -/
theorem card_powerset_filter_shiftFree2_Icc_le {n : ℕ} {m : ℤ} (hm : 1 ≤ m) :
    ((Finset.Icc (m + 1) (n : ℤ)).powerset.filter (shiftFree2 m (2 * m))).card ≤
      ∏ r ∈ Finset.Icc 1 m, (g3Sets (((n : ℤ) - r) / m).toNat).card :=
  (card_powerset_filter_shiftFree2_le_prod (Finset.Icc 1 m) (cls n m)
    (Finset.Icc (m + 1) (n : ℤ)) (Icc_subset_biUnion_cls hm)).trans
    (Finset.prod_le_prod fun r _ =>
      le_of_eq (card_powerset_filter_shiftFree2_cls (n := n) (r := r) hm))

/-- **Assembled bound.**  Combining the class factorisation with the
uniform `3·a(L)·2^L ≤ 4·3^L` gives, for `N = n - m`,

  `card · 3^m · 2^N ≤ 4^m · 3^N`,  i.e.  `card · 2^N ≤ (4/3)^m · 3^N`. -/
theorem card_powerset_filter_shiftFree2_Icc_mul_le {n : ℕ} {m : ℤ}
    (hm : 1 ≤ m) :
    3 ^ m.toNat *
        (((Finset.Icc (m + 1) (n : ℤ)).powerset.filter
          (shiftFree2 m (2 * m))).card * 2 ^ ((n : ℤ) - m).toNat) ≤
      4 ^ m.toNat * 3 ^ ((n : ℤ) - m).toNat := by
  have hcard : (Finset.Icc 1 m).card = m.toNat := by
    rw [Int.card_Icc]; congr 1; omega
  have hsum : ∑ r ∈ Finset.Icc 1 m, (((n : ℤ) - r) / m).toNat =
      ((n : ℤ) - m).toNat := sum_cls_card hm
  have hprod_bound :
      ∏ r ∈ Finset.Icc 1 m,
          3 * ((g3Sets (((n : ℤ) - r) / m).toNat).card *
            2 ^ (((n : ℤ) - r) / m).toNat) ≤
        ∏ r ∈ Finset.Icc 1 m, 4 * 3 ^ (((n : ℤ) - r) / m).toNat :=
    Finset.prod_le_prod fun r _ =>
      g3Sets_card_mul_two_pow_le (((n : ℤ) - r) / m).toNat
  have hL : ∏ r ∈ Finset.Icc 1 m,
        3 * ((g3Sets (((n : ℤ) - r) / m).toNat).card *
          2 ^ (((n : ℤ) - r) / m).toNat) =
      3 ^ m.toNat *
        ((∏ r ∈ Finset.Icc 1 m, (g3Sets (((n : ℤ) - r) / m).toNat).card) *
          2 ^ ((n : ℤ) - m).toNat) := by
    rw [← hsum, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
      Finset.prod_const, hcard, Finset.prod_pow_eq_pow_sum]
  have hR : ∏ r ∈ Finset.Icc 1 m, 4 * 3 ^ (((n : ℤ) - r) / m).toNat =
      4 ^ m.toNat * 3 ^ ((n : ℤ) - m).toNat := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, hcard,
      Finset.prod_pow_eq_pow_sum, hsum]
  have hC := card_powerset_filter_shiftFree2_Icc_le (n := n) hm
  calc 3 ^ m.toNat *
        (((Finset.Icc (m + 1) (n : ℤ)).powerset.filter
          (shiftFree2 m (2 * m))).card * 2 ^ ((n : ℤ) - m).toNat)
      ≤ 3 ^ m.toNat *
        ((∏ r ∈ Finset.Icc 1 m,
            (g3Sets (((n : ℤ) - r) / m).toNat).card) *
          2 ^ ((n : ℤ) - m).toNat) :=
        Nat.mul_le_mul (le_refl _) (Nat.mul_le_mul hC (le_refl _))
    _ = ∏ r ∈ Finset.Icc 1 m,
          3 * ((g3Sets (((n : ℤ) - r) / m).toNat).card *
            2 ^ (((n : ℤ) - r) / m).toNat) := hL.symm
    _ ≤ ∏ r ∈ Finset.Icc 1 m, 4 * 3 ^ (((n : ℤ) - r) / m).toNat :=
        hprod_bound
    _ = 4 ^ m.toNat * 3 ^ ((n : ℤ) - m).toNat := hR

/-- Combined bound for the (empty) `s = 2m` second-minimum class: the
injection into double-shift-free subsets also gives the class
factorisation bound directly. -/
theorem secondMinClass_two_mul_card_le_prod {n : ℕ} {m : ℤ} (_hm : 1 ≤ m) :
    (secondMinClass n m (2 * m)).card ≤
      ∏ r ∈ Finset.Icc 1 m, (g3Sets (((n : ℤ) - r) / m).toNat).card := by
  rw [secondMinClass_two_mul_card]
  exact Nat.zero_le _

end JSP000728
