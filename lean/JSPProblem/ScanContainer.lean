import JSPProblem.ContainerBuild
import Mathlib.Algebra.Ring.Int.Parity

/-!
# JSP-000728 — the scan container

A refinement of `JSPProblem.ContainerBuild`: instead of blocking `x` by the
*earlier fingerprint elements* `T ∩ {1,…,x−1}` only (which leaves `C(∅) =
{1,…,n}` dense), the **scan** blocks `x` by the *container-so-far* — every
element `1,…,x−1` that already survived the scan, fingerprint member or not.

## The construction

`scanAux T k` is built by induction on `k`: `scanAux T 0 = ∅`, and `k + 1` is
adjoined to `scanAux T k` iff `k + 1 ∈ T` or `k + 1` is not blocked by the
container-so-far (`x` is *blocked by* `S` when `x = a + b` for some
`a, b ∈ S`).  Then `scanContainer n T = scanAux T n`.

Because `scanAux T k ⊆ {1,…,k}` and later steps only add elements `> k`, the
container-so-far seen at step `x` is exactly `scanContainer n T ∩ {1,…,x−1}`
(`scanAux_inter_Icc`), which is what makes the membership characterisation
`mem_scanContainer` honest.

## What the scan buys for free

Every Schur triple `(a, b, c)` of `scanContainer n T` has `a, b ≥ 1`, hence
`a, b < c`, hence `a, b ∈ scanContainer n T ∩ {1,…,c−1}` — so `c` was blocked
at its step and can only lie in the container because `c ∈ T`
(`scanContainer_triples_top_mem`).  Consequently each triple is determined by
its top `c ∈ T` and one fiber `a ∈ {1,…,n}`, giving

  `schurTripleCount (scanContainer n T) ≤ T.card * n`
  (`schurTripleCount_scanContainer_le`).

A `δn`-sized fingerprint therefore yields a `δn²`-sparse container *for free* —
the scan turns fingerprint smallness directly into container sparsity, with no
supersaturation input.

## The scan fingerprint and the honest gap

Running the same scan with `I` itself in the "always include" role produces
`scanContainer n I ⊇ I ∩ {1,…,n}`; the elements of `I` that entered the
container *because they were blocked* form the **scan fingerprint**
`scanFingerprint n I`.  The scans of `I` and of `scanFingerprint n I` make
identical decisions at every step (`scanAux_scanFingerprint`), so
`scanContainer n (scanFingerprint n I) = scanContainer n I` covers `I`
(`subset_scanContainer_scanFingerprint`), and every fingerprint element is the
top of a container Schur triple
(`scanFingerprint_card_le_triples`).

**The remaining gap is real.**  `SmallScanFingerprint n k` — every sum-free
`I ⊆ {1,…,n}` has scan fingerprint of size `≤ k` — is *not* provable from the
scan alone: for `I = {⌊n/2⌋+1,…,n}` the scan first admits all odd numbers
`≤ n/2` (odd `x` can never be a sum of two odds), after which every *even*
`x ∈ I` is blocked (`x = 1 + (x−1)`), forcing `≈ n/4` elements into the
fingerprint.  The genuine BLST18 fingerprint machinery (randomised/greedy
fingerprints, supersaturation) is needed to get `k = δn`.  What this file
proves unconditionally is the conditional reduction
`SmallScanFingerprint → ScanContainerExists`
(`scanContainerExists_of_smallScanFingerprint`) and its eventual form
`exists_sparse_containerFamily_of_eventualSmallScanFingerprint`: *if* every
sum-free set has a `δn` scan fingerprint, the family
`{scanContainer n T : T ⊆ {1,…,n}, |T| ≤ δn}` is a genuine container family
that is exponentially few (`scanContainerFamily_card_le_two_rpow`, via
`smallPowersetCard_le_two_rpow`) and `δn²`-sparse.

As a sanity check that the scan is already sparser than `containerOf`:
`scanContainer n ∅` is exactly the set of *odd* elements of `{1,…,n}`
(`mem_scanContainer_empty`), in particular sum-free
(`isSumFree_scanContainer_empty`), whereas `containerOf n ∅ = {1,…,n}`.

## Contents

* `scanAux`, `scanContainer`, `mem_scanAux_succ`, `scanAux_inter_Icc`,
  `mem_scanContainer` — the construction and its membership characterisation.
* `scanContainer_triples_top_mem`, `schurTripleCount_scanContainer_le` —
  every container Schur triple has its top in `T`; hence `≤ |T|·n` triples.
* `mem_scanContainer_empty`, `isSumFree_scanContainer_empty` — `C(∅)` = odds.
* `scanFingerprint`, `mem_scanFingerprint`, `scanAux_scanFingerprint`,
  `scanContainer_scanFingerprint`, `subset_scanContainer_scanFingerprint`,
  `scanFingerprint_card_le_triples` — the fingerprint and coverage.
* `SmallScanFingerprint`, `EventualSmallScanFingerprint`,
  `scanContainerFamily`, `scanContainerFamily_isContainerFamily`,
  `scanContainerFamily_sparse`, `scanContainerFamily_card_le_two_rpow`,
  `ScanContainerExists`,
  `scanContainerExists_of_smallScanFingerprint`,
  `exists_sparse_containerFamily_of_eventualSmallScanFingerprint` — the
  conditional container lemma.
-/

namespace JSP000728

open Filter

/-! ## The scan -/

/-- `scanAux T k`: the container-so-far after scanning `1, …, k`.  The
candidate `k + 1` is adjoined iff it lies in the fingerprint `T` or is not
blocked by the container-so-far (`blockedBy C x` means `x = a + b` for some
`a, b ∈ C`). -/
def scanAux (T : Finset ℤ) : ℕ → Finset ℤ
  | 0 => ∅
  | k + 1 =>
    if ((k + 1 : ℕ) : ℤ) ∈ T ∨
        ¬ blockedBy (scanAux T k) ((k + 1 : ℕ) : ℤ)
    then insert ((k + 1 : ℕ) : ℤ) (scanAux T k)
    else scanAux T k

/-- One unfolding step of the scan, as a membership disjunction. -/
theorem mem_scanAux_succ {T : Finset ℤ} {k : ℕ} {x : ℤ} :
    x ∈ scanAux T (k + 1) ↔
      x ∈ scanAux T k ∨
        (x = ((k + 1 : ℕ) : ℤ) ∧
          (((k + 1 : ℕ) : ℤ) ∈ T ∨
            ¬ blockedBy (scanAux T k) ((k + 1 : ℕ) : ℤ))) := by
  have h : scanAux T (k + 1) =
      if ((k + 1 : ℕ) : ℤ) ∈ T ∨
          ¬ blockedBy (scanAux T k) ((k + 1 : ℕ) : ℤ)
      then insert ((k + 1 : ℕ) : ℤ) (scanAux T k)
      else scanAux T k := rfl
  rw [h]
  split_ifs with hc
  · rw [Finset.mem_insert]
    constructor
    · rintro (rfl | hx)
      · exact Or.inr ⟨rfl, hc⟩
      · exact Or.inl hx
    · rintro (hx | ⟨rfl, -⟩)
      · exact Or.inr hx
      · exact Or.inl rfl
  · constructor
    · intro hx; exact Or.inl hx
    · rintro (hx | ⟨-, hcon⟩)
      · exact hx
      · exact absurd hcon hc

/-- The scan only ever adjoins the current candidate: the `(k+1)`-st
container sits inside `insert (k+1) (scanAux T k)`. -/
theorem scanAux_subset_insert (T : Finset ℤ) (k : ℕ) :
    scanAux T (k + 1) ⊆
      insert ((k + 1 : ℕ) : ℤ) (scanAux T k) := by
  intro x hx
  rcases mem_scanAux_succ.mp hx with hx | ⟨rfl, -⟩
  · exact Finset.mem_insert_of_mem hx
  · exact Finset.mem_insert_self _ _

/-- The scan is monotone step by step. -/
theorem scanAux_mono_step (T : Finset ℤ) (k : ℕ) :
    scanAux T k ⊆ scanAux T (k + 1) :=
  fun _ hx => mem_scanAux_succ.mpr (Or.inl hx)

/-- The scan is monotone in the number of steps. -/
theorem scanAux_mono {T : Finset ℤ} {k m : ℕ} (h : k ≤ m) :
    scanAux T k ⊆ scanAux T m := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  clear h
  induction d with
  | zero => exact Finset.Subset.refl _
  | succ d ih =>
    rw [Nat.add_succ]
    exact ih.trans (scanAux_mono_step T _)

/-- Every element of `scanAux T k` lies in `{1,…,k}`. -/
theorem scanAux_subset_Icc (T : Finset ℤ) (k : ℕ) :
    scanAux T k ⊆ Finset.Icc 1 (k : ℤ) := by
  induction k with
  | zero =>
    intro x hx
    exact absurd hx (Finset.notMem_empty _)
  | succ k ih =>
    intro x hx
    have hx' := scanAux_subset_insert T k hx
    rw [Finset.mem_insert] at hx'
    rcases hx' with rfl | hx'
    · rw [Finset.mem_Icc]
      have hpos : (0 : ℤ) < ((k + 1 : ℕ) : ℤ) := by
        exact_mod_cast Nat.succ_pos k
      exact ⟨by omega, le_rfl⟩
    · have h := ih hx'
      rw [Finset.mem_Icc] at h ⊢
      exact ⟨h.1, h.2.trans (by exact_mod_cast Nat.le_succ k)⟩

/-- **Stability.**  Elements `≤ k` of the `m`-step container are exactly the
`min m k`-step container: later steps never touch `≤ k`. -/
theorem scanAux_inter_Icc (T : Finset ℤ) (m k : ℕ) :
    scanAux T m ∩ Finset.Icc 1 (k : ℤ) = scanAux T (min m k) := by
  induction m with
  | zero => simp [scanAux]
  | succ m ih =>
    by_cases hkm : k ≤ m
    · have hmin : min (m + 1) k = k :=
        min_eq_right (hkm.trans (Nat.le_succ m))
      have ihm : scanAux T m ∩ Finset.Icc 1 (k : ℤ) = scanAux T k := by
        rwa [min_eq_right hkm] at ih
      rw [hmin, ← ihm]
      apply Finset.Subset.antisymm
      · intro x hx
        rw [Finset.mem_inter] at hx
        obtain ⟨hxC, hxI⟩ := hx
        rcases mem_scanAux_succ.mp hxC with hxm | ⟨hxe, -⟩
        · exact Finset.mem_inter.mpr ⟨hxm, hxI⟩
        · exfalso
          have h1 := (Finset.mem_Icc.mp hxI).2
          rw [hxe] at h1
          have h2 : m + 1 ≤ k := by exact_mod_cast h1
          omega
      · intro x hx
        rw [Finset.mem_inter] at hx
        exact Finset.mem_inter.mpr
          ⟨scanAux_mono_step T m hx.1, hx.2⟩
    · have hmk : m + 1 ≤ k := by omega
      have hmin : min (m + 1) k = m + 1 := min_eq_left hmk
      rw [hmin]
      have hsub : scanAux T (m + 1) ⊆ Finset.Icc 1 (k : ℤ) := by
        intro x hx
        have h := scanAux_subset_Icc T (m + 1) hx
        rw [Finset.mem_Icc] at h ⊢
        have hmk' : ((m + 1 : ℕ) : ℤ) ≤ (k : ℤ) := by exact_mod_cast hmk
        exact ⟨h.1, h.2.trans hmk'⟩
      apply Finset.Subset.antisymm
      · exact Finset.inter_subset_left
      · intro x hx
        exact Finset.mem_inter.mpr ⟨hx, hsub hx⟩

/-- **Membership characterisation.**  `x ∈ scanAux T k` iff `x ∈ {1,…,k}` and
(`x ∈ T` or `x` is not blocked by the earlier elements of the container). -/
theorem mem_scanAux {T : Finset ℤ} {k : ℕ} {x : ℤ} :
    x ∈ scanAux T k ↔
      x ∈ Finset.Icc 1 (k : ℤ) ∧
        (x ∈ T ∨
          ¬ blockedBy (scanAux T k ∩ Finset.Icc 1 (x - 1)) x) := by
  constructor
  · intro hx
    have hxI := scanAux_subset_Icc T k hx
    rw [Finset.mem_Icc] at hxI
    obtain ⟨h1, hk⟩ := hxI
    refine ⟨Finset.mem_Icc.mpr ⟨h1, hk⟩, ?_⟩
    set m : ℕ := (x - 1).toNat with hm
    have hmx : (m : ℤ) = x - 1 := Int.toNat_of_nonneg (by omega)
    have hxeq : x = ((m + 1 : ℕ) : ℤ) := by push_cast; omega
    have hmk : m + 1 ≤ k := by
      have hle : ((m + 1 : ℕ) : ℤ) ≤ (k : ℤ) := by rw [← hxeq]; exact hk
      exact_mod_cast hle
    have hxm : x ∈ scanAux T (m + 1) := by
      have hmem : x ∈ scanAux T k ∩ Finset.Icc 1 ((m + 1 : ℕ) : ℤ) := by
        rw [Finset.mem_inter, Finset.mem_Icc]
        exact ⟨hx, h1, le_of_eq hxeq⟩
      rwa [scanAux_inter_Icc, min_eq_right hmk] at hmem
    rcases mem_scanAux_succ.mp hxm with hxm' | ⟨-, hcond⟩
    · have hle := scanAux_subset_Icc T m hxm'
      rw [Finset.mem_Icc] at hle
      omega
    · rw [← hxeq] at hcond
      have hcap : scanAux T k ∩ Finset.Icc 1 (x - 1) = scanAux T m := by
        rw [← hmx, scanAux_inter_Icc,
          min_eq_right (Nat.le_of_succ_le hmk)]
      rcases hcond with hT | hnb
      · exact Or.inl hT
      · exact Or.inr (by rwa [← hcap] at hnb)
  · rintro ⟨hxI, hTor⟩
    rw [Finset.mem_Icc] at hxI
    obtain ⟨h1, hk⟩ := hxI
    set m : ℕ := (x - 1).toNat with hm
    have hmx : (m : ℤ) = x - 1 := Int.toNat_of_nonneg (by omega)
    have hxeq : x = ((m + 1 : ℕ) : ℤ) := by push_cast; omega
    have hmk : m + 1 ≤ k := by
      have hle : ((m + 1 : ℕ) : ℤ) ≤ (k : ℤ) := by rw [← hxeq]; exact hk
      exact_mod_cast hle
    have hcap : scanAux T k ∩ Finset.Icc 1 (x - 1) = scanAux T m := by
      rw [← hmx, scanAux_inter_Icc,
        min_eq_right (Nat.le_of_succ_le hmk)]
    rw [hcap] at hTor
    have hxm : x ∈ scanAux T (m + 1) := by
      rw [mem_scanAux_succ]
      exact Or.inr ⟨hxeq, by rwa [hxeq] at hTor⟩
    exact scanAux_mono hmk hxm

/-! ## The scan container -/

/-- The **scan container** of `T ⊆ {1,…,n}`: scan `x = 1,…,n` left to right,
adjoining `x` iff `x ∈ T` or `x` is not a sum of two elements already in the
container. -/
def scanContainer (n : ℕ) (T : Finset ℤ) : Finset ℤ := scanAux T n

/-- `x ∈ scanContainer n T` iff `x ∈ {1,…,n}` and (`x ∈ T` or `x` is not
blocked by the earlier container elements `scanContainer n T ∩ {1,…,x−1}`). -/
theorem mem_scanContainer {n : ℕ} {T : Finset ℤ} {x : ℤ} :
    x ∈ scanContainer n T ↔
      x ∈ interval n ∧
        (x ∈ T ∨
          ¬ blockedBy (scanContainer n T ∩ Finset.Icc 1 (x - 1)) x) :=
  mem_scanAux

/-- The `containerOf`-flavoured form of the membership characterisation:
for `T ⊆ {1,…,n}`, `x ∈ scanContainer n T` iff `x ∈ T` or `x` is an
unblocked element of `{1,…,n} ∖ T`. -/
theorem mem_scanContainer' {n : ℕ} {T : Finset ℤ} {x : ℤ}
    (hT : T ⊆ interval n) :
    x ∈ scanContainer n T ↔
      x ∈ T ∨
        (x ∈ interval n ∧ x ∉ T ∧
          ¬ blockedBy (scanContainer n T ∩ Finset.Icc 1 (x - 1)) x) := by
  rw [mem_scanContainer]
  constructor
  · rintro ⟨hxn, hxT | hnb⟩
    · exact Or.inl hxT
    · by_cases hxT : x ∈ T
      · exact Or.inl hxT
      · exact Or.inr ⟨hxn, hxT, hnb⟩
  · rintro (hxT | ⟨hxn, -, hnb⟩)
    · exact ⟨hT hxT, Or.inl hxT⟩
    · exact ⟨hxn, Or.inr hnb⟩

theorem scanContainer_subset_interval (n : ℕ) (T : Finset ℤ) :
    scanContainer n T ⊆ interval n :=
  fun _ hx => (mem_scanContainer.mp hx).1

theorem subset_scanContainer {n : ℕ} {T : Finset ℤ} (hT : T ⊆ interval n) :
    T ⊆ scanContainer n T :=
  fun _x hx => mem_scanContainer.mpr ⟨hT hx, Or.inl hx⟩

/-- Every element of a scan container is at least `1`. -/
theorem one_le_mem_scanContainer {n : ℕ} {T : Finset ℤ} {x : ℤ}
    (hx : x ∈ scanContainer n T) : 1 ≤ x :=
  interval_one_le (scanContainer_subset_interval n T hx)

/-! ## Every container Schur triple has its top in the fingerprint -/

/-- **Key orientation lemma.**  If `(a, b, c)` is a Schur triple of
`scanContainer n T`, then `c ∈ T`: since `a, b ≥ 1`, both summands lie in
`{1,…,c−1}`, so `c` was blocked at its step and can only be in the container
as a fingerprint element.  No positivity hypothesis on `T` is needed: the
container is automatically a subset of `{1,…,n}`. -/
theorem scanContainer_triples_top_mem {n : ℕ} {T : Finset ℤ} {a b c : ℤ}
    (h : (a, b, c) ∈ schurTriples (scanContainer n T)) : c ∈ T := by
  rw [schurTriples, Finset.mem_filter, Finset.mem_product,
    Finset.mem_product] at h
  obtain ⟨⟨ha, hb, hc⟩, hab⟩ := h
  have hab' : a + b = c := hab
  obtain ⟨haI, -⟩ := mem_scanContainer.mp ha
  obtain ⟨hbI, -⟩ := mem_scanContainer.mp hb
  obtain ⟨-, hcor⟩ := mem_scanContainer.mp hc
  have ha1 : (1 : ℤ) ≤ a := (Finset.mem_Icc.mp haI).1
  have hb1 : (1 : ℤ) ≤ b := (Finset.mem_Icc.mp hbI).1
  have hblocked : blockedBy
      (scanContainer n T ∩ Finset.Icc 1 (c - 1)) c := by
    refine ⟨a, ?_, b, ?_, hab'⟩
    · exact Finset.mem_inter.mpr
        ⟨ha, Finset.mem_Icc.mpr ⟨ha1, by omega⟩⟩
    · exact Finset.mem_inter.mpr
        ⟨hb, Finset.mem_Icc.mpr ⟨hb1, by omega⟩⟩
  rcases hcor with hcT | hnb
  · exact hcT
  · exact absurd hblocked hnb

/-- **Free sparsity.**  A `k`-element fingerprint yields a `k·n`-sparse
container: each Schur triple is determined by its top `c ∈ T`
(`scanContainer_triples_top_mem`) and one fiber `a ∈ {1,…,n}`, so the map
`(a,b,c) ↦ (c,a)` injects the triples into `T ×ˢ {1,…,n}`. -/
theorem schurTripleCount_scanContainer_le (n : ℕ) (T : Finset ℤ) :
    schurTripleCount (scanContainer n T) ≤ T.card * n := by
  classical
  calc schurTripleCount (scanContainer n T)
      = (schurTriples (scanContainer n T)).card := rfl
    _ ≤ (T ×ˢ interval n).card := by
        apply Finset.card_le_card_of_injOn
          (fun t : ℤ × ℤ × ℤ => (t.2.2, t.1))
        · rintro ⟨a, b, c⟩ ht
          rw [Finset.mem_coe] at ht ⊢
          have hct := scanContainer_triples_top_mem ht
          rw [schurTriples, Finset.mem_filter, Finset.mem_product,
            Finset.mem_product] at ht
          obtain ⟨⟨ha, -, -⟩, -⟩ := ht
          exact Finset.mem_product.mpr
            ⟨hct, (mem_scanContainer.mp ha).1⟩
        · rintro ⟨a, b, c⟩ ht ⟨a', b', c'⟩ ht' h
          rw [Finset.mem_coe, schurTriples, Finset.mem_filter] at ht ht'
          have e1 : a + b = c := ht.2
          have e2 : a' + b' = c' := ht'.2
          have hcc : c = c' := congrArg Prod.fst h
          have haa : a = a' := congrArg Prod.snd h
          have hbb : b = b' := by omega
          rw [haa, hbb, hcc]
    _ = T.card * n := by rw [Finset.card_product, card_interval]

/-! ## The empty fingerprint: `C(∅)` is the odd numbers -/

/-- The scan admits exactly the odd elements: an odd `x` can never be a sum
of two odds (so it is never blocked), while every even `x ≥ 2` is blocked by
`1 + (x − 1)`.  Contrast with `containerOf n ∅ = interval n`: the scan
container of the empty fingerprint is already sum-free. -/
theorem mem_scanAux_empty {k : ℕ} {x : ℤ} :
    x ∈ scanAux ∅ k ↔ x ∈ Finset.Icc 1 (k : ℤ) ∧ Odd x := by
  induction k generalizing x with
  | zero =>
    have hz : scanAux (∅ : Finset ℤ) 0 = ∅ := rfl
    rw [hz]
    simp only [Finset.notMem_empty, Finset.mem_Icc, false_iff]
    rintro ⟨⟨h1, h2⟩, -⟩
    omega
  | succ k ih =>
    rw [mem_scanAux_succ]
    have hcond : ((((k + 1 : ℕ) : ℤ) ∈ (∅ : Finset ℤ)) ∨
        ¬ blockedBy (scanAux ∅ k) ((k + 1 : ℕ) : ℤ)) ↔
        ¬ Even (((k + 1 : ℕ) : ℤ)) := by
      constructor
      · rintro (h | h)
        · exact absurd h (Finset.notMem_empty _)
        · intro hE
          apply h
          -- `k + 1` even ⇒ `k` odd and `≥ 1`; then `k + 1 = 1 + k` blocks it
          obtain ⟨j, hj⟩ := hE
          have hk1 : 1 ≤ k := by
            by_contra hcon
            have hk0 : k = 0 := by omega
            subst hk0
            have hj' : (1 : ℤ) = j + j := by simpa using hj
            omega
          have hs : ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 := by
            push_cast; ring
          have hkodd : Odd ((k : ℤ)) := ⟨j - 1, by omega⟩
          refine ⟨1, ?_, (k : ℤ), ?_, ?_⟩
          · rw [ih]
            exact ⟨Finset.mem_Icc.mpr ⟨le_rfl, by exact_mod_cast hk1⟩,
              odd_one⟩
          · rw [ih]
            exact ⟨Finset.mem_Icc.mpr ⟨by exact_mod_cast hk1, le_rfl⟩,
              hkodd⟩
          · rw [hs]; ring
      · intro hodd
        refine Or.inr ?_
        rintro ⟨a, ha, b, hb, hab⟩
        rw [ih] at ha hb
        have hev : Even (((k + 1 : ℕ) : ℤ)) := by
          rw [← hab]
          exact Odd.add_odd ha.2 hb.2
        exact hodd hev
    constructor
    · rintro (hx | ⟨rfl, hc⟩)
      · rw [ih] at hx
        obtain ⟨hI, ho⟩ := hx
        rw [Finset.mem_Icc] at hI ⊢
        have hkn : (k : ℤ) ≤ ((k + 1 : ℕ) : ℤ) := by
          exact_mod_cast Nat.le_succ k
        exact ⟨⟨hI.1, hI.2.trans hkn⟩, ho⟩
      · have hpos : (0 : ℤ) < ((k + 1 : ℕ) : ℤ) := by
          exact_mod_cast Nat.succ_pos k
        exact ⟨Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩,
          Int.not_even_iff_odd.mp (hcond.mp hc)⟩
    · rintro ⟨hI, ho⟩
      rw [Finset.mem_Icc] at hI
      obtain ⟨h1, hkn⟩ := hI
      have hcase : x ≤ (k : ℤ) ∨ x = ((k + 1 : ℕ) : ℤ) := by
        have hs : ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 := by push_cast; ring
        omega
      rcases hcase with hxk | rfl
      · exact Or.inl (ih.mpr ⟨Finset.mem_Icc.mpr ⟨h1, hxk⟩, ho⟩)
      · exact Or.inr ⟨rfl, hcond.mpr (Int.not_even_iff_odd.mpr ho)⟩

/-- `scanContainer n ∅` is the set of odd elements of `{1,…,n}`. -/
theorem mem_scanContainer_empty {n : ℕ} {x : ℤ} :
    x ∈ scanContainer n ∅ ↔ x ∈ interval n ∧ Odd x :=
  mem_scanAux_empty

/-- In particular the empty fingerprint has a sum-free scan container —
already a strict improvement over `containerOf n ∅ = interval n`. -/
theorem isSumFree_scanContainer_empty (n : ℕ) :
    IsSumFree (scanContainer n ∅) := by
  intro a ha b hb hab
  have hao := (mem_scanContainer_empty.mp ha).2
  have hbo := (mem_scanContainer_empty.mp hb).2
  have hev : Even (a + b) := Odd.add_odd hao hbo
  rw [mem_scanContainer_empty] at hab
  exact Int.not_even_iff_odd.mpr hab.2 hev

/-! ## The scan fingerprint -/

/-- The **scan fingerprint** of `I`: the elements of `I ∩ {1,…,n}` that are
blocked by the container-so-far when the scan of `I` reaches them.  Equivalently
—the content of `scanAux_scanFingerprint`—these are exactly the elements of
`I` that the container of `I` cannot account for unless they are named. -/
def scanFingerprint (n : ℕ) (I : Finset ℤ) : Finset ℤ :=
  (I ∩ interval n).filter fun x =>
    blockedBy (scanContainer n I ∩ Finset.Icc 1 (x - 1)) x

theorem mem_scanFingerprint {n : ℕ} {I : Finset ℤ} {x : ℤ} :
    x ∈ scanFingerprint n I ↔
      x ∈ I ∧ x ∈ interval n ∧
        blockedBy (scanContainer n I ∩ Finset.Icc 1 (x - 1)) x := by
  simp only [scanFingerprint, Finset.mem_filter, Finset.mem_inter]
  constructor
  · rintro ⟨⟨hxI, hxn⟩, hb⟩; exact ⟨hxI, hxn, hb⟩
  · rintro ⟨hxI, hxn, hb⟩; exact ⟨⟨hxI, hxn⟩, hb⟩

theorem scanFingerprint_subset (n : ℕ) (I : Finset ℤ) :
    scanFingerprint n I ⊆ I :=
  fun _ hx => (mem_scanFingerprint.mp hx).1

theorem scanFingerprint_subset_interval (n : ℕ) (I : Finset ℤ) :
    scanFingerprint n I ⊆ interval n :=
  fun _ hx => (mem_scanFingerprint.mp hx).2.1

/-- **Scan consistency.**  Scanning `scanFingerprint n I` and scanning `I`
produce identical containers-so-far at every step `k ≤ n`: the candidate
`k + 1` lies in the fingerprint iff it lies in `I` *and* is blocked, so the
insertion conditions `x ∈ T ∨ ¬blocked` and `x ∈ I ∨ ¬blocked` coincide. -/
theorem scanAux_scanFingerprint {n : ℕ} {I : Finset ℤ} :
    ∀ {k : ℕ}, k ≤ n →
      scanAux (scanFingerprint n I) k = scanAux I k := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hk
    have hk' : k ≤ n := Nat.le_of_succ_le hk
    have hcap : scanContainer n I ∩ Finset.Icc 1 (((k + 1 : ℕ) : ℤ) - 1)
        = scanAux I k := by
      have hkk : ((k + 1 : ℕ) : ℤ) - 1 = (k : ℤ) := by push_cast; ring
      rw [hkk]
      have h := scanAux_inter_Icc I n k
      rw [min_eq_right hk'] at h
      exact h
    have hmem : ((k + 1 : ℕ) : ℤ) ∈ scanFingerprint n I ↔
        ((k + 1 : ℕ) : ℤ) ∈ I ∧
          blockedBy (scanAux I k) ((k + 1 : ℕ) : ℤ) := by
      rw [mem_scanFingerprint]
      constructor
      · rintro ⟨hxI, -, hb⟩
        exact ⟨hxI, by rwa [hcap] at hb⟩
      · rintro ⟨hxI, hb⟩
        refine ⟨hxI, ?_, by rwa [hcap]⟩
        have hpos : (0 : ℤ) < ((k + 1 : ℕ) : ℤ) := by
          exact_mod_cast Nat.succ_pos k
        have hle : ((k + 1 : ℕ) : ℤ) ≤ (n : ℤ) := by exact_mod_cast hk
        exact Finset.mem_Icc.mpr ⟨by omega, hle⟩
    have hiff : (((k + 1 : ℕ) : ℤ) ∈ scanFingerprint n I ∨
          ¬ blockedBy (scanAux I k) ((k + 1 : ℕ) : ℤ)) ↔
        (((k + 1 : ℕ) : ℤ) ∈ I ∨
          ¬ blockedBy (scanAux I k) ((k + 1 : ℕ) : ℤ)) := by
      constructor
      · rintro (hT | hnb)
        · exact Or.inl (hmem.mp hT).1
        · exact Or.inr hnb
      · rintro (hI | hnb)
        · by_cases hb : blockedBy (scanAux I k) ((k + 1 : ℕ) : ℤ)
          · exact Or.inl (hmem.mpr ⟨hI, hb⟩)
          · exact Or.inr hb
        · exact Or.inr hnb
    have hsucc : ∀ T : Finset ℤ, scanAux T (k + 1) =
        if ((k + 1 : ℕ) : ℤ) ∈ T ∨
            ¬ blockedBy (scanAux T k) ((k + 1 : ℕ) : ℤ)
        then insert ((k + 1 : ℕ) : ℤ) (scanAux T k)
        else scanAux T k := fun _ => rfl
    rw [hsucc, hsucc, ih hk']
    exact if_congr hiff rfl rfl

/-- The scan container of the fingerprint of `I` is the scan container of
`I` itself. -/
theorem scanContainer_scanFingerprint (n : ℕ) (I : Finset ℤ) :
    scanContainer n (scanFingerprint n I) = scanContainer n I :=
  scanAux_scanFingerprint le_rfl

/-- **Coverage.**  Every `I ⊆ {1,…,n}` is contained in the scan container of
its own scan fingerprint: elements of `I` are either named in the fingerprint
or survive the scan unblocked. -/
theorem subset_scanContainer_scanFingerprint {n : ℕ} {I : Finset ℤ}
    (hI : I ⊆ interval n) :
    I ⊆ scanContainer n (scanFingerprint n I) := by
  rw [scanContainer_scanFingerprint]
  intro x hx
  exact mem_scanContainer.mpr ⟨hI hx, Or.inl hx⟩

/-- Every fingerprint element is the top of a Schur triple of the container:
`x` was blocked by `a, b ∈ scanContainer n I ∩ {1,…,x−1}`, and `x` itself lies
in `scanContainer n I` because `x ∈ I ∩ {1,…,n}`.  Hence
`|scanFingerprint n I| ≤ schurTripleCount (scanContainer n I)` by projecting
each triple to its top. -/
theorem scanFingerprint_card_le_triples (n : ℕ) (I : Finset ℤ) :
    (scanFingerprint n I).card ≤
      schurTripleCount (scanContainer n I) := by
  have hsub : scanFingerprint n I ⊆
      (schurTriples (scanContainer n I)).image (fun t => t.2.2) := by
    intro x hx
    rw [mem_scanFingerprint] at hx
    obtain ⟨hxI, hxn, a, ha, b, hb, hab⟩ := hx
    rw [Finset.mem_image]
    refine ⟨(a, b, x), ?_, rfl⟩
    rw [schurTriples, Finset.mem_filter, Finset.mem_product,
      Finset.mem_product]
    refine ⟨⟨(Finset.mem_inter.mp ha).1, (Finset.mem_inter.mp hb).1, ?_⟩,
      hab⟩
    exact mem_scanContainer.mpr ⟨hxn, Or.inl hxI⟩
  exact (Finset.card_le_card hsub).trans Finset.card_image_le

/-! ## The conditional container family -/

/-- **Small scan-fingerprint hypothesis** at granularity `k`: every sum-free
subset of `{1,…,n}` has scan fingerprint of size at most `k`.  This is the
fingerprint-existence input that the bare scan *cannot* deliver (see the file
header: `I = {⌊n/2⌋+1,…,n}` forces `≈ n/4` elements into the fingerprint); it
is kept as an explicit hypothesis. -/
def SmallScanFingerprint (n k : ℕ) : Prop :=
  ∀ I : Finset ℤ, I ⊆ interval n → IsSumFree I →
    (scanFingerprint n I).card ≤ k

/-- **Eventual form**: for every `δ > 0`, eventually every sum-free subset of
`{1,…,n}` has scan fingerprint of size at most `⌊δ·n⌋`.  This is the precise
statement the BLST18 fingerprint machinery must supply. -/
def EventualSmallScanFingerprint : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in Filter.atTop,
    SmallScanFingerprint n ⌊δ * (n : ℝ)⌋₊

/-- The **scan container family** at granularity `k`: the scan containers of
all fingerprints `T ⊆ {1,…,n}` of size at most `k`. -/
def scanContainerFamily (n k : ℕ) : Finset (Finset ℤ) :=
  ((interval n).powerset.filter fun T => T.card ≤ k).image
    (scanContainer n)

theorem mem_scanContainerFamily {n k : ℕ} {C : Finset ℤ} :
    C ∈ scanContainerFamily n k ↔
      ∃ T : Finset ℤ, T ⊆ interval n ∧ T.card ≤ k ∧
        scanContainer n T = C := by
  simp only [scanContainerFamily, Finset.mem_image, Finset.mem_filter,
    Finset.mem_powerset]
  constructor
  · rintro ⟨T, ⟨hTn, hTk⟩, rfl⟩
    exact ⟨T, hTn, hTk, rfl⟩
  · rintro ⟨T, hTn, hTk, rfl⟩
    exact ⟨T, ⟨hTn, hTk⟩, rfl⟩

/-- The family has at most as many containers as `k`-element subsets of
`{1,…,n}`. -/
theorem scanContainerFamily_card_le (n k : ℕ) :
    (scanContainerFamily n k).card ≤
      ((interval n).powerset.filter fun T => T.card ≤ k).card :=
  Finset.card_image_le

/-- Every container in the family is `k·n`-sparse: `|T| ≤ k` implies
`schurTripleCount (scanContainer n T) ≤ |T|·n ≤ k·n`. -/
theorem scanContainerFamily_sparse {n k : ℕ} {C : Finset ℤ}
    (hC : C ∈ scanContainerFamily n k) :
    schurTripleCount C ≤ k * n := by
  obtain ⟨T, -, hTk, rfl⟩ := mem_scanContainerFamily.mp hC
  exact (schurTripleCount_scanContainer_le n T).trans
    (Nat.mul_le_mul_right n hTk)

/-- **Conditional container family.**  Under `SmallScanFingerprint n k`, the
scan containers of `k`-element fingerprints form a genuine container family:
each lies inside `{1,…,n}` and each sum-free `I` is covered by the container
of its own fingerprint. -/
theorem scanContainerFamily_isContainerFamily {n k : ℕ}
    (h : SmallScanFingerprint n k) :
    IsContainerFamily n (scanContainerFamily n k) := by
  refine ⟨?_, ?_⟩
  · intro C hC
    obtain ⟨T, -, -, rfl⟩ := mem_scanContainerFamily.mp hC
    exact scanContainer_subset_interval n T
  · intro s hs hsf
    exact ⟨scanContainer n (scanFingerprint n s),
      mem_scanContainerFamily.mpr
        ⟨scanFingerprint n s, scanFingerprint_subset_interval n s,
          h s hs hsf, rfl⟩,
      subset_scanContainer_scanFingerprint hs⟩

/-- The scan container family at fingerprint size `⌊δ·n⌋` is subexponential:
`#F ≤ #{T ⊆ {1,…,n} : |T| ≤ ⌊δn⌋} ≤ 2^{εn}` for `δ` small, eventually. -/
theorem scanContainerFamily_card_le_two_rpow {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n : ℕ in Filter.atTop,
      ((scanContainerFamily n ⌊δ * (n : ℝ)⌋₊).card : ℝ) ≤
        (2 : ℝ) ^ (ε * (n : ℝ)) := by
  obtain ⟨δ, hδ, hδf⟩ := smallPowersetCard_le_two_rpow hε
  refine ⟨δ, hδ, hδf.mono fun n hn => ?_⟩
  have h := scanContainerFamily_card_le n ⌊δ * (n : ℝ)⌋₊
  have h' : ((scanContainerFamily n ⌊δ * (n : ℝ)⌋₊).card : ℝ) ≤
      (((interval n).powerset.filter
        fun T => T.card ≤ ⌊δ * (n : ℝ)⌋₊).card : ℝ) := by
    exact_mod_cast h
  exact h'.trans hn

/-- **The packaged gap.**  `ScanContainerExists n k` asserts the existence of
a container family for `{1,…,n}` which is as small as the `k`-subsets and
`k·n`-sparse — the output the container method needs at `k = δn`. -/
def ScanContainerExists (n k : ℕ) : Prop :=
  ∃ F : Finset (Finset ℤ), IsContainerFamily n F ∧
    F.card ≤
      ((interval n).powerset.filter fun T => T.card ≤ k).card ∧
    ∀ C ∈ F, schurTripleCount C ≤ k * n

/-- **The conditional reduction.**  If every sum-free subset of `{1,…,n}` has
a scan fingerprint of size `≤ k`, then `ScanContainerExists n k` holds —
witnessed by `scanContainerFamily n k`. -/
theorem scanContainerExists_of_smallScanFingerprint {n k : ℕ}
    (h : SmallScanFingerprint n k) : ScanContainerExists n k :=
  ⟨scanContainerFamily n k, scanContainerFamily_isContainerFamily h,
    scanContainerFamily_card_le n k,
    fun _ hC => scanContainerFamily_sparse hC⟩

/-- **The eventual conditional reduction.**  Under
`EventualSmallScanFingerprint`, for every `ε > 0` there is eventually a
container family for `{1,…,n}` that is exponentially few
(`F.card ≤ 2^{εn}`) and `εn²`-sparse
(`schurTripleCount C ≤ ε·n²` for every `C ∈ F`). -/
theorem exists_sparse_containerFamily_of_eventualSmallScanFingerprint
    (h : EventualSmallScanFingerprint) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∃ F : Finset (Finset ℤ), IsContainerFamily n F ∧
        (F.card : ℝ) ≤ (2 : ℝ) ^ (ε * (n : ℝ)) ∧
        ∀ C ∈ F, (schurTripleCount C : ℝ) ≤ ε * (n : ℝ) * (n : ℝ) := by
  obtain ⟨δ, hδ, hδf⟩ := scanContainerFamily_card_le_two_rpow hε
  set δ' := min δ ε with hδ'
  have hδ'pos : 0 < δ' := lt_min hδ hε
  have hδ'δ : δ' ≤ δ := min_le_left _ _
  have hδ'ε : δ' ≤ ε := min_le_right _ _
  filter_upwards [hδf, h δ' hδ'pos] with n hn hδn
  refine ⟨scanContainerFamily n ⌊δ' * (n : ℝ)⌋₊,
    scanContainerFamily_isContainerFamily hδn, ?_, ?_⟩
  · have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hfloor : ⌊δ' * (n : ℝ)⌋₊ ≤ ⌊δ * (n : ℝ)⌋₊ :=
      Nat.floor_le_floor
        (mul_le_mul_of_nonneg_right hδ'δ hn0)
    have hmono :
        (interval n).powerset.filter
          (fun T => T.card ≤ ⌊δ' * (n : ℝ)⌋₊) ⊆
        (interval n).powerset.filter
          (fun T => T.card ≤ ⌊δ * (n : ℝ)⌋₊) := by
      intro T hT
      rw [Finset.mem_filter] at hT ⊢
      exact ⟨hT.1, hT.2.trans hfloor⟩
    have hsub : scanContainerFamily n ⌊δ' * (n : ℝ)⌋₊ ⊆
        scanContainerFamily n ⌊δ * (n : ℝ)⌋₊ :=
      Finset.image_subset_image hmono
    calc ((scanContainerFamily n ⌊δ' * (n : ℝ)⌋₊).card : ℝ)
        ≤ ((scanContainerFamily n ⌊δ * (n : ℝ)⌋₊).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
      _ ≤ (2 : ℝ) ^ (ε * (n : ℝ)) := hn
  · intro C hC
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hfl : (⌊δ' * (n : ℝ)⌋₊ : ℝ) ≤ δ' * (n : ℝ) :=
      Nat.floor_le (mul_nonneg hδ'pos.le hn0)
    have hsparse : (schurTripleCount C : ℝ) ≤
        (⌊δ' * (n : ℝ)⌋₊ : ℝ) * (n : ℝ) := by
      exact_mod_cast scanContainerFamily_sparse hC
    calc (schurTripleCount C : ℝ)
        ≤ (⌊δ' * (n : ℝ)⌋₊ : ℝ) * (n : ℝ) := hsparse
      _ ≤ (δ' * (n : ℝ)) * (n : ℝ) :=
          mul_le_mul_of_nonneg_right hfl hn0
      _ ≤ ε * (n : ℝ) * (n : ℝ) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hδ'ε hn0) hn0

end JSP000728
