import JSPProblem.Containers
import JSPProblem.FingerprintCount
import JSPProblem.Obstruction

/-!
# JSP-000728 — the fingerprint container construction

The deterministic map from *fingerprints* to *containers* at the heart of the
Balogh–Morris–Samotij / Green container method for sum-free sets.

## The construction

A fingerprint is a small set `T ⊆ {1,…,n}`.  Its container `containerOf n T`
consists of `T` together with every `x ∈ {1,…,n} ∖ T` that is *not blocked by
the earlier fingerprint elements* `T ∩ {1,…,x−1}`, where `x` is blocked by a
set `S` when `x = a + b` for some `a, b ∈ S`.

Only the "sum" obstruction `a + b = x` needs to be scanned: for a positive
`S` the other three insertion obstructions of `IsSumFree.insert_iff`
(`a + x ∈ S`, `x + a ∈ S`, `x + x ∈ S`) involve elements `> x`, so they can
never fire inside `T ∩ {1,…,x−1}`.  This is exactly what makes the scan
sound (`containerOf_covers`): for a sum-free `I ⊇ T` and `x ∈ I ∖ T`, any
`a, b ∈ T ∩ {1,…,x−1}` with `a + b = x` would form a Schur triple inside the
sum-free `I` — impossible — so `x` survives the scan and `I ⊆ C(T)`.

## Contents

* `blockedBy`, `containerOf`, `mem_containerOf` — the construction.
* `containerOf_covers` — coverage of sum-free supersets.
* `containerOf_triples_avoid`, `schurTriples_containerOf_subset`,
  `schurTripleCount_containerOf_le` — a Schur triple of `C(T)` whose top
  lies outside `T` cannot have both summands in `T`; quantitatively
  `schurTripleCount (C(T)) ≤ schurTripleCount T + 2·|C(T) ∖ T|·|C(T)|`.
* `SmallFingerprint`, `containerFamily`, `mem_containerFamily`,
  `containerFamily_card_le`, `containerFamily_isContainerFamily_of_fingerprint`,
  `containerFamily_card_le_two_rpow` — the family of containers of all
  `k`-element fingerprints: at most as many containers as `k`-subsets of
  `{1,…,n}` (subexponential for `k = ⌊δn⌋` by
  `smallPowersetCard_le_two_rpow`), and a genuine container family *provided*
  every sum-free set admits a `k`-element fingerprint — the
  fingerprint-existence input, kept as the explicit hypothesis
  `SmallFingerprint`.
-/

namespace JSP000728

open Filter

/-! ## The blocking relation -/

/-- `x` is *blocked* by `S` when `x` is a sum `a + b` of two elements of
`S` (with `a = b` permitted).  Evaluated on `S = T ∩ {1,…,x−1}` this is the
only insertion obstruction a left-to-right scan can detect: the other three
obstructions of `IsSumFree.insert_iff` (`a + x ∈ S`, `x + a ∈ S`,
`x + x ∈ S`) involve elements `> x` whenever `S` is positive. -/
def blockedBy (S : Finset ℤ) (x : ℤ) : Prop :=
  ∃ a ∈ S, ∃ b ∈ S, a + b = x

instance decidableBlockedBy (S : Finset ℤ) (x : ℤ) :
    Decidable (blockedBy S x) := by
  unfold blockedBy
  infer_instance

theorem blockedBy.mono {S T : Finset ℤ} (hST : S ⊆ T) {x : ℤ}
    (h : blockedBy S x) : blockedBy T x := by
  obtain ⟨a, ha, b, hb, hab⟩ := h
  exact ⟨a, hST ha, b, hST hb, hab⟩

theorem not_blockedBy_empty (x : ℤ) : ¬ blockedBy ∅ x := by
  rintro ⟨a, ha, -, -, -⟩
  exact Finset.notMem_empty a ha

/-- Blocking is a genuine obstruction: adjoining a blocked element destroys
sum-freeness. -/
theorem not_isSumFree_insert_of_blockedBy {S : Finset ℤ} {x : ℤ}
    (h : blockedBy S x) : ¬ IsSumFree (insert x S) := by
  obtain ⟨a, ha, b, hb, hab⟩ := h
  intro hsf
  exact hsf a (Finset.mem_insert_of_mem ha) b (Finset.mem_insert_of_mem hb)
    (by rw [hab]; exact Finset.mem_insert_self x S)

/-! ## The container of a fingerprint -/

/-- The **container of a fingerprint** `T` inside `{1,…,n}`: `T` itself,
together with every `x ∈ {1,…,n} ∖ T` that is not blocked by the earlier
elements `T ∩ {1,…,x−1}` of `T`. -/
def containerOf (n : ℕ) (T : Finset ℤ) : Finset ℤ :=
  T ∪ (interval n).filter fun x =>
    x ∉ T ∧ ¬ blockedBy (T ∩ Finset.Icc 1 (x - 1)) x

/-- Membership characterisation: `x ∈ C(T)` iff `x ∈ T`, or `x` lies in
`{1,…,n} ∖ T` and is not blocked by the earlier elements of `T`. -/
theorem mem_containerOf {n : ℕ} {T : Finset ℤ} {x : ℤ} :
    x ∈ containerOf n T ↔
      x ∈ T ∨
        (x ∈ interval n ∧ x ∉ T ∧
          ¬ blockedBy (T ∩ Finset.Icc 1 (x - 1)) x) := by
  simp only [containerOf, Finset.mem_union, Finset.mem_filter]

theorem subset_containerOf (n : ℕ) (T : Finset ℤ) : T ⊆ containerOf n T :=
  Finset.subset_union_left

theorem containerOf_subset_interval {n : ℕ} {T : Finset ℤ}
    (hT : T ⊆ interval n) : containerOf n T ⊆ interval n := by
  intro x hx
  rw [mem_containerOf] at hx
  rcases hx with hxT | ⟨hxI, -, -⟩
  · exact hT hxT
  · exact hxI

theorem one_le_of_mem_containerOf {n : ℕ} {T : Finset ℤ}
    (hT : ∀ a ∈ T, 1 ≤ a) {x : ℤ} (hx : x ∈ containerOf n T) :
    1 ≤ x := by
  rw [mem_containerOf] at hx
  rcases hx with hxT | ⟨hxI, -, -⟩
  · exact hT x hxT
  · exact interval_one_le hxI

theorem not_mem_containerOf_of_blockedBy {n : ℕ} {T : Finset ℤ} {x : ℤ}
    (hxT : x ∉ T) (h : blockedBy (T ∩ Finset.Icc 1 (x - 1)) x) :
    x ∉ containerOf n T := by
  rw [mem_containerOf]
  rintro (hx | ⟨-, -, hnb⟩)
  · exact hxT hx
  · exact hnb h

/-- The empty fingerprint blocks nothing, so its container is the whole
interval. -/
theorem containerOf_empty (n : ℕ) : containerOf n ∅ = interval n := by
  ext x
  simp [mem_containerOf, blockedBy]

/-! ## Coverage -/

/-- **Coverage theorem.**  Every sum-free `I ⊆ {1,…,n}` containing the
fingerprint `T` is contained in `C(T)`: an `x ∈ I ∖ T` cannot be the sum of
two earlier elements of `T ⊆ I`, for that would be a Schur triple inside
the sum-free `I`. -/
theorem containerOf_covers {n : ℕ} {I T : Finset ℤ}
    (hI : I ⊆ interval n) (hIsf : IsSumFree I) (hT : T ⊆ I) :
    I ⊆ containerOf n T := by
  intro x hx
  rw [mem_containerOf]
  by_cases hxT : x ∈ T
  · exact Or.inl hxT
  · refine Or.inr ⟨hI hx, hxT, ?_⟩
    rintro ⟨a, ha, b, hb, hab⟩
    exact hIsf a (hT (Finset.mem_inter.mp ha).1)
      b (hT (Finset.mem_inter.mp hb).1) (by rw [hab]; exact hx)

/-! ## Schur triples inside the container -/

/-- **Orientation lemma.**  A Schur triple `(a, b, c)` of `C(T)` with
`c ∉ T` cannot have both summands in `T` (provided the fingerprint is
positive): `a, b ∈ T` with `a + b = c` forces `a, b < c`, so `c` would have
been blocked by `T ∩ {1,…,c−1}` and excluded from the container. -/
theorem containerOf_triples_avoid {n : ℕ} {T : Finset ℤ}
    (hT : ∀ a ∈ T, 1 ≤ a) {a b c : ℤ}
    (h : (a, b, c) ∈ schurTriples (containerOf n T)) (hc : c ∉ T) :
    a ∉ T ∨ b ∉ T := by
  rw [schurTriples, Finset.mem_filter, Finset.mem_product,
    Finset.mem_product] at h
  obtain ⟨⟨haC, hbC, hcC⟩, hab⟩ := h
  have hab' : a + b = c := hab
  rcases mem_containerOf.mp hcC with hcT | ⟨-, -, hnb⟩
  · exact absurd hcT hc
  by_contra hcon
  push Not at hcon
  obtain ⟨haT, hbT⟩ := hcon
  have ha1 : 1 ≤ a := hT a haT
  have hb1 : 1 ≤ b := hT b hbT
  have haI : a ∈ T ∩ Finset.Icc 1 (c - 1) := by
    rw [Finset.mem_inter, Finset.mem_Icc]
    exact ⟨haT, ha1, by omega⟩
  have hbI : b ∈ T ∩ Finset.Icc 1 (c - 1) := by
    rw [Finset.mem_inter, Finset.mem_Icc]
    exact ⟨hbT, hb1, by omega⟩
  exact hnb ⟨a, haI, b, hbI, hab'⟩

/-- **Structural split.**  Every Schur triple of `C(T)` is either entirely
inside the fingerprint `T`, or has its first summand outside `T`, or its
second summand outside `T`. -/
theorem schurTriples_containerOf_subset {n : ℕ} {T : Finset ℤ}
    (hT : ∀ a ∈ T, 1 ≤ a) :
    schurTriples (containerOf n T) ⊆
      schurTriples T ∪
        (((containerOf n T \ T) ×ˢ
            (containerOf n T ×ˢ containerOf n T)).filter
          fun t : ℤ × ℤ × ℤ => t.1 + t.2.1 = t.2.2) ∪
        ((containerOf n T ×ˢ
            ((containerOf n T \ T) ×ˢ containerOf n T)).filter
          fun t : ℤ × ℤ × ℤ => t.1 + t.2.1 = t.2.2) := by
  rintro ⟨a, b, c⟩ ht
  have htr := ht
  rw [schurTriples, Finset.mem_filter, Finset.mem_product,
    Finset.mem_product] at htr
  obtain ⟨⟨haC, hbC, hcC⟩, hab⟩ := htr
  have hab' : a + b = c := hab
  rw [Finset.mem_union, Finset.mem_union]
  by_cases haT : a ∈ T
  · by_cases hbT : b ∈ T
    · left; left
      have hcT : c ∈ T := by
        by_contra hcT
        rcases containerOf_triples_avoid hT ht hcT with hna | hnb
        · exact hna haT
        · exact hnb hbT
      rw [schurTriples, Finset.mem_filter, Finset.mem_product,
        Finset.mem_product]
      exact ⟨⟨haT, hbT, hcT⟩, hab'⟩
    · right
      rw [Finset.mem_filter, Finset.mem_product, Finset.mem_product,
        Finset.mem_sdiff]
      exact ⟨⟨haC, ⟨hbC, hbT⟩, hcC⟩, hab'⟩
  · left; right
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_product,
      Finset.mem_sdiff]
    exact ⟨⟨⟨haC, haT⟩, hbC, hcC⟩, hab'⟩

/-- Fiber bound: Schur triples `(a, b, c)` with `a ∈ A` and `b, c ∈ B` are
determined by the pair `(a, c)`, so there are at most `|A|·|B|` of them. -/
theorem card_schurTriples_fst_le (A B : Finset ℤ) :
    ((A ×ˢ (B ×ˢ B)).filter
        fun t : ℤ × ℤ × ℤ => t.1 + t.2.1 = t.2.2).card ≤
      A.card * B.card := by
  calc ((A ×ˢ (B ×ˢ B)).filter
        fun t : ℤ × ℤ × ℤ => t.1 + t.2.1 = t.2.2).card
      ≤ (A ×ˢ B).card := by
        apply Finset.card_le_card_of_injOn
          (fun t : ℤ × ℤ × ℤ => (t.1, t.2.2))
        · rintro ⟨a, b, c⟩ ht
          rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_product,
            Finset.mem_product] at ht
          obtain ⟨⟨haA, -, hcB⟩, -⟩ := ht
          exact Finset.mem_coe.mpr (Finset.mem_product.mpr ⟨haA, hcB⟩)
        · rintro ⟨a, b, c⟩ ht ⟨a', b', c'⟩ ht' h
          rw [Finset.mem_coe, Finset.mem_filter] at ht ht'
          have e1 : a + b = c := ht.2
          have e2 : a' + b' = c' := ht'.2
          have haa : a = a' := congrArg Prod.fst h
          have hcc : c = c' := congrArg Prod.snd h
          subst haa hcc
          have hb : b = b' := by omega
          rw [hb]
    _ = A.card * B.card := Finset.card_product _ _

/-- Fiber bound: Schur triples `(a, b, c)` with `b ∈ A` and `a, c ∈ B` are
determined by the pair `(b, c)`, so there are at most `|A|·|B|` of them. -/
theorem card_schurTriples_snd_le (A B : Finset ℤ) :
    ((B ×ˢ (A ×ˢ B)).filter
        fun t : ℤ × ℤ × ℤ => t.1 + t.2.1 = t.2.2).card ≤
      A.card * B.card := by
  calc ((B ×ˢ (A ×ˢ B)).filter
        fun t : ℤ × ℤ × ℤ => t.1 + t.2.1 = t.2.2).card
      ≤ (A ×ˢ B).card := by
        apply Finset.card_le_card_of_injOn
          (fun t : ℤ × ℤ × ℤ => (t.2.1, t.2.2))
        · rintro ⟨a, b, c⟩ ht
          rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_product,
            Finset.mem_product] at ht
          obtain ⟨⟨-, hbA, hcB⟩, -⟩ := ht
          exact Finset.mem_coe.mpr (Finset.mem_product.mpr ⟨hbA, hcB⟩)
        · rintro ⟨a, b, c⟩ ht ⟨a', b', c'⟩ ht' h
          rw [Finset.mem_coe, Finset.mem_filter] at ht ht'
          have e1 : a + b = c := ht.2
          have e2 : a' + b' = c' := ht'.2
          have hbb : b = b' := congrArg Prod.fst h
          have hcc : c = c' := congrArg Prod.snd h
          subst hbb hcc
          have ha : a = a' := by omega
          rw [ha]
    _ = A.card * B.card := Finset.card_product _ _

/-- **Container Schur-triple count.**  The Schur triples of `C(T)` are the
triples internal to the fingerprint plus those with a summand outside `T`,
each of the latter being fixed by its off-fingerprint summand and its top:
`schurTripleCount (C(T)) ≤ schurTripleCount T + 2·|C(T) ∖ T|·|C(T)|`. -/
theorem schurTripleCount_containerOf_le {n : ℕ} {T : Finset ℤ}
    (hT : ∀ a ∈ T, 1 ≤ a) :
    schurTripleCount (containerOf n T) ≤
      schurTripleCount T +
        2 * ((containerOf n T \ T).card * (containerOf n T).card) := by
  calc schurTripleCount (containerOf n T)
      = (schurTriples (containerOf n T)).card := rfl
    _ ≤ (schurTriples T ∪
          (((containerOf n T \ T) ×ˢ
              (containerOf n T ×ˢ containerOf n T)).filter
            fun t : ℤ × ℤ × ℤ => t.1 + t.2.1 = t.2.2) ∪
          ((containerOf n T ×ˢ
              ((containerOf n T \ T) ×ˢ containerOf n T)).filter
            fun t : ℤ × ℤ × ℤ => t.1 + t.2.1 = t.2.2)).card :=
        Finset.card_le_card (schurTriples_containerOf_subset hT)
    _ ≤ (schurTriples T).card +
          (((containerOf n T \ T) ×ˢ
              (containerOf n T ×ˢ containerOf n T)).filter
            fun t : ℤ × ℤ × ℤ => t.1 + t.2.1 = t.2.2).card +
          ((containerOf n T ×ˢ
              ((containerOf n T \ T) ×ˢ containerOf n T)).filter
            fun t : ℤ × ℤ × ℤ => t.1 + t.2.1 = t.2.2).card := by
        refine (Finset.card_union_le _ _).trans ?_
        exact Nat.add_le_add_right (Finset.card_union_le _ _) _
    _ ≤ schurTripleCount T +
          ((containerOf n T \ T).card * (containerOf n T).card) +
          ((containerOf n T \ T).card * (containerOf n T).card) := by
        refine Nat.add_le_add (Nat.add_le_add_left ?_ _) ?_
        · exact card_schurTriples_fst_le _ _
        · exact card_schurTriples_snd_le _ _
    _ = schurTripleCount T +
          2 * ((containerOf n T \ T).card * (containerOf n T).card) := by
        ring

/-! ## The container family -/

/-- **Small fingerprint hypothesis** at granularity `k`: every sum-free
subset of `{1,…,n}` contains a fingerprint `T` of at most `k` elements.
This is the fingerprint-existence input of the container lemma (the actual
BMS/Green kernel), kept here as an explicit hypothesis. -/
def SmallFingerprint (n k : ℕ) : Prop :=
  ∀ I : Finset ℤ, I ⊆ interval n → IsSumFree I →
    ∃ T : Finset ℤ, T ⊆ I ∧ T.card ≤ k

/-- The **container family** at granularity `k`: the containers of all
fingerprints `T ⊆ {1,…,n}` of size at most `k`. -/
def containerFamily (n k : ℕ) : Finset (Finset ℤ) :=
  ((interval n).powerset.filter fun T => T.card ≤ k).image (containerOf n)

theorem mem_containerFamily {n k : ℕ} {C : Finset ℤ} :
    C ∈ containerFamily n k ↔
      ∃ T : Finset ℤ, T ⊆ interval n ∧ T.card ≤ k ∧
        containerOf n T = C := by
  simp only [containerFamily, Finset.mem_image, Finset.mem_filter,
    Finset.mem_powerset]
  constructor
  · rintro ⟨T, ⟨hTn, hTk⟩, rfl⟩
    exact ⟨T, hTn, hTk, rfl⟩
  · rintro ⟨T, hTn, hTk, rfl⟩
    exact ⟨T, ⟨hTn, hTk⟩, rfl⟩

/-- The family has at most as many containers as `k`-element subsets of
`{1,…,n}`: the map `T ↦ C(T)` need not be injective, but its image is no
larger than its domain. -/
theorem containerFamily_card_le (n k : ℕ) :
    (containerFamily n k).card ≤
      ((interval n).powerset.filter fun T => T.card ≤ k).card :=
  Finset.card_image_le

/-- **Conditional container family.**  Under `SmallFingerprint n k`, the
containers of `k`-element fingerprints form a container family: each
container lies inside `{1,…,n}`, and each sum-free `I` is covered by
`C(T)` for its fingerprint `T ⊆ I` (`containerOf_covers`). -/
theorem containerFamily_isContainerFamily_of_fingerprint {n k : ℕ}
    (h : SmallFingerprint n k) :
    IsContainerFamily n (containerFamily n k) := by
  refine ⟨?_, ?_⟩
  · intro C hC
    obtain ⟨T, hTn, -, rfl⟩ := mem_containerFamily.mp hC
    exact containerOf_subset_interval hTn
  · intro s hs hsf
    obtain ⟨T, hTs, hTk⟩ := h s hs hsf
    exact ⟨containerOf n T,
      mem_containerFamily.mpr ⟨T, hTs.trans hs, hTk, rfl⟩,
      containerOf_covers hs hsf hTs⟩

/-- The container family at fingerprint size `⌊δ·n⌋` is subexponential:
`#F ≤ #{T ⊆ {1,…,n} : |T| ≤ ⌊δn⌋} ≤ 2^{εn}` for `δ` small, eventually. -/
theorem containerFamily_card_le_two_rpow {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n : ℕ in Filter.atTop,
      ((containerFamily n ⌊δ * (n : ℝ)⌋₊).card : ℝ) ≤
        (2 : ℝ) ^ (ε * (n : ℝ)) := by
  obtain ⟨δ, hδ, hδf⟩ := smallPowersetCard_le_two_rpow hε
  refine ⟨δ, hδ, hδf.mono fun n hn => ?_⟩
  have h := containerFamily_card_le n ⌊δ * (n : ℝ)⌋₊
  have h' : ((containerFamily n ⌊δ * (n : ℝ)⌋₊).card : ℝ) ≤
      (((interval n).powerset.filter
        fun T => T.card ≤ ⌊δ * (n : ℝ)⌋₊).card : ℝ) := by
    exact_mod_cast h
  exact h'.trans hn

end JSP000728
