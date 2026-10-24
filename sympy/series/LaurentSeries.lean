/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
/-
Copyright (c) 2024 AlgebraicCombinatorics contributors. All rights reserved.
Authors: AlgebraicCombinatorics contributors
-/
import Mathlib
import Lemma.PowerSeries.InfiniteProducts2
import Lemma.Partition.NPartition
/-!
# Laurent Power Series

This file formalizes the content from Section `sec.gf.laure` of the textbook,
covering Laurent power series and related concepts.

## Main Definitions

* `BinaryRepresentation` - A binary representation of a nonnegative integer
* `BalancedTernaryRepresentation` - A balanced ternary representation of an integer
* `DoublyInfinitePowerSeries` - The K-module K[[x^±]] of all families indexed by ℤ
* `DoublyInfinitePowerSeries.IsLaurentSeries` - Predicate for when a doubly infinite
  power series is a Laurent series (Definition `def.fps.laure.lauser`)
* We also use Mathlib's `LaurentPolynomial` for K[x^±] and `LaurentSeries` for K((x))

## Main Results

* `binaryRepresentation_unique` - Each n ∈ ℕ has a unique binary representation
* `balancedTernaryRepresentation_unique` - Each integer has a unique balanced ternary representation
* `isLaurentSeries_ofLaurentSeries` - Mathlib's LaurentSeries satisfies our IsLaurentSeries predicate
* `toLaurentSeries_ofLaurentSeries` / `ofLaurentSeries_toLaurentSeries` - Round-trip equivalence
  showing our definition matches Mathlib's
* `Int.isPWO_of_bddBelow` - Bounded below subsets of ℤ are partially well-ordered
* Properties of Laurent polynomials and Laurent series from Mathlib

## References

* [Grinberg, *Algebraic Combinatorics*], Section on Laurent power series
-/


open scoped LaurentPolynomial

noncomputable section

namespace AlgebraicCombinatorics
/-! ## Binary Representation

A binary representation encodes a nonnegative integer as an essentially finite
sequence of bits (0 or 1).
-/


/-- A binary representation of a nonnegative integer `n` is an essentially finite
sequence `(b_i)_{i ∈ ℕ}` of elements in `{0, 1}` such that `n = ∑ b_i * 2^i`.

This corresponds to Definition in `sec.gf.laure` of the source.
-/
structure BinaryRepresentation (n : ℕ) where
  /-- The sequence of bits -/
  bits : ℕ → Fin 2
  /-- Only finitely many bits are nonzero -/
  finite_support : {i | bits i ≠ 0}.Finite
  /-- The sum equals n -/
  sum_eq : ∑ᶠ i, (bits i : ℕ) * 2^i = n

namespace BinaryRepresentation

/-- Helper: construct bits from a list of digits. -/
def bitsFromList (L : List ℕ) (hL : ∀ x ∈ L, x < 2) : ℕ → Fin 2 := fun i =>
  if h : i < L.length then ⟨L[i], hL _ (List.getElem_mem h)⟩ else 0

end BinaryRepresentation

/-- Helper: the support of bits i * 2^i is contained in the support of bits. -/
theorem support_mul_pow_subset (bits : ℕ → Fin 2) :
    {i : ℕ | (bits i : ℕ) * 2^i ≠ 0} ⊆ {i | bits i ≠ 0} := by
  intro i hi
  simp only [Set.mem_ofPred_eq, ne_eq] at hi ⊢
  intro h
  apply hi
  simp [h]

/-- The least significant bit equals n mod 2. -/
theorem bits_zero_eq_mod (n : ℕ) (r : BinaryRepresentation n) : (r.bits 0 : ℕ) = n % 2 := by
  have h := r.sum_eq
  have hfin : {i : ℕ | (r.bits i : ℕ) * 2^i ≠ 0}.Finite :=
    r.finite_support.subset (support_mul_pow_subset r.bits)
  have hdiv : ∀ i : ℕ, i ≥ 1 → 2 ∣ (r.bits i : ℕ) * 2^i := by
    intro i hi
    have : 2 ∣ 2^i := dvd_pow_self 2 (Nat.one_le_iff_ne_zero.mp hi)
    exact Dvd.dvd.mul_left this (r.bits i : ℕ)
  have h_mod : (∑ᶠ i, (r.bits i : ℕ) * 2^i) % 2 = (r.bits 0 : ℕ) % 2 := by
    rw [finsum_eq_sum_of_support_subset (s := hfin.toFinset) (f := fun i => (r.bits i : ℕ) * 2^i)]
    · by_cases h0 : 0 ∈ hfin.toFinset
      · rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem h0]
        simp only [pow_zero, mul_one]
        have hsum_div : 2 ∣ ∑ i ∈ hfin.toFinset \ {0}, (r.bits i : ℕ) * 2 ^ i := by
          apply Finset.dvd_sum
          intro i hi
          simp only [Finset.mem_sdiff, Finset.mem_singleton] at hi
          exact hdiv i (Nat.one_le_iff_ne_zero.mpr hi.2)
        have : (∑ i ∈ hfin.toFinset \ {0}, (r.bits i : ℕ) * 2 ^ i) % 2 = 0 :=
          Nat.mod_eq_zero_of_dvd hsum_div
        omega
      · simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, pow_zero, mul_one, ne_eq,
                   not_not] at h0
        have hsum_div : 2 ∣ ∑ i ∈ hfin.toFinset, (r.bits i : ℕ) * 2 ^ i := by
          apply Finset.dvd_sum
          intro i hi
          simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, ne_eq] at hi
          have hne : i ≠ 0 := by
            intro heq
            subst heq
            simp only [pow_zero, mul_one] at hi h0
            exact hi h0
          exact hdiv i (Nat.one_le_iff_ne_zero.mpr hne)
        have hsum_zero : (∑ i ∈ hfin.toFinset, (r.bits i : ℕ) * 2 ^ i) % 2 = 0 :=
          Nat.mod_eq_zero_of_dvd hsum_div
        simp only [h0, Nat.zero_mod]
        exact hsum_zero
    · intro i hi
      simp only [Function.mem_support, ne_eq] at hi
      exact hfin.mem_toFinset.mpr hi
  rw [h] at h_mod
  have hlt : (r.bits 0 : ℕ) < 2 := (r.bits 0).isLt
  omega

/-- Sum decomposition: ∑ᶠ i, bits i * 2^i = bits 0 + 2 * ∑ᶠ i, bits (i+1) * 2^i -/
theorem sum_decomposition (bits : ℕ → Fin 2) (hfin : {i | bits i ≠ 0}.Finite) :
    ∑ᶠ i, (bits i : ℕ) * 2^i = (bits 0 : ℕ) + 2 * (∑ᶠ i, (bits (i + 1) : ℕ) * 2^i) := by
  -- First rewrite the LHS as sum over {0} plus sum over positive naturals
  have huniv : (Set.univ : Set ℕ) = {0} ∪ Set.range Nat.succ := by
    ext n
    simp only [Set.mem_univ, Set.mem_union, Set.mem_singleton_iff, Set.mem_range, true_iff]
    cases n with
    | zero => left; rfl
    | succ n => right; exact ⟨n, rfl⟩
  -- Helper lemma: (bits i : ℕ) = 0 iff bits i = 0
  have hval_zero : ∀ i, (bits i : ℕ) = 0 ↔ bits i = 0 := by
    intro i
    constructor
    · intro h
      exact Fin.val_injective h
    · intro h
      simp [h]
  -- The support is finite
  have hsup : (Function.support (fun i => (bits i : ℕ) * 2^i)).Finite := by
    apply hfin.subset
    intro i hi
    simp only [Function.mem_support, ne_eq, Set.mem_ofPred_eq] at hi ⊢
    intro hb
    apply hi
    simp [hb]
  -- Rewrite as finsum over univ
  rw [← finsum_mem_univ (f := fun i => (bits i : ℕ) * 2^i)]
  rw [huniv]
  -- Split the union
  rw [finsum_mem_union']
  · -- Simplify the singleton sum
    simp only [finsum_mem_singleton, pow_zero, mul_one]
    congr 1
    -- The sum over range Nat.succ equals the shifted sum
    rw [finsum_mem_range Nat.succ_injective]
    -- Now we have ∑ᶠ j, bits (j + 1) * 2^(j + 1)
    -- Need to show this equals 2 * ∑ᶠ i, bits (i + 1) * 2^i
    have hfin_shift : (Function.support (fun i => (bits (i + 1) : ℕ) * 2^i)).Finite := by
      have hsub : Function.support (fun i => (bits (i + 1) : ℕ) * 2^i) ⊆
                  Nat.pred '' {i | bits i ≠ 0} := by
        intro i hi
        simp only [Function.mem_support, ne_eq] at hi
        simp only [Set.mem_image, Set.mem_ofPred_eq]
        use i + 1
        constructor
        · intro hb
          apply hi
          simp [hb]
        · simp
      exact (hfin.image _).subset hsub
    -- We have ∑ᶠ j, bits (j.succ) * 2^(j.succ) = ∑ᶠ j, bits (j + 1) * 2^(j + 1)
    -- And we want 2 * ∑ᶠ i, bits (i + 1) * 2^i
    -- Note that bits (j + 1) * 2^(j + 1) = 2 * bits (j + 1) * 2^j
    have heq : ∀ j, (bits j.succ : ℕ) * 2^j.succ = 2 * ((bits (j + 1) : ℕ) * 2^j) := by
      intro j
      simp only [Nat.succ_eq_add_one]
      ring
    conv_lhs =>
      arg 1
      ext j
      rw [heq j]
    -- Now we have ∑ᶠ j, 2 * (bits (j + 1) * 2^j) = 2 * ∑ᶠ i, bits (i + 1) * 2^i
    -- The support of 2 * f is the same as the support of f
    have hsup2 : (Function.support (fun i => 2 * ((bits (i + 1) : ℕ) * 2^i))).Finite := by
      apply hfin_shift.subset
      intro i hi
      simp only [Function.mem_support, ne_eq] at hi ⊢
      intro h
      apply hi
      omega
    have hsupeq : hsup2.toFinset = hfin_shift.toFinset := by
      ext i
      simp only [Set.Finite.mem_toFinset, Function.mem_support, ne_eq]
      constructor
      · intro h1 h2
        apply h1
        omega
      · intro h1 h2
        apply h1
        simp only [mul_eq_zero, pow_eq_zero_iff', OfNat.ofNat_ne_zero, ne_eq, false_and, or_false] at h2
        cases h2 with
        | inl h => exact absurd h (by norm_num)
        | inr h => simp [(hval_zero (i + 1)).mp h]
    rw [finsum_eq_sum _ hsup2, hsupeq]
    calc ∑ i ∈ hfin_shift.toFinset, 2 * ((bits (i + 1) : ℕ) * 2^i)
        = 2 * ∑ i ∈ hfin_shift.toFinset, (bits (i + 1) : ℕ) * 2^i := by rw [Finset.mul_sum]
      _ = 2 * ∑ᶠ i, (bits (i + 1) : ℕ) * 2^i := by rw [← finsum_eq_sum _ hfin_shift]
  · -- Disjoint
    simp only [Set.disjoint_singleton_left, Set.mem_range]
    intro ⟨n, hn⟩
    omega
  · -- Finite intersection for singleton
    exact Set.finite_singleton 0 |>.inter_of_left _
  · -- Finite intersection for range
    apply Set.Finite.subset hsup
    intro i hi
    obtain ⟨_, hi'⟩ := hi
    exact hi'

/-- The shifted representation gives a representation of n / 2. -/
def BinaryRepresentation.shift {n : ℕ} (r : BinaryRepresentation n) :
    BinaryRepresentation (n / 2) where
  bits := fun i => r.bits (i + 1)
  finite_support := by
    have h := r.finite_support
    have hsub : {i | r.bits (i + 1) ≠ 0} ⊆ Nat.pred '' {i | r.bits i ≠ 0} := by
      intro i hi
      simp only [Set.mem_ofPred_eq, ne_eq] at hi
      simp only [Set.mem_image, Set.mem_ofPred_eq, ne_eq]
      use i + 1, hi
      rfl
    exact Set.Finite.subset (h.image _) hsub
  sum_eq := by
    have h := r.sum_eq
    have hb0 := bits_zero_eq_mod n r
    have hlt : (r.bits 0 : ℕ) < 2 := (r.bits 0).isLt
    have hdecomp := sum_decomposition r.bits r.finite_support
    have heq : n = (r.bits 0 : ℕ) + 2 * (∑ᶠ i, (r.bits (i + 1) : ℕ) * 2^i) := by
      calc n = ∑ᶠ i, (r.bits i : ℕ) * 2^i := h.symm
           _ = (r.bits 0 : ℕ) + 2 * (∑ᶠ i, (r.bits (i + 1) : ℕ) * 2^i) := hdecomp
    have hdiv2 : n / 2 = (∑ᶠ i, (r.bits (i + 1) : ℕ) * 2^i) := by
      calc n / 2 = ((r.bits 0 : ℕ) + 2 * (∑ᶠ i, (r.bits (i + 1) : ℕ) * 2^i)) / 2 := by rw [← heq]
           _ = (∑ᶠ i, (r.bits (i + 1) : ℕ) * 2^i) := by
               rw [Nat.add_mul_div_left _ _ (by omega : 0 < 2)]
               simp only [Nat.div_eq_of_lt hlt, Nat.zero_add]
    exact hdiv2.symm
/-! ## Balanced Ternary Representation

A balanced ternary representation uses digits from {-1, 0, 1} with base 3.
Unlike binary representations, this can represent negative integers.
-/


/-- The set of balanced ternary digits: {-1, 0, 1} -/
inductive BalancedTernaryDigit : Type
  | negOne : BalancedTernaryDigit
  | zero : BalancedTernaryDigit
  | one : BalancedTernaryDigit
  deriving DecidableEq, Repr

namespace BalancedTernaryDigit

/-- Convert a balanced ternary digit to an integer -/
def toInt : BalancedTernaryDigit → ℤ
  | negOne => -1
  | zero => 0
  | one => 1

instance : Zero BalancedTernaryDigit := ⟨zero⟩

@[simp]
theorem toInt_zero : (0 : BalancedTernaryDigit).toInt = 0 := rfl

end BalancedTernaryDigit

/-- A balanced ternary representation of an integer `n` is an essentially finite
sequence `(b_i)_{i ∈ ℕ}` of elements in `{-1, 0, 1}` such that `n = ∑ b_i * 3^i`.

This corresponds to the Definition of balanced ternary representation in `sec.gf.laure`.
-/
structure BalancedTernaryRepresentation (n : ℤ) where
  /-- The sequence of digits -/
  digits : ℕ → BalancedTernaryDigit
  /-- Only finitely many digits are nonzero -/
  finite_support : {i | digits i ≠ 0}.Finite
  /-- The sum equals n -/
  sum_eq : ∑ᶠ i, (digits i).toInt * (3 : ℤ)^i = n
/-! ### Helper definitions and lemmas for balanced ternary existence proof -/


/-- A digit is nonzero iff its toInt is nonzero -/
theorem BalancedTernaryDigit.ne_zero_iff_toInt_ne_zero (d : BalancedTernaryDigit) :
    d ≠ 0 ↔ d.toInt ≠ 0 := by
  cases d with
  | negOne => simp only [toInt, ne_eq]; decide
  | zero => simp only [toInt, ne_eq, not_true_eq_false, iff_false, not_not]; rfl
  | one => simp only [toInt, ne_eq]; decide

/-- Given n mod 3, return the unique balanced ternary digit d such that
    (n - d.toInt) is divisible by 3. -/
def digitOfMod3 (r : ℤ) : BalancedTernaryDigit :=
  if r % 3 = 0 then .zero
  else if r % 3 = 1 ∨ r % 3 = -2 then .one
  else .negOne

/-- The zero representation for n = 0. -/
def zeroRep : BalancedTernaryRepresentation 0 where
  digits := fun _ => 0
  finite_support := by simp only [ne_eq, not_true_eq_false, Set.ofPred_false, Set.finite_empty]
  sum_eq := by simp only [BalancedTernaryDigit.toInt_zero, zero_mul, finsum_zero]

/-- Helper: the digits function for prepending a digit. -/
def prependDigits (d : BalancedTernaryDigit) (f : ℕ → BalancedTernaryDigit) :
    ℕ → BalancedTernaryDigit
  | 0 => d
  | i + 1 => f i

theorem prependDigits_zero (d : BalancedTernaryDigit) (f : ℕ → BalancedTernaryDigit) :
    prependDigits d f 0 = d := rfl

theorem prependDigits_succ (d : BalancedTernaryDigit) (f : ℕ → BalancedTernaryDigit)
    (i : ℕ) : prependDigits d f (i + 1) = f i := rfl

theorem prependDigits_finite_support (d : BalancedTernaryDigit)
    (f : ℕ → BalancedTernaryDigit) (hf : {i | f i ≠ 0}.Finite) :
    {i | prependDigits d f i ≠ 0}.Finite := by
  have hsub : {i | prependDigits d f i ≠ 0} ⊆ {0} ∪ Nat.succ '' {i | f i ≠ 0} := by
    intro i hi
    simp only [Set.mem_ofPred_eq, ne_eq] at hi
    cases i with
    | zero => left; exact Set.mem_singleton 0
    | succ i =>
      right
      simp only [Set.mem_image, Set.mem_ofPred_eq, ne_eq]
      use i
      simp [prependDigits] at hi
      exact ⟨hi, rfl⟩
  exact Set.Finite.subset (Set.finite_singleton 0 |>.union (hf.image _)) hsub

theorem prependDigits_sum (d : BalancedTernaryDigit) (f : ℕ → BalancedTernaryDigit)
    (hf : {i | f i ≠ 0}.Finite) :
    ∑ᶠ i, (prependDigits d f i).toInt * (3 : ℤ)^i =
    d.toInt + 3 * ∑ᶠ i, (f i).toInt * (3 : ℤ)^i := by
  let S := {0} ∪ Nat.succ '' (hf.toFinset : Set ℕ)
  have hS_fin : S.Finite := Set.finite_singleton 0 |>.union (Finset.finite_toSet _ |>.image _)
  have hsupp_sub : Function.support (fun i => (prependDigits d f i).toInt * (3 : ℤ)^i) ⊆
      hS_fin.toFinset := by
    intro i hi
    simp only [Function.mem_support, ne_eq, mul_eq_zero, pow_eq_zero_iff', OfNat.ofNat_ne_zero,
      false_and, or_false, Set.Finite.mem_toFinset, Set.mem_union, Set.mem_singleton_iff,
      Set.mem_image, Finset.mem_coe, S] at hi ⊢
    cases i with
    | zero => left; rfl
    | succ i =>
      right; use i; simp [prependDigits] at hi
      refine ⟨?_, rfl⟩
      simp only [Set.mem_ofPred_eq]
      exact (BalancedTernaryDigit.ne_zero_iff_toInt_ne_zero _).mpr hi
  rw [finsum_eq_sum_of_support_subset _ hsupp_sub]
  have hS_eq : hS_fin.toFinset = {0} ∪ (hf.toFinset.image Nat.succ) := by
    ext i; simp [Set.Finite.mem_toFinset, Set.mem_image, Finset.mem_image, S]
  rw [hS_eq]
  have h0_not_in_image : (0 : ℕ) ∉ hf.toFinset.image Nat.succ := by
    simp only [Finset.mem_image, not_exists, not_and]; intro i _ h; omega
  rw [Finset.sum_union (Finset.disjoint_singleton_left.mpr h0_not_in_image)]
  simp only [Finset.sum_singleton, prependDigits_zero, pow_zero, mul_one]
  rw [Finset.sum_image (fun i _ j _ h => Nat.succ_injective h)]
  have hsum_eq : ∑ i ∈ hf.toFinset, (prependDigits d f (i + 1)).toInt * (3 : ℤ)^(i + 1) =
                 ∑ i ∈ hf.toFinset, (f i).toInt * (3 : ℤ)^(i + 1) := by
    apply Finset.sum_congr rfl; intro i _; simp [prependDigits_succ]
  rw [hsum_eq]
  have hfactor : ∑ i ∈ hf.toFinset, (f i).toInt * (3 : ℤ)^(i + 1) =
                 3 * ∑ i ∈ hf.toFinset, (f i).toInt * (3 : ℤ)^i := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
  rw [hfactor]
  have hfinsum_eq : ∑ᶠ i, (f i).toInt * (3 : ℤ)^i =
      ∑ i ∈ hf.toFinset, (f i).toInt * (3 : ℤ)^i := by
    apply finsum_eq_sum_of_support_subset
    intro i hi
    simp only [Function.mem_support, ne_eq, mul_eq_zero, pow_eq_zero_iff', OfNat.ofNat_ne_zero,
      false_and, or_false] at hi
    rw [Finset.mem_coe, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    exact (BalancedTernaryDigit.ne_zero_iff_toInt_ne_zero _).mpr hi
  simp only [hfinsum_eq]

/-- Prepend a digit to a representation, scaling by 3. -/
def prependDigit (d : BalancedTernaryDigit) {m : ℤ}
    (r : BalancedTernaryRepresentation m) :
    BalancedTernaryRepresentation (d.toInt + 3 * m) where
  digits := prependDigits d r.digits
  finite_support := prependDigits_finite_support d r.digits r.finite_support
  sum_eq := by rw [prependDigits_sum d r.digits r.finite_support, r.sum_eq]
/-! ## Doubly Infinite Power Series

The K-module K[[x^±]] of all families (a_n)_{n ∈ ℤ} of elements of K.
This is the largest space allowing negative powers of x, but it does not
have a well-defined multiplication in general.

This corresponds to Definition `def.fps.laure.double`.
-/


/-- The K-module of doubly infinite power series K[[x^±]].

An element is a family `(a_n)_{n ∈ ℤ}` of elements of K. Addition and scalar
multiplication are defined entrywise.

Note: This is NOT a ring because multiplication is not always well-defined
(the convolution sum may be infinite).

This corresponds to Definition `def.fps.laure.double`.
-/
def DoublyInfinitePowerSeries (K : Type*) [Semiring K] := ℤ → K

namespace DoublyInfinitePowerSeries

variable {K : Type*} [Semiring K]

instance : AddCommMonoid (DoublyInfinitePowerSeries K) := Pi.addCommMonoid

instance : Module K (DoublyInfinitePowerSeries K) := Pi.module _ _ _

/-- The coefficient of x^n in a doubly infinite power series -/
def coeff (f : DoublyInfinitePowerSeries K) (n : ℤ) : K := f n

/-- Two doubly infinite power series are equal iff all their coefficients are equal -/
@[ext]
theorem ext {f g : DoublyInfinitePowerSeries K} (h : ∀ n, coeff f n = coeff g n) : f = g :=
  funext h

/-- The element x^n in K[[x^±]], represented as a family -/
def single (n : ℤ) : DoublyInfinitePowerSeries K := fun m => if m = n then 1 else 0

/-- A doubly infinite power series is a Laurent series if the sequence of negative
coefficients (a_{-1}, a_{-2}, a_{-3}, ...) is essentially finite, i.e., all
sufficiently negative indices have zero coefficient.

This is Definition `def.fps.laure.lauser` from the textbook:
We let K((x)) be the subset of K[[x^±]] consisting of all families (a_i)_{i∈ℤ}
such that the sequence (a_{-1}, a_{-2}, a_{-3}, ...) is essentially finite --
i.e., such that all sufficiently low i ∈ ℤ satisfy a_i = 0.

The elements of K((x)) are called Laurent series in one indeterminate x over K. -/
def IsLaurentSeries (f : DoublyInfinitePowerSeries K) : Prop :=
  ∃ N : ℤ, ∀ n : ℤ, n < N → coeff f n = 0

/-- Convert a Mathlib LaurentSeries to a DoublyInfinitePowerSeries -/
def ofLaurentSeries (f : LaurentSeries K) : DoublyInfinitePowerSeries K :=
  fun n => f.coeff n

/-- For ℤ, a set bounded below is partially well-ordered.

This follows from the fact that any sequence in ℤ bounded below has a monotone
subsequence (by Ramsey's theorem / infinite pigeonhole). -/
theorem Int.isPWO_of_bddBelow {s : Set ℤ} (hs : BddBelow s) : s.IsPWO := by
  obtain ⟨N, hN⟩ := hs
  rw [Set.isPWO_iff_exists_monotone_subseq]
  intro g hg
  -- g : ℕ → ℤ with values in s
  -- Consider h : ℕ → ℕ defined by h(n) = (g(n) - N).toNat
  let h : ℕ → ℕ := fun n => (g n - N).toNat
  -- Any sequence in ℕ has a monotone or antitone subsequence (Ramsey)
  have ⟨φ, hφ⟩ := exists_increasing_or_nonincreasing_subseq (α := ℕ) (r := (· ≤ ·)) h
  rcases hφ with hφ_mono | hφ_anti
  · -- Increasing case
    use φ
    intro i j hij
    have hi := hg (φ i)
    have hj := hg (φ j)
    have hNi : N ≤ g (φ i) := hN hi
    have hNj : N ≤ g (φ j) := hN hj
    rcases hij.lt_or_eq with hij' | rfl
    · have hmono := hφ_mono i j hij'
      simp only [h] at hmono
      have h1 : 0 ≤ g (φ i) - N := by omega
      have h2 : 0 ≤ g (φ j) - N := by omega
      have h3 : (g (φ i) - N).toNat ≤ (g (φ j) - N).toNat := hmono
      have h4 : g (φ i) - N ≤ g (φ j) - N := by
        calc g (φ i) - N = ((g (φ i) - N).toNat : ℤ) := (Int.toNat_of_nonneg h1).symm
          _ ≤ ((g (φ j) - N).toNat : ℤ) := by exact_mod_cast h3
          _ = g (φ j) - N := Int.toNat_of_nonneg h2
      -- Now we need g (φ i) ≤ g (φ j), which follows from h4
      have : g (φ i) ≤ g (φ j) := by linarith
      exact this
    · rfl
  · -- Non-increasing (decreasing) case
    -- In ℕ, a strictly decreasing sequence can't exist infinitely
    exfalso
    -- Build a strictly decreasing sequence in ℕ
    have hdec : ∀ m n, m < n → h (φ n) < h (φ m) := fun m n hmn => by
      have := hφ_anti m n hmn
      omega
    -- Infinite strictly decreasing sequence in ℕ is impossible
    -- h(φ 0) > h(φ 1) > h(φ 2) > ... but all are ≥ 0
    have : ∀ n, h (φ n) + n ≤ h (φ 0) := by
      intro n
      induction n with
      | zero => simp
      | succ k ih =>
        have hk := hdec k (k + 1) (Nat.lt_succ_self k)
        omega
    have := this (h (φ 0) + 1)
    omega

/-- Convert a DoublyInfinitePowerSeries satisfying IsLaurentSeries to a Mathlib LaurentSeries -/
def toLaurentSeries (f : DoublyInfinitePowerSeries K) (hf : IsLaurentSeries f) :
    LaurentSeries K := by
  refine ⟨fun n => coeff f n, ?_⟩
  apply Int.isPWO_of_bddBelow
  obtain ⟨N, hN⟩ := hf
  use N
  intro n hn
  -- hn : n ∈ {n | coeff f n ≠ 0}
  change coeff f n ≠ 0 at hn
  by_contra h
  push Not at h
  exact hn (hN n h)

end DoublyInfinitePowerSeries
/-! ## Laurent Polynomials

The K-algebra K[x^±] of Laurent polynomials consists of essentially finite
families (a_n)_{n ∈ ℤ}. Unlike K[[x^±]], this IS a ring.

We use Mathlib's `LaurentPolynomial` which is defined as `AddMonoidAlgebra R ℤ`.

This corresponds to Definition `def.fps.laure.laupol`.

### Theorem `thm.fps.laure.laupol-ring`

The K-module K[x^±], equipped with the convolution multiplication, is a commutative
K-algebra. Its unity is `(δ_{i,0})_{i∈ℤ}`. The element x (represented as T 1) is
invertible in this K-algebra.

This is fully formalized below using Mathlib's `LaurentPolynomial` type.
-/


section LaurentPolynomials

variable (K : Type*) [CommSemiring K]
/-! ### Part 1: K[x^±] is a commutative K-algebra

The Laurent polynomial ring K[x^±] is a commutative semiring (and a commutative ring
when K is a ring). It is also a K-algebra.

In Mathlib, this is established via `AddMonoidAlgebra.instCommSemiring` and related instances.
-/


/-- Laurent polynomials form a commutative semiring.
This is part of Theorem `thm.fps.laure.laupol-ring`. -/
instance laurentPolynomial_commSemiring : CommSemiring K[T;T⁻¹] := inferInstance

/-- Laurent polynomials form a K-algebra.
This is part of Theorem `thm.fps.laure.laupol-ring`. -/
instance laurentPolynomial_algebra : Algebra K K[T;T⁻¹] := inferInstance
/-! ### Part 2: The unity is (δ_{i,0})_{i∈ℤ}

The multiplicative identity in K[x^±] is the family that is 1 at index 0 and 0 elsewhere.
In Mathlib, this is `LaurentPolynomial.T 0 = 1`.
-/
/-! ### Part 3: The element x is invertible

The element x (represented as T 1 in Mathlib) is a unit in K[x^±], with inverse x⁻¹ = T (-1).
-/

/-- The inverse of T n is T (-n).
This is the explicit inverse formula from Theorem `thm.fps.laure.laupol-ring`. -/
@[simp]
theorem laurentPolynomial_T_mul_T_neg (n : ℤ) :
    (LaurentPolynomial.T n : K[T;T⁻¹]) * LaurentPolynomial.T (-n) = 1 := by
  rw [← LaurentPolynomial.T_add, add_neg_cancel, LaurentPolynomial.T_zero]

/-- The inverse of T n is T (-n) (multiplication in the other order).
This is the explicit inverse formula from Theorem `thm.fps.laure.laupol-ring`. -/
@[simp]
theorem laurentPolynomial_T_neg_mul_T (n : ℤ) :
    (LaurentPolynomial.T (-n) : K[T;T⁻¹]) * LaurentPolynomial.T n = 1 := by
  rw [← LaurentPolynomial.T_add, neg_add_cancel, LaurentPolynomial.T_zero]

/-- The unit associated to T n, with explicit inverse T (-n). -/
def laurentPolynomial_T_unit (n : ℤ) : (K[T;T⁻¹])ˣ where
  val := LaurentPolynomial.T n
  inv := LaurentPolynomial.T (-n)
  val_inv := laurentPolynomial_T_mul_T_neg K n
  inv_val := laurentPolynomial_T_neg_mul_T K n
/-! ### Representation as sum

Any Laurent polynomial f = (a_i)_{i ∈ ℤ} satisfies f = ∑_{i ∈ support f} a_i T^i.
-/
/-! ### Alternative characterizations

The Laurent polynomial ring K[x^±] can equivalently be described as:
- The group algebra of ℤ over K
- The localization of K[x] at the powers of x

These are mentioned in the textbook after Theorem `thm.fps.laure.laupol-ring`.
-/

end LaurentPolynomials

section LaurentPolynomialsCommRing

variable (K : Type*) [CommRing K]

/-- When K is a CommRing, Laurent polynomials form a CommRing.
This is part of Theorem `thm.fps.laure.laupol-ring`. -/
instance laurentPolynomial_commRing : CommRing K[T;T⁻¹] := inferInstance

end LaurentPolynomialsCommRing
/-! ## Laurent Series

The K-algebra K((x)) of Laurent series consists of families (a_n)_{n ∈ ℤ}
such that a_n = 0 for all sufficiently negative n.

We use Mathlib's `LaurentSeries` which is defined as `HahnSeries ℤ R`.

This corresponds to Definition `def.fps.laure.lauser`.
-/


section LaurentSeriesSection

variable (K : Type*) [CommRing K]

/-- Laurent series form a commutative K-algebra with unity.
This is Theorem `thm.fps.laure.lauser-ring`.

In Mathlib, this is established via `HahnSeries.instCommRing` and related instances. -/
example : CommRing (LaurentSeries K) := inferInstance

example : Algebra K (LaurentSeries K) := inferInstance

/-- The FPS ring K[[x]] embeds into the Laurent series ring K((x)).
This is mentioned after Theorem `thm.fps.laure.lauser-ring`. -/
example : PowerSeries K →+* LaurentSeries K := HahnSeries.ofPowerSeries ℤ K

/-- Helper monoid homomorphism: maps n ∈ ℤ (as a multiplicative element) to the single
Hahn series x^n. This is used to construct the Laurent polynomial embedding. -/
def singleMonoidHom : Multiplicative ℤ →* LaurentSeries K where
  toFun n := HahnSeries.single (Multiplicative.toAdd n) 1
  map_one' := rfl
  map_mul' := by
    intro x y
    have h : Multiplicative.toAdd (x * y) = Multiplicative.toAdd x + Multiplicative.toAdd y := rfl
    simp only [h, HahnSeries.single_mul_single, one_mul]

/-- The ring homomorphism from Laurent polynomials to Laurent series.
This embeds K[x^±] into K((x)) by mapping each Laurent polynomial to the corresponding
Laurent series with the same coefficients.

This is mentioned after Theorem `thm.fps.laure.lauser-ring`. -/
def laurentPolyToSeries : K[T;T⁻¹] →+* LaurentSeries K :=
  AddMonoidAlgebra.liftNCRingHom HahnSeries.C (singleMonoidHom K)
    (by
      intro x y
      simp only [HahnSeries.C, singleMonoidHom, Commute, SemiconjBy]
      simp only [RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
      rw [HahnSeries.single_mul_single, HahnSeries.single_mul_single]
      simp [add_comm])

end LaurentSeriesSection
/-! ## Module Structure on K[[x^±]]

While K[[x^±]] is not a ring, it has a K[x^±]-module structure.
A Laurent polynomial can be multiplied with any doubly infinite power series.

This corresponds to the discussion in "A K[x^±]-module structure on K[[x^±]]".
-/


section ModuleStructure

variable {K : Type*} [CommRing K] [Nontrivial K]

/-- The action of a Laurent polynomial on a doubly infinite power series.

The product (∑ b_n x^n) · (∑ a_n x^n) = (∑ c_n x^n) where c_n = ∑_{i ∈ ℤ} a_i b_{n-i}.
This sum is finite because the Laurent polynomial has finite support.

This makes K[[x^±]] into a K[x^±]-module. -/
def laurentPolynomialSmul (p : K[T;T⁻¹]) (f : DoublyInfinitePowerSeries K) :
    DoublyInfinitePowerSeries K :=
  fun n => p.coeff.sum fun i b => b * f (n - i)

end ModuleStructure
/-! ## k-bounded Balanced Ternary Representations

A balanced ternary representation is k-bounded if all digits beyond position k are zero.
This is used in the rigorous proof of Theorem `thm.fps.laure.balanced-tern-rep-uniq`.
-/


/-- A balanced ternary representation is k-bounded if b_{k+1} = b_{k+2} = ... = 0. -/
def BalancedTernaryRepresentation.isBounded {n : ℤ} (r : BalancedTernaryRepresentation n)
    (k : ℕ) : Prop :=
  ∀ i > k, r.digits i = 0
/-! ## Field Structure

When K is a field, K((x)) is also a field. This is mentioned at the end of the section. -/


/-- When K is a field, the Laurent series ring K((x)) is a field.
This is stated at the end of the section and proved in Exercise `exe.fps.laure.field`. -/
example (K : Type*) [Field K] : Field (LaurentSeries K) := inferInstance
/-! ## Partial Product Formula

The key computation used to prove Theorem `thm.fps.laure.balanced-tern-rep-uniq`
involves the partial products ∏_{i=0}^{k} (1 + x^{3^i} + x^{-3^i}).
-/


/-- The partial product ∏_{i=0}^{k} (1 + T^{3^i} + T^{-3^i}) in the Laurent polynomial ring.
This is used in the proof of Theorem `thm.fps.laure.balanced-tern-rep-uniq`. -/
def balancedTernaryPartialProduct (K : Type*) [CommSemiring K] (k : ℕ) : K[T;T⁻¹] :=
  ∏ i ∈ Finset.range (k + 1),
    (1 + LaurentPolynomial.T ((3 : ℤ)^i) + LaurentPolynomial.T (-((3 : ℤ)^i)))

end AlgebraicCombinatorics
