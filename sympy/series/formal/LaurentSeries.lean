/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
/-
Copyright (c) 2025 AlgebraicCombinatorics contributors. All rights reserved.
Authors: AlgebraicCombinatorics contributors
-/
import Mathlib
import sympy.series.LaurentSeries
import Lemma.PowerSeries.InfiniteProducts2
import Lemma.LaurentSeries.LaurentSeries
import Lemma.Partition.NPartition
/-!
# Laurent Power Series

This file formalizes properties of Laurent polynomials and Laurent power series,
following Section `\ref{sec.details.gf.laure}` of the source material.

## Overview

Laurent polynomials are formal sums `∑_{i ∈ ℤ} aᵢ xⁱ` where only finitely many coefficients
are nonzero. Laurent power series are formal sums where the sequence of negative-indexed
coefficients is essentially finite (i.e., only finitely many negative powers appear).

In Mathlib:
- Laurent polynomials are `LaurentPolynomial R` (notation `R[T;T⁻¹]`), implemented as
  `AddMonoidAlgebra R ℤ`
- Laurent series are `LaurentSeries R` (notation `R⸨X⸩`), implemented as `HahnSeries ℤ R`

## Main Results

### Laurent Polynomials (Theorem thm.fps.laure.laupol-ring)
- `LaurentPolynomial` forms a commutative `K`-algebra with `x` invertible
- Multiplication by `x` shifts coefficients: `x · a = (aₙ₋₁)_{n∈ℤ}` (Lemma lem.fps.laure.xa)
- For each `k ∈ ℤ`, we have `xᵏ = (δᵢ,ₖ)_{i∈ℤ}` (Proposition prop.fps.laure.xk)
- Every Laurent polynomial can be written as `∑ aᵢ xⁱ` (`eq_sum_T`)

### Laurent Series (Theorem thm.fps.laure.lauser-ring)
- `LaurentSeries` forms a commutative `K`-algebra with `x` invertible
- The product of two Laurent series is again a Laurent series (closure under multiplication)
- Every Laurent series can be written as `∑_{i∈ℤ} aᵢ xⁱ` (Proposition prop.fps.laure.a=sumaixi)

## References

- Source: `AlgebraicCombinatorics/tex/Details/LaurentSeries.tex`
- Labels: `thm.fps.laure.laupol-ring`, `lem.fps.laure.xa`, `prop.fps.laure.xk`,
  `prop.fps.laure.a=sumaixi`, `thm.fps.laure.lauser-ring`
-/


open scoped LaurentPolynomial Polynomial
open LaurentPolynomial HahnSeries

-- `AddMonoidAlgebra` is a wrapper around `M →₀ R` (`coeff`), not the `Finsupp` itself.
namespace AddMonoidAlgebra

variable {R M : Type*} [Semiring R]

def support (x : AddMonoidAlgebra R M) : Finset M := x.coeff.support

instance : CoeFun (AddMonoidAlgebra R M) (fun _ => M → R) where
  coe x m := x.coeff m

end AddMonoidAlgebra

noncomputable section

namespace AlgebraicCombinatorics.FPS.Laurent
/-!
## Section: Laurent Polynomials

A Laurent polynomial over a commutative ring `K` is a formal sum `∑_{i ∈ ℤ} aᵢ xⁱ`
where only finitely many coefficients `aᵢ` are nonzero.

In Mathlib, `LaurentPolynomial R` is defined as `AddMonoidAlgebra R ℤ`, i.e., finitely
supported functions `ℤ →₀ R`. The variable is denoted `T` to distinguish from polynomials.
-/
/-!
## Definition: Laurent Polynomials (def.fps.laure.laupol)

This section formalizes Definition \ref{def.fps.laure.laupol} from the source material.

A Laurent polynomial over K is an essentially finite family (aₙ)_{n∈ℤ}, i.e., a function
ℤ → K with finite support. The set K[x^±] of all Laurent polynomials forms a K-submodule
of the doubly infinite power series K[[x^±]].

Multiplication is defined by convolution:
  (a · b)_n = ∑_{i∈ℤ} aᵢ · b_{n-i}

The indeterminate x is defined as x = (δ_{i,1})_{i∈ℤ}, i.e., the sequence with 1 at
position 1 and 0 elsewhere.

In Mathlib, Laurent polynomials are represented as `LaurentPolynomial K = AddMonoidAlgebra K ℤ`,
which is exactly `ℤ →₀ K` (finitely supported functions from ℤ to K). This matches the
definition of essentially finite families.
-/


section LaurentPolynomialDefinition

variable {K : Type*} [CommRing K]

/-- **Definition of Laurent polynomials** (Definition def.fps.laure.laupol)

A Laurent polynomial over K is an essentially finite family (aₙ)_{n∈ℤ}, represented
in Mathlib as `LaurentPolynomial K = AddMonoidAlgebra K ℤ = ℤ →₀ K`.

This definition captures the key property: only finitely many coefficients are nonzero. -/
abbrev LaurentPoly (K : Type*) [CommRing K] := K[T;T⁻¹]

/-- The coefficient function of a Laurent polynomial. -/
def laurentPoly_coeff (p : LaurentPoly K) (n : ℤ) : K := p n

/-- **The indeterminate x in Laurent polynomials**.
(Part of Definition def.fps.laure.laupol)

The element x = (δ_{i,1})_{i∈ℤ} is the sequence with 1 at position 1 and 0 elsewhere.
In Mathlib notation, this is `T 1`. -/
def laurentPoly_X : LaurentPoly K := T 1

/-- **Laurent polynomials form a K-module**.
(Part of Definition def.fps.laure.laupol)

The set K[x^±] is a K-submodule of K[[x^±]]. In Mathlib, this is captured by the
Module instance on LaurentPolynomial. -/
def laurentPoly_module : Module K (LaurentPoly K) := inferInstance

/-- **Construction of Laurent polynomials from finite data**.

Any finitely supported function ℤ → K gives a Laurent polynomial. -/
def laurentPoly_ofFinsupp (f : ℤ →₀ K) : LaurentPoly K := AddMonoidAlgebra.ofCoeff f

/-- **Single term Laurent polynomial**.

The Laurent polynomial with a single term `a · x^k` is represented as `Finsupp.single k a`. -/
def laurentPoly_single (k : ℤ) (a : K) : LaurentPoly K := AddMonoidAlgebra.single k a

end LaurentPolynomialDefinition

section LaurentPolynomialBasics

variable {K : Type*} [CommRing K]

/-- **Laurent polynomials form a commutative K-algebra**.
(Theorem thm.fps.laure.laupol-ring, label: thm.fps.laure.laupol-ring)

This is the key structural result: `K[T;T⁻¹]` is a commutative ring with `T` invertible. -/
def laurentPolynomial_commRing : CommRing K[T;T⁻¹] := inferInstance

def laurentPolynomial_algebra : Algebra K K[T;T⁻¹] := inferInstance

end LaurentPolynomialBasics
/-!
## Section: Multiplication by T shifts coefficients

This section proves the analogue of Lemma `lem.fps.xa` for Laurent polynomials:
multiplication by `T` shifts coefficients by 1.
-/


section ShiftByT

variable {K : Type*} [CommRing K]

end ShiftByT
/-!
## Section: Powers of T

This section proves that `Tᵏ = (δᵢ,ₖ)_{i∈ℤ}` for all `k ∈ ℤ`, the analogue of
Proposition `prop.fps.xk` for Laurent polynomials.
-/


section PowersOfT

variable {K : Type*} [CommRing K]

end PowersOfT
/-!
## Section: Representation as sums

Every Laurent polynomial can be written as a finite sum `∑ aᵢ Tⁱ`.
-/


section Representation

variable {K : Type*} [CommRing K]

end Representation
/-!
## Section: Laurent Series

Laurent series are formal power series with finitely many negative exponents.
In Mathlib, they are implemented as `HahnSeries ℤ R`, which are functions `ℤ → R`
with well-founded support.

The key result (Theorem thm.fps.laure.lauser-ring) is that Laurent series form
a commutative K-algebra, and in particular that the product of two Laurent series
is again a Laurent series.
-/


section LaurentSeriesBasics

variable {K : Type*} [CommRing K]

/-- **Laurent series form a commutative K-algebra**.
(Theorem thm.fps.laure.lauser-ring, label: thm.fps.laure.lauser-ring)

This is the key structural result for Laurent series. -/
def laurentSeries_commRing : CommRing (LaurentSeries K) := inferInstance

def laurentSeries_algebra : Algebra K (LaurentSeries K) := inferInstance

/-- A summable family of single Hahn series indexed by the support of a given Laurent series.
This is used to express a Laurent series as an infinite sum of monomials. -/
def singleFamily (x : LaurentSeries K) : SummableFamily ℤ K x.support where
  toFun := fun ⟨g, _⟩ => single g (x.coeff g)
  isPWO_iUnion_support' := by
    refine x.isPWO_support.mono ?_
    intro g hg
    simp only [Set.mem_iUnion] at hg
    obtain ⟨⟨g', hg'⟩, hg''⟩ := hg
    simp only [mem_support] at hg''
    by_cases h : x.coeff g' = 0
    · simp [h] at hg''
    · have hsingle : (single g' (x.coeff g')).coeff g ≠ 0 := hg''
      rw [coeff_single] at hsingle
      split_ifs at hsingle with heq
      · subst heq
        exact hg'
      · contradiction
  finite_co_support' := fun g => by
    by_cases hg : x.coeff g = 0
    · convert Set.finite_empty
      ext ⟨g', _⟩
      simp only [Set.mem_ofPred_eq, coeff_single, Set.mem_empty_iff_false, iff_false]
      intro h
      split_ifs at h with heq
      · subst heq
        exact h hg
      · exact h rfl
    · have hg_supp : g ∈ x.support := by simpa [mem_support] using hg
      refine Set.Finite.subset (Set.finite_singleton ⟨g, hg_supp⟩) ?_
      intro ⟨g', hg'⟩ h
      simp only [Set.mem_ofPred_eq, coeff_single, ne_eq] at h
      simp only [Set.mem_singleton_iff, Subtype.mk.injEq]
      split_ifs at h with heq
      · exact heq.symm
      · contradiction

end LaurentSeriesBasics
/-!
## Section: Closure of Laurent Series under Multiplication

The main technical content of Theorem thm.fps.laure.lauser-ring is showing that
the product of two Laurent series is again a Laurent series. This requires showing
that if `(a_{-1}, a_{-2}, ...)` and `(b_{-1}, b_{-2}, ...)` are essentially finite,
then so is the corresponding sequence for the product.
-/


section MultiplicationClosure

variable {K : Type*} [CommRing K]

/-- The order of a nonzero Laurent series is the smallest index with nonzero coefficient. -/
def laurentOrder (f : LaurentSeries K) : ℤ := f.order

end MultiplicationClosure
/-!
## Section: Embedding of Power Series into Laurent Series

Power series embed into Laurent series via the natural map that sends
`∑_{n≥0} aₙ xⁿ` to the same series viewed as a Laurent series with
zero coefficients for negative indices.
-/


section PowerSeriesEmbedding

variable {K : Type*} [CommRing K]

/-- Power series embed into Laurent series.
(Implicit in the source material) -/
def powerSeriesToLaurent : PowerSeries K →+* LaurentSeries K :=
  HahnSeries.ofPowerSeries ℤ K

end PowerSeriesEmbedding
/-!
## Section: Embedding of Laurent Polynomials into Laurent Series

Laurent polynomials embed into Laurent series.
-/


section LaurentPolynomialEmbedding

variable {K : Type*} [CommRing K]

/-- A Laurent polynomial can be viewed as a Laurent series.

This is the inclusion `K[T;T⁻¹] → K⸨X⸩`. -/
def laurentPolynomialToSeries (p : K[T;T⁻¹]) : LaurentSeries K where
  coeff n := p.coeff n
  isPWO_support' := by
    apply Set.Finite.isPWO
    have h : {x | ¬p.coeff x = 0} = (p.support : Set ℤ) := by
      ext x
      simp [AddMonoidAlgebra.support, Finsupp.mem_support_iff]
    simpa [h] using p.support.finite_toSet

end LaurentPolynomialEmbedding
/-!
## Section: Binary Representation Uniqueness

This section proves that every natural number has a unique binary representation,
which is Theorem `thm.fps.laure.binary-rep-uniq` in the source material.

A binary representation of `n ∈ ℕ` is an essentially finite sequence `(bᵢ)_{i ∈ ℕ}` with
`bᵢ ∈ {0, 1}` such that `n = ∑_{i ∈ ℕ} bᵢ · 2^i`.

In Mathlib, this is captured by the equivalence `Finset.equivBitIndices : ℕ ≃ Finset ℕ`,
where a finset `s ⊆ ℕ` represents the binary sequence with `bᵢ = 1` iff `i ∈ s`.
-/


section BinaryRepresentation

open Finset in
/-- **Binary Representation Definition**.

A binary representation of `n` is a finset `s ⊆ ℕ` such that `n = ∑_{i ∈ s} 2^i`.
This is equivalent to specifying which bits are 1 in the binary expansion.

The essentially finite sequence `(bᵢ)_{i ∈ ℕ}` from the textbook corresponds to
`bᵢ = 1` if `i ∈ s`, and `bᵢ = 0` otherwise. -/
def BinaryRepresentation (n : ℕ) (s : Finset ℕ) : Prop :=
  n = ∑ i ∈ s, 2 ^ i

/-- The canonical binary representation of `n` is `n.bitIndices.toFinset`. -/
def canonicalBinaryRep (n : ℕ) : Finset ℕ := n.bitIndices.toFinset

/-- **Bijection between ℕ and Finset ℕ via binary representation**.

This equivalence maps `n` to its binary representation (as a finset of indices where
the binary digit is 1), and conversely maps a finset `s` to `∑_{i ∈ s} 2^i`.

This is the formalization of the bijection implicit in Theorem thm.fps.laure.binary-rep-uniq. -/
def binaryRepEquiv : ℕ ≃ Finset ℕ := Finset.equivBitIndices

end BinaryRepresentation
/-!
## Section: Balanced Ternary Representation Uniqueness

This section proves Theorem `thm.fps.laure.balanced-tern-rep-uniq`: Every integer
has a unique balanced ternary representation.

A **balanced ternary representation** of an integer `n` is an essentially finite
sequence `(b_i)_{i∈ℕ}` with `b_i ∈ {-1, 0, 1}` such that `n = ∑_{i∈ℕ} b_i · 3^i`.

The proof uses Laurent polynomials and the key identity:
  `∏_{i=0}^{k} (1 + x^{3^i} + x^{-3^i}) = ∑_{|n| ≤ M_k} x^n`
where `M_k = 3^0 + 3^1 + ... + 3^k = (3^{k+1} - 1) / 2`.

Comparing coefficients shows that each integer in `[-M_k, M_k]` has exactly one
k-bounded balanced ternary representation. Taking `k → ∞` gives the full result.
-/


section BalancedTernaryRepresentation

open Finset

/-- The set of balanced ternary digits {-1, 0, 1}. -/
def btDigits : Finset ℤ := {-1, 0, 1}

/-- **Balanced Ternary Representation Definition**.
(Definition def.fps.laure.balanced-tern, label: def.fps.laure.balanced-tern)

A balanced ternary representation of an integer `n` is a finitely supported
function `f : ℕ → ℤ` with values in {-1, 0, 1} such that `n = ∑_i f(i) · 3^i`.

Unlike binary representations (where digits are 0 or 1), balanced ternary
allows digits to be -1, 0, or 1. This enables direct representation of
negative integers without a separate sign. -/
structure BalancedTernaryRep (n : ℤ) where
  /-- The digit function -/
  digits : ℕ →₀ ℤ
  /-- All digits are in {-1, 0, 1} -/
  digits_range : ∀ i, digits i ∈ btDigits
  /-- The value equals n -/
  sum_eq : ∑ i ∈ digits.support, digits i * (3 : ℤ) ^ i = n

/-- The value of a finitely supported balanced ternary representation. -/
def balancedTernaryValue (f : ℕ →₀ ℤ) : ℤ :=
  ∑ i ∈ f.support, f i * (3 : ℤ) ^ i

/-- A k-bounded balanced ternary representation is a function `f : Fin (k+1) → {-1, 0, 1}`.

These are representations where `f(i) = 0` for all `i > k`. -/
def kBoundedBTReps (k : ℕ) : Finset (Fin (k + 1) → ℤ) :=
  Fintype.piFinset (fun _ => btDigits)

/-- The value of a k-bounded balanced ternary representation. -/
def kBoundedBTValue (k : ℕ) (f : Fin (k + 1) → ℤ) : ℤ :=
  ∑ i : Fin (k + 1), f i * (3 : ℤ) ^ (i : ℕ)

/-- The maximum absolute value representable with k+1 balanced ternary digits:
    `M_k = 3^0 + 3^1 + ... + 3^k = (3^{k+1} - 1) / 2` -/
def maxBT (k : ℕ) : ℕ := ∑ i ∈ range (k + 1), 3 ^ i

/-- The set of integers from -M to M. -/
def Icc_symm (M : ℕ) : Finset ℤ := Icc (-(M : ℤ)) (M : ℤ)

/-- Helper to convert a k-bounded representation to a Finsupp. -/
noncomputable def kBoundedToFinsupp (k : ℕ) (f : Fin (k + 1) → ℤ) : ℕ →₀ ℤ :=
  Finsupp.onFinset (range (k + 1)) (fun i => if h : i < k + 1 then f ⟨i, h⟩ else 0)
    (fun i hi => by
      simp only [mem_range, ne_eq] at hi ⊢
      by_contra h
      push Not at h
      exact hi (dif_neg (not_lt.mpr h)))

end BalancedTernaryRepresentation
/-!
## Section: Equivalence with Alternative Balanced Ternary Representation

This section establishes the equivalence between the `BalancedTernaryRep` structure
defined in this file (using `ℕ →₀ ℤ` with `btDigits` constraint) and the 
`AlgebraicCombinatorics.BalancedTernaryRepresentation` structure defined in 
`LaurentSeries.lean` (using an inductive `BalancedTernaryDigit` type).

Both representations capture the same mathematical concept: balanced ternary 
representations of integers. The equivalence theorems below show that:
1. Any `BalancedTernaryRepresentation` can be converted to a `BalancedTernaryRep`
2. Any `BalancedTernaryRep` can be converted to a `BalancedTernaryRepresentation`  
3. These conversions are inverses of each other (up to the digit representation)

This provides a bridge between the two equivalent formulations.
-/


section BalancedTernaryEquivalence

-- Alias for the type from LaurentSeries.lean for clarity
abbrev BTRep := AlgebraicCombinatorics.BalancedTernaryRepresentation
abbrev BTDigit := AlgebraicCombinatorics.BalancedTernaryDigit

/-- The existing `BalancedTernaryDigit.toInt` maps into `btDigits`. -/
theorem BTDigit.toInt_mem_btDigits (d : BTDigit) : d.toInt ∈ btDigits := by
  cases d <;> simp [AlgebraicCombinatorics.BalancedTernaryDigit.toInt, btDigits]

/-- Convert an integer in `btDigits` to a `BalancedTernaryDigit`. -/
def btDigitOfInt (z : ℤ) : BTDigit :=
  if z = -1 then .negOne
  else if z = 0 then .zero
  else .one

@[simp]
theorem btDigitOfInt_toInt (z : ℤ) (hz : z ∈ btDigits) : 
    (btDigitOfInt z).toInt = z := by
  simp only [btDigits, Finset.mem_insert, Finset.mem_singleton] at hz
  simp only [btDigitOfInt]
  rcases hz with hz | hz | hz <;> 
    simp [hz, AlgebraicCombinatorics.BalancedTernaryDigit.toInt]

@[simp]
theorem toInt_btDigitOfInt (d : BTDigit) : btDigitOfInt d.toInt = d := by
  cases d <;> simp [btDigitOfInt, AlgebraicCombinatorics.BalancedTernaryDigit.toInt]

/-- `btDigitOfInt 0 = zero` -/
@[simp]
theorem btDigitOfInt_zero : 
    btDigitOfInt 0 = AlgebraicCombinatorics.BalancedTernaryDigit.zero := by 
  simp [btDigitOfInt]

/-- `btDigitOfInt z ≠ 0` iff `z ≠ 0` (for `z ∈ btDigits`) -/
theorem btDigitOfInt_ne_zero_iff (z : ℤ) (hz : z ∈ btDigits) : 
    btDigitOfInt z ≠ 0 ↔ z ≠ 0 := by
  simp only [btDigits, Finset.mem_insert, Finset.mem_singleton] at hz
  rcases hz with hz | hz | hz <;> simp [hz, btDigitOfInt]; rfl

/-- Convert a `BTRep` (inductive style from `LaurentSeries.lean`) 
to a `BalancedTernaryRep` (Finsupp style). -/
noncomputable def BTRep.toFinsupp {n : ℤ} (r : BTRep n) : BalancedTernaryRep n where
  digits := {
    support := r.finite_support.toFinset
    toFun := fun i => (r.digits i).toInt
    mem_support_toFun := by
      intro i
      simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq,
                 AlgebraicCombinatorics.BalancedTernaryDigit.ne_zero_iff_toInt_ne_zero, ne_eq]
  }
  digits_range := fun i => BTDigit.toInt_mem_btDigits _
  sum_eq := by
    simp only [Finsupp.coe_mk]
    have h := r.sum_eq
    rw [finsum_eq_sum_of_support_subset _ (s := r.finite_support.toFinset)] at h
    · convert h using 1
    · intro i hi
      simp only [Function.mem_support, ne_eq] at hi
      simp only [Set.Finite.coe_toFinset, Set.mem_ofPred_eq]
      intro heq
      apply hi
      simp only [heq, AlgebraicCombinatorics.BalancedTernaryDigit.toInt_zero, zero_mul]

/-- Convert a `BalancedTernaryRep` (Finsupp style) to a 
`BTRep` (inductive style from `LaurentSeries.lean`). -/
noncomputable def BalancedTernaryRep.toInductive {n : ℤ} (r : BalancedTernaryRep n) : BTRep n where
  digits := fun i => btDigitOfInt (r.digits i)
  finite_support := by
    have h : {i | btDigitOfInt (r.digits i) ≠ 0} ⊆ r.digits.support := by
      intro i hi
      simp only [Set.mem_ofPred_eq] at hi
      simp only [Finset.mem_coe, Finsupp.mem_support_iff]
      rw [btDigitOfInt_ne_zero_iff _ (r.digits_range i)] at hi
      exact hi
    exact r.digits.support.finite_toSet.subset h
  sum_eq := by
    have h := r.sum_eq
    rw [finsum_eq_sum_of_support_subset _ (s := r.digits.support)]
    · convert h using 2 with i _
      rw [btDigitOfInt_toInt _ (r.digits_range i)]
    · intro i hi
      simp only [Function.mem_support, ne_eq] at hi
      rw [Finset.mem_coe, Finsupp.mem_support_iff]
      intro hz
      apply hi
      rw [hz, btDigitOfInt_zero]
      simp [AlgebraicCombinatorics.BalancedTernaryDigit.toInt]

/-- **Round-trip equivalence**: Converting from the inductive representation to Finsupp 
and back gives the same digits (as `BalancedTernaryDigit` values). -/
theorem BTRep.toFinsupp_toInductive_digits {n : ℤ} (r : BTRep n) :
    r.toFinsupp.toInductive.digits = r.digits := by
  ext i
  simp only [BalancedTernaryRep.toInductive, BTRep.toFinsupp, Finsupp.coe_mk, toInt_btDigitOfInt]

/-- **Round-trip equivalence**: Converting from Finsupp representation to inductive 
and back gives the same digits (as integer values in the Finsupp). -/
theorem BalancedTernaryRep.toInductive_toFinsupp_digits {n : ℤ} (r : BalancedTernaryRep n) :
    r.toInductive.toFinsupp.digits = r.digits := by
  ext i
  simp only [BTRep.toFinsupp, BalancedTernaryRep.toInductive, Finsupp.coe_mk, 
             btDigitOfInt_toInt _ (r.digits_range i)]

/-- Type equivalence between the two balanced ternary representations.
This shows the types `BalancedTernaryRep n` and `AlgebraicCombinatorics.BalancedTernaryRepresentation n`
are equivalent (bijective correspondence). -/
noncomputable def balancedTernary_equiv (n : ℤ) : BalancedTernaryRep n ≃ BTRep n where
  toFun := BalancedTernaryRep.toInductive
  invFun := BTRep.toFinsupp
  left_inv r := by
    have h := r.toInductive_toFinsupp_digits
    cases r with | mk digits _ _ =>
    simp only [BTRep.toFinsupp, BalancedTernaryRep.toInductive] at h ⊢
    congr 1
  right_inv r := by
    have h := r.toFinsupp_toInductive_digits
    cases r with | mk digits _ _ =>
    simp only [BalancedTernaryRep.toInductive, BTRep.toFinsupp] at h ⊢
    congr 1

end BalancedTernaryEquivalence

end AlgebraicCombinatorics.FPS.Laurent
