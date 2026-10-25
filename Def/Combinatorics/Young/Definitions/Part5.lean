/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Instance.GroupTheory.Perm.Basics.Part2
import Lemma.PowerSeries.CommutativeRings
import Abbrev.Combinatorics.Young.Definitions.Part3
open scoped Polynomial
open MvPolynomial Finset

/-!
# Definitions and Examples of Symmetric Polynomials

This file formalizes the definitions and basic properties of symmetric polynomials,
following Section "Definitions and examples of symmetric polynomials" (sec.sf.sp) of the source.

## Main definitions

* We use Mathlib's `MvPolynomial.IsSymmetric` for the notion of symmetric polynomials.
* `MvPolynomial.symmetricSubalgebra σ R` is the ring of symmetric polynomials.
* `MvPolynomial.esymm σ R n` is the n-th elementary symmetric polynomial.
* `MvPolynomial.hsymm σ R n` is the n-th complete homogeneous symmetric polynomial.
* `MvPolynomial.psum σ R n` is the n-th power sum.

## Main results

* The symmetric group acts on polynomials by permuting variables (Proposition prop.sf.SN-acts)
* The action is by K-algebra automorphisms (Proposition prop.sf.SN-acts-by-alg-auts)
* The set of symmetric polynomials forms a K-subalgebra (Theorem thm.sf.S-subalg)
* For n > N, the n-th elementary symmetric polynomial is zero (Proposition prop.sf.en=0)
* Newton-Girard formulas relating e_n, h_n, and p_n (Theorem thm.sf.NG)
* Fundamental Theorem of Symmetric Polynomials (Theorem thm.sf.ftsf)
* A polynomial is symmetric iff it is invariant under simple transpositions (Lemma lem.sf.simples-enough)

## References

* Source: SymmetricFunctions/Definitions.tex, sec.sf.sp

## Implementation notes

Mathlib already provides extensive support for symmetric polynomials via `MvPolynomial.IsSymmetric`
and related definitions. This file connects the textbook presentation to Mathlib's API
and provides additional lemmas following the source material.

The symmetric group action on polynomials is given by `MvPolynomial.rename` in Mathlib.
For a permutation σ : Equiv.Perm (Fin N), the action σ · f is `MvPolynomial.rename σ f`.
-/


/-! Compatibility with the pre-2026 `MvPolynomial.coeff m p` argument order. -/


namespace AlgebraicCombinatorics

namespace SymmetricPolynomials

variable {K : Type*} [CommRing K]

variable {N : ℕ}

variable {σ : Type*}

/-- Convert a monomial (exponent vector) to the corresponding polynomial x₁^{a₁} ⋯ x_N^{a_N}.
    Label: def.sf.monomial -/
noncomputable def Monomial.toPoly (m : Monomial N) : P K N :=
  monomial m 1

/-- The degree of a monomial is the sum of its exponents.
    Label: def.sf.monomial -/
def Monomial.degree (m : Monomial N) : ℕ := m.sum (fun _ a => a)

/-- A monomial is squarefree if all exponents are 0 or 1.
    Label: def.sf.monomial -/
def Monomial.IsSquarefree (m : Monomial N) : Prop := ∀ i, m i ≤ 1

/-- A monomial is primal if at most one exponent is positive.
    This means the monomial is either 1 or a power of a single variable.
    Label: def.sf.monomial -/
def Monomial.IsPrimal (m : Monomial N) : Prop := m.support.card ≤ 1

/-- The set of all monomials of a given degree n.
    Label: def.sf.monomial -/
def monomialsOfDegree (N n : ℕ) : Set (Monomial N) :=
  {m | m.degree = n}

/-- The set of all squarefree monomials of a given degree n.
    Label: def.sf.monomial -/
def squarefreeMonomials (N n : ℕ) : Set (Monomial N) :=
  {m | m.IsSquarefree ∧ m.degree = n}

/-- The set of all primal monomials of a given degree n.
    Label: def.sf.monomial -/
def primalMonomials (N n : ℕ) : Set (Monomial N) :=
  {m | m.IsPrimal ∧ m.degree = n}

/-- A single variable x_i corresponds to the monomial with exponent 1 at position i.
    Label: def.sf.monomial -/
noncomputable def Monomial.single (i : Fin N) : Monomial N := Finsupp.single i 1

/-- The monomial corresponding to a subset S ⊆ [N] is ∏_{i ∈ S} x_i.
    This is the squarefree monomial with support S.
    Label: def.sf.monomial -/
noncomputable def Monomial.ofFinset (s : Finset (Fin N)) : Monomial N :=
  s.sum (Finsupp.single · 1)

end SymmetricPolynomials
end AlgebraicCombinatorics
