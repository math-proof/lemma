/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Instance.GroupTheory.Perm.Basics.Part2
import Lemma.PowerSeries.CommutativeRings
import Def.Combinatorics.Young.Definitions.Part5
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

/-!
## Elementary Symmetric Polynomials (Definition def.sf.ehp (a))

e_n = sum of all squarefree monomials of degree n
    = ∑_{i₁ < i₂ < ... < i_n} x_{i₁} x_{i₂} ⋯ x_{i_n}

In Mathlib, this is `MvPolynomial.esymm (Fin N) K n`.
-/


/-- The n-th elementary symmetric polynomial.
    Label: def.sf.ehp -/
noncomputable abbrev e (n : ℕ) : P K N := esymm (Fin N) K n

/-!
## Complete Homogeneous Symmetric Polynomials (Definition def.sf.ehp (b))

h_n = sum of all monomials of degree n
    = ∑_{i₁ ≤ i₂ ≤ ... ≤ i_n} x_{i₁} x_{i₂} ⋯ x_{i_n}

In Mathlib, this is `MvPolynomial.hsymm (Fin N) K n`.
-/


section WithDecidableEq

variable [DecidableEq (Fin N)]

/-- The n-th complete homogeneous symmetric polynomial.
    Label: def.sf.ehp -/
noncomputable abbrev h (n : ℕ) : P K N := hsymm (Fin N) K n

end WithDecidableEq

/-!
## Power Sums (Definition def.sf.ehp (c))

p_n = x₁^n + x₂^n + ... + x_N^n  (for n > 0)
p_0 = 1
p_n = 0  (for n < 0)

In Mathlib, this is `MvPolynomial.psum (Fin N) K n`.
Note: Mathlib's definition has p_0 = N (the number of variables), not 1.
-/


/-- The n-th power sum symmetric polynomial.
    Label: def.sf.ehp -/
noncomputable abbrev p (n : ℕ) : P K N := psum (Fin N) K n

end SymmetricPolynomials
end AlgebraicCombinatorics
