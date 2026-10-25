/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Instance.GroupTheory.Perm.Basics.Part2
import Lemma.PowerSeries.CommutativeRings
import Theorem.Combinatorics.Young.Definitions.Part3
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

/-- The map from S_N to Aut_K(P) is a group homomorphism.
    This is the full content of Proposition prop.sf.SN-acts-by-alg-auts:
    S_N acts on P by K-algebra automorphisms.
    Label: prop.sf.SN-acts-by-alg-auts -/
noncomputable def permAutomorphismHom :
    Equiv.Perm (Fin N) →* (P K N ≃ₐ[K] P K N) where
  toFun σ := permAutomorphism σ
  map_one' := permAutomorphism_id
  map_mul' σ τ := permAutomorphism_mul_perm σ τ

/-!
## Theorem thm.sf.S-subalg: S is a K-subalgebra of P

The set of symmetric polynomials is closed under addition, multiplication, and scaling,
and contains 0 and 1.

From the source (AlgebraicCombinatorics/tex/SymmetricFunctions/Definitions.tex, Theorem thm.sf.S-subalg):

> The subset S is a K-subalgebra of P.

A K-subalgebra of P must satisfy:
1. S contains 0 and 1
2. S is closed under addition
3. S is closed under multiplication
4. S is closed under scalar multiplication by elements of K

This section proves all these properties both in terms of `IsSymm` (the predicate)
and `∈ S K N` (membership in the subalgebra).
-/


/-- **Theorem thm.sf.S-subalg**: The symmetric polynomials form a K-subalgebra of P.

    This is the main theorem stating that the set S of symmetric polynomials is
    a K-subalgebra of the polynomial ring P = K[x₁, x₂, ..., x_N].

    A K-subalgebra satisfies:
    - (a) S contains 0 and 1 (see `S_zero_mem`, `S_one_mem`)
    - (b) S is closed under addition (see `S_add_mem`)
    - (c) S is closed under multiplication (see `S_mul_mem`)
    - (d) S is closed under scalar multiplication by K (see `S_smul_mem`)

    The definition `S K N := symmetricSubalgebra (Fin N) K` directly provides
    the `Subalgebra K (P K N)` structure, which bundles all these properties.

    Label: thm.sf.S-subalg -/
def S_subalgebra : Subalgebra K (P K N) := S K N

end SymmetricPolynomials
end AlgebraicCombinatorics
