/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Instance.GroupTheory.Perm.Basics.Part2
import Lemma.PowerSeries.CommutativeRings
import Abbrev.Combinatorics.Young.Definitions.Part4
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
## Basic Values (Example exa.sf.ehp.1)

(d) e_1 = h_1 = p_1 = x_1 + x_2 + ... + x_N
(e) e_0 = h_0 = 1, p_0 = N
(f) e_n = h_n = p_n = 0 for n < 0 (vacuously true for ℕ)
-/
/-!
## Integer-indexed versions (Definition def.sf.ehp)

The source defines e_n, h_n, p_n for all integers n ∈ ℤ.
For negative n, they are all 0. This section provides integer-indexed versions
that match the textbook definitions exactly.
-/


/-- Integer-indexed elementary symmetric polynomial.
    For n ∈ ℤ: e_n = esymm n if n ≥ 0, e_n = 0 if n < 0.
    This matches Definition def.sf.ehp (a) in the source.
    Label: def.sf.ehp -/
noncomputable def eZ (n : ℤ) : P K N :=
  if 0 ≤ n then e n.toNat else 0

/-- Integer-indexed complete homogeneous symmetric polynomial.
    For n ∈ ℤ: h_n = hsymm n if n ≥ 0, h_n = 0 if n < 0.
    This matches Definition def.sf.ehp (b) in the source.
    Label: def.sf.ehp -/
noncomputable def hZ [DecidableEq (Fin N)] (n : ℤ) : P K N :=
  if 0 ≤ n then h n.toNat else 0

/-- Integer-indexed power sum (textbook convention).
    For n ∈ ℤ: p'_n = psum n if n > 0, p'_0 = 1, p'_n = 0 if n < 0.
    This matches Definition def.sf.ehp (c) in the source.

    Note: Mathlib's psum has p_0 = N (number of variables), but the textbook
    defines p_0 = 1. We follow the textbook convention here.
    Label: def.sf.ehp -/
noncomputable def pZ (n : ℤ) : P K N :=
  if n > 0 then p n.toNat
  else if n = 0 then 1
  else 0

end SymmetricPolynomials
end AlgebraicCombinatorics
