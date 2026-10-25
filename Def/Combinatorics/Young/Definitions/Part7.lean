/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Instance.GroupTheory.Perm.Basics.Part2
import Lemma.PowerSeries.CommutativeRings
import Theorem.Combinatorics.Young.Definitions.Part4
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

section WithDecidableEq'

variable [DecidableEq (Fin N)]

/-- Add replicate (j+1) i to a Sym (n-1-j) to get a Sym n. -/
def addReplicate (m j : ℕ) (hj : j < m) (t : Sym (Fin N) (m - 1 - j)) (i : Fin N) :
    Sym (Fin N) m :=
  ⟨t.1 + Multiset.replicate (j + 1) i, add_replicate_card m j hj t i⟩

/-- Subtract replicate (k+1) i from a Sym n to get a Sym (n-1-k). -/
def subReplicate (m k : ℕ) (s : Sym (Fin N) m) (i : Fin N) (hk : k < s.1.count i) :
    Sym (Fin N) (m - 1 - k) :=
  ⟨s.1 - Multiset.replicate (k + 1) i, sub_replicate_card m k s i hk⟩

end WithDecidableEq'

/-!
## Generating Function Identities (Proposition prop.sf.e-h-FPS)

These identities express the elementary and complete homogeneous symmetric polynomials
as coefficients in certain generating functions.

(a) In P[t]: ∏_{i=1}^N (1 - t·x_i) = ∑_{n≥0} (-1)^n t^n e_n
(b) In P[u,v]: ∏_{i=1}^N (u - v·x_i) = ∑_{n=0}^N (-1)^n u^{N-n} v^n e_n
(c) In P[[t]]: ∏_{i=1}^N 1/(1 - t·x_i) = ∑_{n≥0} t^n h_n
-/
/-!
## Fundamental Theorem of Symmetric Polynomials (Theorem thm.sf.ftsf)

(a) e_1, e_2, ..., e_N are algebraically independent and generate S.
(b) h_1, h_2, ..., h_N are algebraically independent and generate S.
(c) If K is a ℚ-algebra, then p_1, p_2, ..., p_N are algebraically independent and generate S.

These are implemented in Mathlib via `MvPolynomial.esymmAlgEquiv`.

### Part (a): Elementary Symmetric Polynomials

The elementary symmetric polynomials e_1, e_2, ..., e_N are algebraically independent
over K and generate the K-algebra S of symmetric polynomials. This means:
1. The only polynomial relation P(e_1, ..., e_N) = 0 is P = 0 (algebraic independence)
2. Every symmetric polynomial can be written uniquely as a polynomial in e_1, ..., e_N (generation)

Equivalently, the map K[y_1, ..., y_N] → S given by g ↦ g(e_1, ..., e_N) is a K-algebra isomorphism.
-/


/-- The elementary symmetric polynomials e_1, ..., e_N generate the symmetric subalgebra
    and the map g ↦ g[e_1, ..., e_N] is a K-algebra isomorphism.
    (Theorem thm.sf.ftsf (a)).
    Label: thm.sf.ftsf -/
noncomputable def esymmAlgEquiv' : MvPolynomial (Fin N) K ≃ₐ[K] S K N :=
  esymmAlgEquiv (Fin N) K (Fintype.card_fin N)

/-!
### Part (b): Complete Homogeneous Symmetric Polynomials

The complete homogeneous symmetric polynomials h_1, h_2, ..., h_N are also algebraically
independent and generate S. This is a consequence of the Newton-Girard relations which
express each h_k as a polynomial in e_1, ..., e_k and vice versa.
-/


section PartB

variable [DecidableEq (Fin N)]

/-- The aeval map sending X_i to h_{i+1}.
    Label: thm.sf.ftsf -/
noncomputable def hsymmAeval : MvPolynomial (Fin N) K →ₐ[K] P K N :=
  aeval (fun i : Fin N => hsymm (Fin N) K (i + 1))

/-- The range of hsymmAeval is a subalgebra.
    Label: thm.sf.ftsf -/
noncomputable def hsymmRange : Subalgebra K (P K N) := hsymmAeval.range

end PartB

/-!
### Part (c): Power Sums (over ℚ-algebras)

When K is a ℚ-algebra (e.g., K = ℚ, ℝ, ℂ, or any field of characteristic 0),
the power sums p_1, p_2, ..., p_N are also algebraically independent and generate S.

Note: This fails in positive characteristic. For example, over 𝔽_p, we have
p_p = x_1^p + ... + x_N^p = (x_1 + ... + x_N)^p = p_1^p by the Frobenius endomorphism.
-/


section PartC

variable [Algebra ℚ K] [IsDomain K]

/-! ### Weight argument infrastructure for power sum algebraic independence

The key insight for proving the triangular structure of ψ(X_i) is a weight argument:
- Define weight(X_k) = k+1 for variables X_k in MvPolynomial (Fin N) K
- The map psumAeval' sends X_k to psum(k+1), which is homogeneous of degree k+1
- Therefore psumAeval' maps polynomials of weighted degree w to polynomials of total degree w
- Since esymm(i+1) has total degree i+1, any polynomial P with psumAeval'(P) = esymm(i+1)
  must have all monomials with weighted degree i+1
- This constrains which variables can appear in P with which exponents
-/


/-- The weight function for power sum analysis: X_k has weight k+1 -/
def psumWeight' : Fin N → ℕ := fun k => k.val + 1

/-- The aeval map sending X_i to p_{i+1}.
    Label: thm.sf.ftsf -/
noncomputable def psumAeval : MvPolynomial (Fin N) K →ₐ[K] P K N :=
  aeval (fun i : Fin N => psum (Fin N) K (i + 1))

/-- The range of psumAeval is a subalgebra.
    Label: thm.sf.ftsf -/
noncomputable def psumRange : Subalgebra K (P K N) := psumAeval.range

end PartC
end SymmetricPolynomials
end AlgebraicCombinatorics
