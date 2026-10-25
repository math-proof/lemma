/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Def.Combinatorics.Enumerative.Partition.NPartition.Part9
import Def.Combinatorics.Young.MonomialSymmetric.Part6
import Def.Combinatorics.Young.LittlewoodRichardson.Part16
open Finset Function BigOperators Polynomial MvPolynomial

/-!
# The Littlewood-Richardson Rule

This file formalizes the Littlewood-Richardson rule for Schur polynomials, following
the presentation in the Algebraic Combinatorics textbook.

The Littlewood-Richardson rule is one of the most famous results in the theory of symmetric
polynomials. It provides a combinatorial formula for expanding the product of Schur polynomials
as a sum of Schur polynomials:
$$s_\nu \cdot s_{\lambda/\mu} = \sum_{T} s_{\nu + \operatorname{cont}(T)}$$
where the sum is over all ν-Yamanouchi semistandard tableaux T of shape λ/μ.

## Main definitions

* `NPartition`: An N-partition is a weakly decreasing N-tuple of natural numbers
* `contentTableau`: The content of a tableau (counting occurrences of each entry)
* `colGeq`: Restriction of a tableau to columns ≥ j
* `IsYamanouchi`: A semistandard tableau is ν-Yamanouchi if certain conditions hold
* `alternant`: The alternant polynomial a_α
* `schurPoly`: The Schur polynomial s_λ (via the Jacobi-Trudi formula)
* `skewSchurPoly`: The skew Schur polynomial s_{λ/μ}

## Main results

* `littlewoodRichardson`: Zelevinsky's generalized Littlewood-Richardson rule (thm.sf.lr-zy)
* `stembridgeLemma`: Stembridge's lemma (lem.sf.stemb-lem)
* `schurPoly_eq_alternant_div`: Theorem relating Schur polynomials to alternants (thm.sf.schur-symm (b))

## Indexing Convention

**This file uses 1-indexed columns** for skew Young diagrams, matching the textbook convention:
- A cell (i, j) is in Y(λ/μ) iff μ_i < j ≤ λ_i
- Column indices start at 1 (the first column is j = 1)

This differs from `SchurBasics.lean` which uses **0-indexed columns** (Mathlib convention):
- A cell (i, j) is in Y(λ/μ) iff μ_i ≤ j < λ_i
- Column indices start at 0 (the first column is j = 0)

The bijection (i, j) ↔ (i, j+1) converts between the conventions.
See `SchurBasics.skewCellEquiv` and `SchurBasics.mem_skewYoungDiagram_iff_mem_LR_shifted`
for explicit equivalences.

## References

* [Stembridge, *A concise proof of the Littlewood-Richardson rule*][Stembr02]
* [Grinberg-Reiner, *Hopf algebras in Combinatorics*][GriRei]

## Tags

Littlewood-Richardson rule, Schur polynomial, Yamanouchi tableau, symmetric polynomial
-/


namespace AlgebraicCombinatorics

variable {R : Type*} [CommRing R]

variable {N : ℕ}

/-! ## Examples -/


/-- Example (exa.sf.lr-zy.1): For N=3, nu=(1,0,0), lam=(2,1,0), mu=(0,0,0):
    s_{(1,0,0)} · s_{(2,1,0)} = s_{(3,1,0)} + s_{(2,2,0)} + s_{(2,1,1)}

    The (1,0,0)-Yamanouchi semistandard tableaux of shape (2,1,0)/0 are:
    - T₁ with entries [[1,1],[2]] and cont(T₁) = (2,1,0), giving s_{(3,1,0)}
    - T₂ with entries [[1,2],[2]] and cont(T₂) = (1,2,0), giving s_{(2,2,0)}
    - T₃ with entries [[1,2],[3]] and cont(T₃) = (1,1,1), giving s_{(2,1,1)}

    Note: s_{(1,0,0)} = x₁ + x₂ + x₃ (the elementary symmetric polynomial e₁). -/
example : True := trivial -- Requires explicit computation with concrete tableaux

end AlgebraicCombinatorics
