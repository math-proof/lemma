/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Def.Combinatorics.Enumerative.Partition.NPartition.Part9
import Def.Combinatorics.Young.MonomialSymmetric.Part6
import Instance.Combinatorics.Young.LittlewoodRichardson.Part3
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

/-- The skew Schur polynomial s_{lam/mu}.
    Defined as a sum over semistandard tableaux of shape lam/mu:
    s_{lam/mu} = ∑_{T semistandard of shape lam/mu} x^(cont(T))

    Note: This is a finite sum since there are finitely many semistandard tableaux
    of any given shape (entries are bounded by N).

    ## Relationship to Other Definitions

    This project has two skew Schur polynomial definitions with different design tradeoffs:

    | Definition | File | Input | Ring | Use case |
    |------------|------|-------|------|----------|
    | `AlgebraicCombinatorics.skewSchurPoly` (this) | LittlewoodRichardson.lean | `Fin N → ℕ` | generic `R` | Littlewood-Richardson rule, generic rings |
    | `skewSchurPoly` | SchurBasics.lean | `NPartition N` | `ℤ` | Proofs using skew diagrams, symmetry |

    **When to use which:**
    - Use **this definition** when you need a generic coefficient ring `R`, when working
      with the Littlewood-Richardson rule, or when you have an unbundled `Fin N → ℕ`.
    - Use **`SchurBasics.skewSchurPoly`** when working with skew Young diagrams, SSYT
      fillings as explicit structures, or proving symmetry properties. It requires
      `[NeZero N]` and uses integer coefficients.

    **Equivalence:** See `SSYTEquiv.lean` for the bridge between these definitions. -/
noncomputable def skewSchurPoly (lam mu : Fin N → ℕ) : MvPolynomial (Fin N) R :=
  -- Sum over all semistandard tableaux T of shape lam/mu
  -- Each term is x^(cont(T))
  ∑ T : {T : Tableau lam mu // IsSemistandard T}, xPow (contentTableau T.val)

/-- The Schur polynomial s_lam for an N-partition lam.
    Defined as s_{lam/0}, i.e., the skew Schur polynomial with empty inner shape.

    ## Relationship to Other Definitions

    This project has two Schur polynomial definitions with different design tradeoffs:

    | Definition | File | Input | Ring | Use case |
    |------------|------|-------|------|----------|
    | `AlgebraicCombinatorics.schurPoly` (this) | LittlewoodRichardson.lean | `Fin N → ℕ` | generic `R` | Littlewood-Richardson rule, generic rings |
    | `schurPoly` | SchurBasics.lean | `NPartition N` | `ℤ` | Proofs using Young diagrams, symmetry |

    **When to use which:**
    - Use **this definition** when you need a generic coefficient ring `R`, when working
      with the Littlewood-Richardson rule, or when you have an unbundled `Fin N → ℕ`.
    - Use **`SchurBasics.schurPoly`** when working with Young diagrams, SSYT fillings
      as explicit structures, or proving symmetry properties. It requires `[NeZero N]`
      and uses integer coefficients.

    **Equivalence:** The two definitions agree when the partition is valid. See:
    - `SSYTEquiv.schurPoly_eq_schur`: relates `SchurBasics.schurPoly` to `SymmetricFunctions.schur`
    - `schurPoly_eq_AC_schurPoly`: relates `SchurBasics.schurPoly` to this definition -/
noncomputable def schurPoly (lam : Fin N → ℕ) : MvPolynomial (Fin N) R :=
  skewSchurPoly lam 0

end AlgebraicCombinatorics
