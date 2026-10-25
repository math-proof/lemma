/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Def.Combinatorics.Enumerative.Partition.NPartition.Part9
import Def.Combinatorics.Young.MonomialSymmetric.Part6
import Abbrev.Combinatorics.Young.LittlewoodRichardson
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

/-- Subtraction of N-tuples, defined entrywise. Note: result is in ℤ.
    (def.sf.tuple-addition (b)) -/
def subTuple (α β : Fin N → ℕ) : Fin N → ℤ := fun i => (α i : ℤ) - (β i : ℤ)

/-! ### API for def.sf.tuple-addition

The following lemmas establish the basic properties of N-tuple arithmetic
as stated in Definition def.sf.tuple-addition:
- (a) The zero N-tuple 0 = (0, 0, ..., 0)
- (b) Addition α + β and subtraction α - β are entrywise operations

Key properties (from the source text):
- "The addition operation + is associative and commutative"
- "The N-tuple 0 is its neutral element"
- "The subtraction operation − undoes +"
-/


section TupleAdditionAPI

variable (α β γ : Fin N → ℕ)

/-! #### Part (a): The zero N-tuple -/
/-! #### Part (b): Entrywise operations -/
/-! #### Algebraic properties of addition -/
/-! #### Subtraction undoes addition -/
/-! #### Interaction with N-partitions -/

end TupleAdditionAPI

/-- The staircase partition ρ = (N-1, N-2, ..., 1, 0). -/
def rho (N : ℕ) : Fin N → ℕ := fun i => N - 1 - i.val

/-! ## Tableaux and their content

We work with semistandard Young tableaux. The content of a tableau counts
how many times each value appears.

### Indexing Convention

**This file uses 1-indexed columns** for skew Young diagrams:
- A cell (i, j) is in Y(λ/μ) iff μ_i < j ≤ λ_i
- Column indices start at 1 (the first column is j = 1)
- This matches the textbook convention

**SchurBasics.lean uses 0-indexed columns**:
- A cell (i, j) is in Y(λ/μ) iff μ_i ≤ j < λ_i
- Column indices start at 0 (the first column is j = 0)
- This follows Mathlib/programming convention

**Conversion**: The bijection (i, j) ↔ (i, j+1) transforms between conventions.
See `SchurBasics.skewCellEquiv` and `SchurBasics.mem_skewYoungDiagram_iff_mem_LR_shifted`
for the explicit equivalences and conversion lemmas.
-/


/-- The skew Young diagram Y(lam/mu) as a set of cells.
    A cell (i,j) is in Y(lam/mu) if mu_i < j ≤ lam_i.
    
    **This is the `Set` version with 1-indexed columns (textbook convention).**
    The first column is j = 1, not j = 0.
    
    For the canonical `Finset` version with 0-indexed columns, see:
    - `NPartition.skewYoungDiagram` in NPartition.lean (canonical, no `[NeZero N]` required)
    - `skewYoungDiagram` in SchurBasics.lean (duplicate, requires `[NeZero N]`)
    
    Comparison:
    - Here: (i, j) ∈ Y(λ/μ) iff μ_i < j ≤ λ_i (1-indexed)
    - NPartition/SchurBasics: (i, j) ∈ Y(λ/μ) iff μ_i ≤ j < λ_i (0-indexed)
    
    The bijection between them is: (i, j) here ↔ (i, j-1) in NPartition/SchurBasics.
    See `SchurBasics.mem_skewYoungDiagram_iff_mem_LR_shifted` for the conversion lemma. -/
def skewYoungDiagram (lam mu : Fin N → ℕ) : Set (Fin N × ℕ) :=
  {c | mu c.1 < c.2 ∧ c.2 ≤ lam c.1}

end AlgebraicCombinatorics
