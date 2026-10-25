/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Def.Combinatorics.Enumerative.Partition.NPartition.Part9
import Def.Combinatorics.Young.MonomialSymmetric.Part6
import Theorem.Combinatorics.Young.LittlewoodRichardson.Part3
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

/-- The domain of col_{≥1}(T) is equivalent to the domain of T.

    This formalizes the note "col_{≥1}(T) = T for any tableau T" from the source:
    the two functions have equivalent domains and agree on corresponding elements. -/
def equivColGeqOne {lam mu : Fin N → ℕ} :
    {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} ≃
    {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu ∧ c.2 ≥ 1} where
  toFun := embedColGeqOne
  invFun := embedFromColGeqOne
  left_inv := embedFromColGeqOne_embedColGeqOne
  right_inv := embedColGeqOne_embedFromColGeqOne

/-- The embedding from the domain of col_{≥k}(T) to the domain of col_{≥j}(T) when j ≤ k. -/
def embedColGeq {lam mu : Fin N → ℕ} {j k : ℕ} (hjk : j ≤ k) :
    {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu ∧ c.2 ≥ k} →
    {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu ∧ c.2 ≥ j} :=
  fun c => ⟨c.val, ⟨c.prop.1, le_trans hjk c.prop.2⟩⟩

/-- The content of a restricted tableau col_{≥j}(T).
    Counts occurrences of each value in columns j and beyond. -/
noncomputable def contentColGeq {lam mu : Fin N → ℕ}
    (T : Tableau lam mu) (j : ℕ) : Fin N → ℕ := fun i =>
  Nat.card {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu ∧ c.2 ≥ j} // T ⟨c.val, c.prop.1⟩ = i}

/-! ## Yamanouchi tableaux

A semistandard tableau T is ν-Yamanouchi if ν + cont(col_{≥j}(T)) is an N-partition
for every positive integer j. -/


/-- A semistandard tableau T of shape λ/μ is ν-Yamanouchi if for each positive integer j,
    the N-tuple ν + cont(col_{≥j}(T)) is an N-partition (i.e., weakly decreasing).

    **Definition (def.sf.yamanouchi)**:
    Let λ, μ, ν be three N-partitions. A semistandard tableau T of shape λ/μ is said to be
    ν-Yamanouchi if for each positive integer j, the N-tuple ν + cont(col_{≥j}T) ∈ ℕ^N is
    an N-partition (i.e., weakly decreasing).

    **Key properties:**
    - The condition ensures that as we process the tableau column by column from right to left,
      starting with tally ν, the running tally always remains weakly decreasing.
    - For j = 1, we get that ν + cont(T) is an N-partition (see `IsYamanouchi.isNPartition_add_content`).
    - A 0-Yamanouchi tableau (also called a "ballot tableau") has content that is itself an N-partition.

    **Voting interpretation (rmk.sf.yamanouchi.votes):**
    Think of each entry i in T as a vote for candidate i. Starting with tally ν and counting votes
    column by column from right to left, the tally must remain weakly decreasing at every step.
    Since columns have distinct entries (strictly increasing), no candidate gains more than one
    vote at a time. -/
def IsYamanouchi {lam mu : Fin N → ℕ}
    (nu : Fin N → ℕ) (T : Tableau lam mu) : Prop :=
  IsSemistandard T ∧
  ∀ j : ℕ, j > 0 → IsNPartition (nu + contentColGeq T j)

end AlgebraicCombinatorics
