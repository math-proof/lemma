/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Def.Combinatorics.Enumerative.Partition.NPartition.Part9
import Def.Combinatorics.Young.MonomialSymmetric.Part6
import Theorem.Combinatorics.Young.LittlewoodRichardson.Part7
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

/-- Stembridge's involution on non-Yamanouchi tableaux.
    For T not ν-Yamanouchi:
    1. Let j = findViolatorColumn ν T (largest column where ν + cont(col_{≥j}(T)) is not a partition)
    2. Let k = findMisstepIndex ν T j (smallest index where the partition condition fails)
    3. Apply BK_k to columns 1, ..., j-1 of T using benderKnuthPrefixMatching

    This involution pairs non-Yamanouchi tableaux such that their alternant
    contributions cancel.

    **Key insight**: The violator column j and misstep index k are the same for T and T'
    because benderKnuthPrefixMatching leaves columns ≥ j unchanged.
    This ensures the involution is well-defined and pairs tableaux correctly.

    **Implementation note**: We use the helper functions findViolatorColumn and findMisstepIndex
    to extract j and k, then apply benderKnuthPrefixMatching. The proofs that these functions return
    valid values (Some j, Some k) follow from the non-Yamanouchi assumption.

    **Implementation**: Uses `violatorColumns_nonempty_of_not_yamanouchi` to find j,
    `misstepSet_nonempty_of_not_partition` to find k, then applies `benderKnuthPrefixMatching k j T`. -/
noncomputable def stembridgeInvolution {lam mu : Fin N → ℕ} (nu : Fin N → ℕ)
    (T : Tableau lam mu) (hT : IsSemistandard T) (hnotYam : ¬IsYamanouchi nu T) :
    Tableau lam mu := by
  classical
  -- Step 1: Find the violator column j using violatorColumns_nonempty_of_not_yamanouchi
  have hviolator : (violatorColumns nu T).Nonempty :=
    violatorColumns_nonempty_of_not_yamanouchi hT hnotYam
  let j := (violatorColumns nu T).max' hviolator
  -- Step 2: Get the tuple α = ν + cont(col_{≥j}(T)) and show it's not a partition
  let α := nu + contentColGeq T j
  have hnotPart : ¬IsNPartition α := by
    -- j is a violator column, so ν + cont(col_{≥j}(T)) is not a partition
    have hj_mem : j ∈ violatorColumns nu T := Finset.max'_mem _ hviolator
    simp only [violatorColumns, Finset.mem_filter] at hj_mem
    exact hj_mem.2.2
  -- Step 3: Find the misstep index k
  have hmisstep : (misstepSet α).Nonempty := misstepSet_nonempty_of_not_partition hnotPart
  let k := (misstepSet α).min' hmisstep
  -- Step 4: Extract the bound k.val + 1 < N from the misstep property
  have hk_mem : k ∈ misstepSet α := Finset.min'_mem _ hmisstep
  have hk : k.val + 1 < N := by
    simp only [misstepSet, Finset.mem_filter, Finset.mem_univ, true_and] at hk_mem
    exact hk_mem.choose
  -- Step 5: Apply benderKnuthPrefixMatching k j T (using matching-based version)
  exact benderKnuthPrefixMatching k hk j T hT

/-! ### Matching-based Stembridge involution

The `stembridgeInvolutionMatching` definition is an alternative to `stembridgeInvolution` that
explicitly requires partition hypotheses. Both use `benderKnuthPrefixMatching` internally.

**Port status**: Complete. (The port to matching-based BK was completed and old code removed.)
- `stembridgeInvolutionMatching`: Definition using matching-based BK ✓
- Involutivity: Uses `benderKnuthPrefixMatching_involutive_stembridge` which is sorry-free

**Key difference from `stembridgeInvolution`**:
- Requires `hlam : IsNPartition lam`, `hmu : IsNPartition mu`, and `hnu : IsNPartition nu` parameters
- Uses matching-based conditions to determine which cells to swap
-/


/-- Stembridge's involution using matching-based Bender-Knuth (version with explicit partition hypotheses).

    This version of the Stembridge involution explicitly requires partition hypotheses for
    `lam`, `mu`, and `nu`. The matching-based approach correctly preserves row-weak
    ordering by only swapping unmatched free entries.

    **Parameters**:
    - `hlam`, `hmu`: Partition hypotheses needed for the matching-based BK to preserve semistandardness
    - `hnu`: Partition hypothesis for ν (needed to prove β is a partition when j is max violator)
    - `nu`: The ν parameter for the Yamanouchi condition
    - `T`: Input semistandard tableau
    - `hnotYam`: Proof that T is not ν-Yamanouchi

    **Implementation**: Same as `stembridgeInvolution`, but uses `benderKnuthPrefixMatching`
    in the final step. -/
noncomputable def stembridgeInvolutionMatching {lam mu : Fin N → ℕ}
    (_hlam : IsNPartition lam) (_hmu : IsNPartition mu)
    (nu : Fin N → ℕ) (_hnu : IsNPartition nu)
    (T : Tableau lam mu) (hT : IsSemistandard T) (hnotYam : ¬IsYamanouchi nu T) :
    Tableau lam mu := by
  classical
  -- Step 1: Find the violator column j using violatorColumns_nonempty_of_not_yamanouchi
  have hviolator : (violatorColumns nu T).Nonempty :=
    violatorColumns_nonempty_of_not_yamanouchi hT hnotYam
  let j := (violatorColumns nu T).max' hviolator
  -- Step 2: Get the tuple α = ν + cont(col_{≥j}(T)) and show it's not a partition
  let α := nu + contentColGeq T j
  have hnotPart : ¬IsNPartition α := by
    have hj_mem : j ∈ violatorColumns nu T := Finset.max'_mem _ hviolator
    simp only [violatorColumns, Finset.mem_filter] at hj_mem
    exact hj_mem.2.2
  -- Step 3: Find the misstep index k
  have hmisstep : (misstepSet α).Nonempty := misstepSet_nonempty_of_not_partition hnotPart
  let k := (misstepSet α).min' hmisstep
  -- Step 4: Extract the bound k.val + 1 < N from the misstep property
  have hk_mem : k ∈ misstepSet α := Finset.min'_mem _ hmisstep
  have hk : k.val + 1 < N := by
    simp only [misstepSet, Finset.mem_filter, Finset.mem_univ, true_and] at hk_mem
    exact hk_mem.choose
  -- Step 5: Apply benderKnuthPrefixMatching k j T (the correct matching-based version)
  exact benderKnuthPrefixMatching k hk j T hT

end AlgebraicCombinatorics
