/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Def.Combinatorics.Enumerative.Partition.NPartition.Part9
import Def.Combinatorics.Young.MonomialSymmetric.Part6
import Abbrev.Combinatorics.Young.LittlewoodRichardson.Part3
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

/-- Count of free (k+1)'s in row i restricted to columns < j. -/
noncomputable def freeKSuccCountPrefix {lam mu : Fin N → ℕ} (T : Tableau lam mu) (i : Fin N)
    (k : Fin N) (hk : k.val + 1 < N) (j : ℕ) : ℕ :=
  Nat.card {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} //
    c.val.1 = i ∧ c.val.2 < j ∧ T c = ⟨k.val + 1, hk⟩ ∧ ¬isForcedKSucc T k hk c}

/-- Count of free k's in row i with column ≤ col, restricted to columns < j.
    Used for the parenthesis-matching algorithm in benderKnuthPrefixMatching. -/
noncomputable def freeKCountUpToPrefix {lam mu : Fin N → ℕ} (T : Tableau lam mu) (i : Fin N)
    (k : Fin N) (hk : k.val + 1 < N) (j : ℕ) (col : ℕ) : ℕ :=
  Nat.card {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} //
    c.val.1 = i ∧ c.val.2 ≤ col ∧ c.val.2 < j ∧ T c = k ∧ ¬isForcedK T k hk c}

/-- Count of free (k+1)'s in row i with column ≤ col, restricted to columns < j.
    Used for the parenthesis-matching algorithm in benderKnuthPrefixMatching. -/
noncomputable def freeKSuccCountUpToPrefix {lam mu : Fin N → ℕ} (T : Tableau lam mu) (i : Fin N)
    (k : Fin N) (hk : k.val + 1 < N) (j : ℕ) (col : ℕ) : ℕ :=
  Nat.card {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} //
    c.val.1 = i ∧ c.val.2 ≤ col ∧ c.val.2 < j ∧ T c = ⟨k.val + 1, hk⟩ ∧ ¬isForcedKSucc T k hk c}

/-- A free k at position c is "unmatched" within the column prefix (columns < j).

    This is the prefix-restricted version of `isUnmatchedFreeK`. The matching is computed
    using only free entries in columns < j, not the entire row.

    A free k is unmatched in the prefix iff at its position, the cumulative count of
    free k's (in the prefix) exceeds the TOTAL count of free (k+1)'s (in the prefix).

    **Usage**: Used by `benderKnuthPrefixMatching` to correctly preserve row-weak ordering. -/
def isUnmatchedFreeKPrefix {lam mu : Fin N → ℕ} (T : Tableau lam mu) (k : Fin N) (hk : k.val + 1 < N)
    (j : ℕ) (c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu}) : Prop :=
  c.val.2 < j ∧ T c = k ∧ ¬isForcedK T k hk c ∧
  freeKCountUpToPrefix T c.val.1 k hk j c.val.2 > freeKSuccCountPrefix T c.val.1 k hk j

/-- A free (k+1) at position c is "unmatched" within the column prefix (columns < j).

    This is the prefix-restricted version of `isUnmatchedFreeKSucc`. The matching is computed
    using only free entries in columns < j, not the entire row.

    A free (k+1) is unmatched in the prefix iff it's among the leftmost excess (k+1)'s,
    i.e., the cumulative count of free (k+1)'s up to c plus the total free k count
    is at most the total free (k+1) count (all counts restricted to the prefix).

    **Usage**: Used by `benderKnuthPrefixMatching` to correctly preserve row-weak ordering. -/
def isUnmatchedFreeKSuccPrefix {lam mu : Fin N → ℕ} (T : Tableau lam mu) (k : Fin N) (hk : k.val + 1 < N)
    (j : ℕ) (c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu}) : Prop :=
  c.val.2 < j ∧ T c = ⟨k.val + 1, hk⟩ ∧ ¬isForcedKSucc T k hk c ∧
  freeKCountPrefix T c.val.1 k hk j + freeKSuccCountUpToPrefix T c.val.1 k hk j c.val.2 ≤
    freeKSuccCountPrefix T c.val.1 k hk j

/-- A matched free k in the prefix (columns < j) is a free k that is not unmatched.
    In the parenthesis-matching algorithm restricted to the prefix, these are the k's
    that get paired with (k+1)'s. -/
def isMatchedFreeKPrefix {lam mu : Fin N → ℕ} (T : Tableau lam mu) (k : Fin N) (hk : k.val + 1 < N)
    (j : ℕ) (c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu}) : Prop :=
  c.val.2 < j ∧ T c = k ∧ ¬isForcedK T k hk c ∧ ¬isUnmatchedFreeKPrefix T k hk j c

/-- A matched free (k+1) in the prefix (columns < j) is a free (k+1) that is not unmatched.
    In the parenthesis-matching algorithm restricted to the prefix, these are the (k+1)'s
    that get paired with k's. -/
def isMatchedFreeKSuccPrefix {lam mu : Fin N → ℕ} (T : Tableau lam mu) (k : Fin N) (hk : k.val + 1 < N)
    (j : ℕ) (c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu}) : Prop :=
  c.val.2 < j ∧ T c = ⟨k.val + 1, hk⟩ ∧ ¬isForcedKSucc T k hk c ∧ ¬isUnmatchedFreeKSuccPrefix T k hk j c

/-! ### Cardinality lemmas for prefix-restricted matching

These lemmas establish cardinalities of matched/unmatched cells in the prefix,
analogous to `matchedFreeK_row_card` and `unmatchedFreeK_row_card` for the full-row version.

**Key results**:
- `matchedFreeKPrefix_row_card`: #{matched free k's in row i, prefix} = min(m, n)
- `unmatchedFreeKPrefix_row_card`: #{unmatched free k's in row i, prefix} = m - min(m, n)
- `matchedFreeKSuccPrefix_row_card`: #{matched free (k+1)'s in row i, prefix} = min(m, n)
- `unmatchedFreeKSuccPrefix_row_card`: #{unmatched free (k+1)'s in row i, prefix} = n - min(m, n)

where m = freeKCountPrefix T i k hk j and n = freeKSuccCountPrefix T i k hk j.

These are the prefix-restricted versions of the lemmas at lines 3244-3550. -/
/-! ### Helper lemmas for prefix-restricted matching

These lemmas establish key properties of `isUnmatchedFreeKPrefix` and `isUnmatchedFreeKSuccPrefix`
that are used by `benderKnuthPrefixMatching_row_weak_stembridge` and related proofs.

**Key insight**: In the prefix-restricted matching:
- Unmatched free k's are the RIGHTMOST excess free k's (after matching with free (k+1)'s)
- Unmatched free (k+1)'s are the LEFTMOST excess free (k+1)'s

This means if c₁ is unmatched free k and c₂ is unmatched free (k+1) in the same row,
then c₁.col > c₂.col (c₁ is to the right of c₂). This is crucial for row-weak preservation. -/
/-! ### Cross-boundary case analysis for benderKnuthPrefixMatching

The following lemma addresses the "cross-boundary" case in `benderKnuthPrefixMatching_row_weak_stembridge`:
when c₁ is in the prefix (col < j) and c₂ is in the suffix (col ≥ j).

**Problem**: If c₁ is unmatched free k in the prefix and T c₂ = k in the suffix,
then after transformation: T' c₁ = k+1 > k = T' c₂, violating row-weak.

**Key insight**: In the Stembridge involution, j is chosen as the largest violator column.
This means ν + cont(col_{≥j}(T)) is NOT a partition, but ν + cont(col_{≥j+1}(T)) IS a partition.
The misstep index k is chosen such that (ν + cont(col_{≥j}(T)))_k < (ν + cont(col_{≥j}(T)))_{k+1}.

This structure constrains what values can appear in which columns, potentially ruling out
the problematic cross-boundary case. -/

/-- Apply the Bender-Knuth involution BK_k to columns < j of a tableau (matching-based version).

    This definition uses `isUnmatchedFreeKPrefix` and `isUnmatchedFreeKSuccPrefix`
    (which compute matching restricted to columns < j) instead of simple free conditions.
    This is the correct definition that preserves row-weak ordering.

    The matching-based conditions ensure that only unmatched free entries are swapped,
    preserving the row-weak property. See `benderKnuthPrefixMatching_row_weak_stembridge` below. -/
noncomputable def benderKnuthPrefixMatching {lam mu : Fin N → ℕ} (k : Fin N) (hk : k.val + 1 < N)
    (j : ℕ) (T : Tableau lam mu) (_hT : IsSemistandard T) : Tableau lam mu := by
  classical
  exact fun c =>
    -- Only apply BK_k transformation to cells in columns < j
    if isUnmatchedFreeKPrefix T k hk j c then
      -- Unmatched free k → k+1
      ⟨k.val + 1, hk⟩
    else if isUnmatchedFreeKSuccPrefix T k hk j c then
      -- Unmatched free k+1 → k
      k
    else
      -- All other cells unchanged
      T c

end AlgebraicCombinatorics
