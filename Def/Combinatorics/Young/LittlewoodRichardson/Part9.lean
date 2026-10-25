/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Def.Combinatorics.Enumerative.Partition.NPartition.Part9
import Def.Combinatorics.Young.MonomialSymmetric.Part6
import Instance.Combinatorics.Young.LittlewoodRichardson.Part4
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

/-! ## Bender-Knuth Involutions

The Bender-Knuth involutions are key tools for proving properties of Schur polynomials.
For each k ∈ [N-1], the k-th Bender-Knuth involution BK_k is a bijection on semistandard
tableaux that swaps certain k's and (k+1)'s while preserving the SSYT property.

### Definition

For a semistandard tableau T and k ∈ [N-1], the Bender-Knuth involution BK_k works as follows:
1. For each row i, consider the cells containing k or k+1
2. Partition these cells into "free" and "forced" based on column constraints:
   - A cell with value k is "forced" if the cell above it has value k
   - A cell with value k+1 is "forced" if the cell below it has value k+1
   - All other k's and (k+1)'s are "free"
3. In each row, swap the free k's with the free (k+1)'s

### Key Properties

1. **Involution**: BK_k ∘ BK_k = id
2. **Preserves SSYT**: If T is semistandard, so is BK_k(T)
3. **Content change**: cont(BK_k(T)) differs from cont(T) by swapping entries k and k+1
4. **Monomial change**: x_{BK_k(T)} = s_k · x_T where s_k swaps x_k and x_{k+1}

### References

- [Stanley, EC2, Section 7.10]
- [Fulton, Young Tableaux, Section 4.3]
- [Bender-Knuth, "Enumeration of plane partitions", 1972]
-/
/-! ### Helper function for swapping adjacent values -/


/-- Swap adjacent values k and k+1 in a Fin N. -/
def swapAdjacentFin (k : Fin N) (hk : k.val + 1 < N) (v : Fin N) : Fin N :=
  if v = k then ⟨k.val + 1, hk⟩
  else if v = ⟨k.val + 1, hk⟩ then k
  else v

/-- In row i of tableau T, count the number of cells with value k.
    This is used to define the Bender-Knuth involution. -/
noncomputable def rowCount {lam mu : Fin N → ℕ} (T : Tableau lam mu) (i : Fin N) (k : Fin N) : ℕ :=
  Nat.card {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} // c.val.1 = i ∧ T c = k}

/-- A cell containing k is "k-forced" if there's a k+1 directly BELOW it in the same column.
    This means the k and the k+1 below it form a "pair" that won't be swapped by BK_k.

    **Note**: The original (incorrect) definition said "k above k", but in a semistandard tableau,
    entries strictly increase down columns, so you can't have the same value in vertically
    adjacent cells. The correct definition is: k is paired with k+1 below it. -/
def isForcedK {lam mu : Fin N → ℕ} (T : Tableau lam mu) (k : Fin N) (hk : k.val + 1 < N)
    (c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu}) : Prop :=
  T c = k ∧
  ∃ (c_below : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu}),
    c_below.val.2 = c.val.2 ∧ -- same column
    c.val.1.val + 1 = c_below.val.1.val ∧ -- row below (c.row + 1 = c_below.row)
    T c_below = ⟨k.val + 1, hk⟩

/-- A cell containing k+1 is "(k+1)-forced" if there's a k directly ABOVE it in the same column.
    This means the k above and this k+1 form a "pair" that won't be swapped by BK_k.

    **Note**: The original (incorrect) definition said "k+1 below k+1", but in a semistandard
    tableau, entries strictly increase down columns. The correct definition is: k+1 is paired
    with k above it. -/
def isForcedKSucc {lam mu : Fin N → ℕ} (T : Tableau lam mu) (k : Fin N) (hk : k.val + 1 < N)
    (c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu}) : Prop :=
  T c = ⟨k.val + 1, hk⟩ ∧
  ∃ (c_above : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu}),
    c_above.val.2 = c.val.2 ∧ -- same column
    c_above.val.1.val + 1 = c.val.1.val ∧ -- row above (c_above.row + 1 = c.row)
    T c_above = k

/-- A cell containing k or k+1 is "free" if it is not forced.
    Free cells can be swapped by the Bender-Knuth involution. -/
def isFreeCell {lam mu : Fin N → ℕ} (T : Tableau lam mu) (k : Fin N) (hk : k.val + 1 < N)
    (c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu}) : Prop :=
  (T c = k ∧ ¬isForcedK T k hk c) ∨
  (T c = ⟨k.val + 1, hk⟩ ∧ ¬isForcedKSucc T k hk c)

/-- Count of free k's in row i. -/
noncomputable def freeKCount {lam mu : Fin N → ℕ} (T : Tableau lam mu) (i : Fin N)
    (k : Fin N) (hk : k.val + 1 < N) : ℕ :=
  Nat.card {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} //
    c.val.1 = i ∧ T c = k ∧ ¬isForcedK T k hk c}

/-- Count of free (k+1)'s in row i. -/
noncomputable def freeKSuccCount {lam mu : Fin N → ℕ} (T : Tableau lam mu) (i : Fin N)
    (k : Fin N) (hk : k.val + 1 < N) : ℕ :=
  Nat.card {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} //
    c.val.1 = i ∧ T c = ⟨k.val + 1, hk⟩ ∧ ¬isForcedKSucc T k hk c}

/-- Count of free k's in row i with column strictly less than j.
    Used for the parenthesis-matching algorithm in Bender-Knuth. -/
noncomputable def freeKCountBefore {lam mu : Fin N → ℕ} (T : Tableau lam mu) (i : Fin N)
    (k : Fin N) (hk : k.val + 1 < N) (j : ℕ) : ℕ :=
  Nat.card {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} //
    c.val.1 = i ∧ c.val.2 < j ∧ T c = k ∧ ¬isForcedK T k hk c}

/-- Count of free k's in row i with column at most j.
    Used for the parenthesis-matching algorithm in Bender-Knuth. -/
noncomputable def freeKCountUpTo {lam mu : Fin N → ℕ} (T : Tableau lam mu) (i : Fin N)
    (k : Fin N) (hk : k.val + 1 < N) (j : ℕ) : ℕ :=
  Nat.card {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} //
    c.val.1 = i ∧ c.val.2 ≤ j ∧ T c = k ∧ ¬isForcedK T k hk c}

/-- Count of free (k+1)'s in row i with column at most j.
    Used for the parenthesis-matching algorithm in Bender-Knuth. -/
noncomputable def freeKSuccCountUpTo {lam mu : Fin N → ℕ} (T : Tableau lam mu) (i : Fin N)
    (k : Fin N) (hk : k.val + 1 < N) (j : ℕ) : ℕ :=
  Nat.card {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} //
    c.val.1 = i ∧ c.val.2 ≤ j ∧ T c = ⟨k.val + 1, hk⟩ ∧ ¬isForcedKSucc T k hk c}

/-- A free k at position c is "unmatched" in the parenthesis-matching sense.

    The Bender-Knuth involution uses a parenthesis-matching algorithm:
    - Read free entries left-to-right in each row
    - Each free (k+1) matches with the nearest unmatched free k to its left
    - Unmatched entries get swapped

    A free k is unmatched iff at its position, the cumulative count of free k's exceeds
    the TOTAL count of free (k+1)'s in the row. In other words, there aren't enough (k+1)'s
    in the entire row to match all the k's up to this position.

    This definition correctly implements the standard parenthesis-matching algorithm:
    - Unmatched k's are exactly those at positions where there's an "excess" of k's
    - These are the rightmost free k's that don't have a (k+1) to match with
    
    Note: We compare freeKCountUpTo(c) with freeKSuccCount (total), not freeKSuccCountUpTo(c),
    because a k can match with any (k+1) to its right, not just (k+1)'s up to its position. -/
def isUnmatchedFreeK {lam mu : Fin N → ℕ} (T : Tableau lam mu) (k : Fin N) (hk : k.val + 1 < N)
    (c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu}) : Prop :=
  T c = k ∧ ¬isForcedK T k hk c ∧
  freeKCountUpTo T c.val.1 k hk c.val.2 > freeKSuccCount T c.val.1 k hk

/-- A free (k+1) at position c is "unmatched" in the parenthesis-matching sense.

    In the BK involution on a semistandard row with `a` free k's followed by `b` free (k+1)'s:
    - If b > a: the LEFTMOST (b-a) free (k+1)'s are unmatched → become k
    - If a ≥ b: all free (k+1)'s are matched (paired with the rightmost b free k's)

    A free (k+1) at position c is unmatched iff it's among the leftmost (b-a) free (k+1)'s,
    i.e., the cumulative count of free (k+1)'s up to c is at most (b-a).

    Equivalently: `freeKSuccCountUpTo(c) + freeKCount ≤ freeKSuccCount`

    This marks the LEFTMOST excess (k+1)'s as unmatched, which is correct for the BK involution.
    The matched pairs are: leftmost min(a,b) k's paired with rightmost min(a,b) (k+1)'s.

    Note: The previous (incorrect) definition used `freeKSuccCountUpTo > freeKCountUpTo`,
    which marked RIGHTMOST (k+1)'s as unmatched — the wrong polarity. -/
def isUnmatchedFreeKSucc {lam mu : Fin N → ℕ} (T : Tableau lam mu) (k : Fin N) (hk : k.val + 1 < N)
    (c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu}) : Prop :=
  T c = ⟨k.val + 1, hk⟩ ∧ ¬isForcedKSucc T k hk c ∧
  freeKCount T c.val.1 k hk + freeKSuccCountUpTo T c.val.1 k hk c.val.2 ≤ freeKSuccCount T c.val.1 k hk

/-- A matched free k is a free k that is not unmatched.
    In the parenthesis-matching algorithm, these are the k's that get paired with (k+1)'s. -/
def isMatchedFreeK {lam mu : Fin N → ℕ} (T : Tableau lam mu) (k : Fin N) (hk : k.val + 1 < N)
    (c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu}) : Prop :=
  T c = k ∧ ¬isForcedK T k hk c ∧ ¬isUnmatchedFreeK T k hk c

/-- A matched free (k+1) is a free (k+1) that is not unmatched.
    In the parenthesis-matching algorithm, these are the (k+1)'s that get paired with k's. -/
def isMatchedFreeKSucc {lam mu : Fin N → ℕ} (T : Tableau lam mu) (k : Fin N) (hk : k.val + 1 < N)
    (c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu}) : Prop :=
  T c = ⟨k.val + 1, hk⟩ ∧ ¬isForcedKSucc T k hk c ∧ ¬isUnmatchedFreeKSucc T k hk c

/-- The Bender-Knuth involution BK_k on semistandard tableaux.

    This involution swaps UNMATCHED free k's with UNMATCHED free (k+1)'s in each row,
    using a parenthesis-matching algorithm that preserves semistandardness.

    **Algorithm** (for each row independently):
    1. Identify all "free" entries (k's not paired with k+1 below, (k+1)'s not paired with k above)
    2. Read free entries left-to-right, matching each (k+1) with nearest unmatched k to its left
    3. Swap only the UNMATCHED entries: unmatched k → k+1, unmatched (k+1) → k

    **Why this preserves row-weak ordering**:
    - Matched pairs don't change
    - Unmatched k's (which become k+1) are always to the RIGHT of all matched (k+1)'s
    - Unmatched (k+1)'s (which become k) are always to the LEFT of all matched k's

    **Key theorem**: This is an involution that preserves semistandardness
    and swaps the counts of k and k+1 in the content.

    **Note**: The naive cell-by-cell swap (swapping ALL free entries) is INCORRECT
    because adjacent free k and free (k+1) would become (k+1, k), violating row-weak ordering.
    The parenthesis-matching ensures only non-adjacent free entries get swapped. -/
noncomputable def benderKnuth {lam mu : Fin N → ℕ} (k : Fin N) (hk : k.val + 1 < N)
    (T : Tableau lam mu) (_hT : IsSemistandard T) : Tableau lam mu := by
  classical
  exact fun c =>
    if isUnmatchedFreeK T k hk c then
      ⟨k.val + 1, hk⟩
    else if isUnmatchedFreeKSucc T k hk c then
      k
    else
      T c

/-! ### Key lemmas for benderKnuth_involutive

The proof of involutivity requires showing that the matching structure is preserved
under BK. The key insights are:

1. **Matching symmetry**: If a free k at position c is matched with a free (k+1) at
   position c', then after BK, both stay as their original values (k and k+1).

2. **Unmatched symmetry**: An unmatched free k becomes an unmatched free (k+1) in T',
   and an unmatched free (k+1) becomes an unmatched free k in T'.

3. **Row-weak preservation**: In each row, the ordering of entries is preserved because:
   - Unmatched (k+1)'s (→ k) are to the LEFT of matched entries
   - Unmatched k's (→ k+1) are to the RIGHT of matched entries

4. **Column-strict preservation**: Forced pairs stay together, and free cells in the
   same column have the same matching status (since they're in the same row).
-/
/-! ### Partner functions for forced cells

Forced k cells and forced (k+1) cells come in pairs: each forced k has exactly one
forced (k+1) directly below it, and vice versa. These helper functions extract the
partner cell, which is useful for proving the content swap property. -/


/-- The cell below a forced k cell. This is well-defined because the existence is witnessed. -/
noncomputable def forcedK_partner {lam mu : Fin N → ℕ}
    (T : Tableau lam mu) (k : Fin N) (hk : k.val + 1 < N)
    (c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu})
    (hc : isForcedK T k hk c) : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} :=
  Classical.choose hc.2

/-- The cell above a forced (k+1) cell. -/
noncomputable def forcedKSucc_partner {lam mu : Fin N → ℕ}
    (T : Tableau lam mu) (k : Fin N) (hk : k.val + 1 < N)
    (c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu})
    (hc : isForcedKSucc T k hk c) : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} :=
  Classical.choose hc.2

/-- The set of cells where T c = k and c is not an unmatched free k.
    This includes forced k cells and matched free k cells. -/
def notUnmatchedK {lam mu : Fin N → ℕ} (T : Tableau lam mu) (k : Fin N) (hk : k.val + 1 < N) :
    Set {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} :=
  {c | T c = k ∧ ¬isUnmatchedFreeK T k hk c}

/-- The set of cells where T c = k+1 and c is not an unmatched free (k+1).
    This includes forced (k+1) cells and matched free (k+1) cells. -/
def notUnmatchedKSucc {lam mu : Fin N → ℕ} (T : Tableau lam mu) (k : Fin N) (hk : k.val + 1 < N) :
    Set {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} :=
  {c | T c = ⟨k.val + 1, hk⟩ ∧ ¬isUnmatchedFreeKSucc T k hk c}

end AlgebraicCombinatorics
