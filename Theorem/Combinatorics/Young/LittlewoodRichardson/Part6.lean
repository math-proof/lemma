/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Def.Combinatorics.Enumerative.Partition.NPartition.Part9
import Def.Combinatorics.Young.MonomialSymmetric.Part6
import Def.Combinatorics.Young.LittlewoodRichardson.Part10
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

/-! ### Per-row count swap lemmas for Bender-Knuth

These lemmas establish that applying Bender-Knuth swaps the counts of free k's and free (k+1)'s
in each row. This is the key fact needed to prove that matched cells stay matched after BK. -/
/-! ### Content swap proof structure

The key insight for `benderKnuth_content_swap` is:

**Decomposition of cells by type:**
- `{c | T c = k}` = `{forced k}` ⊔ `{free k}`
- `{c | T c = k+1}` = `{forced (k+1)}` ⊔ `{free (k+1)}`

**Forced pairs bijection:**
Forced k and forced (k+1) cells are in bijection: each forced k cell has a unique
(k+1) directly below it, and vice versa. So `|forced k| = |forced (k+1)|`.

**Free cell transformation by BK:**
In each row with m free k's and n free (k+1)'s:
- min(m,n) pairs are "matched" (paired by parenthesis matching)
- max(0, m-n) free k's are "unmatched" → become (k+1)
- max(0, n-m) free (k+1)'s are "unmatched" → become k
- After BK: new free k count = n, new free (k+1) count = m

**Content swap:**
```
cont(T')_k = |forced k| + |new free k|
          = |forced k| + Σ_rows (free (k+1) count in row)
          = |forced (k+1)| + |free (k+1)|
          = cont(T)_{k+1}
```
Similarly for cont(T')_{k+1} = cont(T)_k.
-/
/-! ## Stembridge's Involution for Non-Yamanouchi Tableaux

For Stembridge's lemma, we need a sign-reversing involution on non-Yamanouchi tableaux.
Given a tableau T that is not ν-Yamanouchi:
1. Find the largest "violator" column j (where ν + cont(col_{≥j}(T)) fails to be a partition)
2. Find the smallest "misstep" index k (where the partition condition fails)
3. Apply Bender-Knuth BK_k to columns 1, ..., j-1

This involution has the property that the paired tableaux contribute opposite signs
to the alternant sum, causing them to cancel. -/


/-- When j is beyond all columns in the diagram, contentColGeq T j = 0. -/
theorem contentColGeq_eq_zero_of_large {lam mu : Fin N → ℕ}
    (T : Tableau lam mu) (j : ℕ) (hj : ∀ i : Fin N, lam i < j) :
    contentColGeq T j = 0 := by
  ext i
  unfold contentColGeq
  simp only [Pi.zero_apply]
  rw [Nat.card_eq_zero]
  left
  constructor
  intro ⟨⟨c, hc_mem, hc_col⟩, _⟩
  have hc_le : c.2 ≤ lam c.1 := hc_mem.2
  have hc_lt : lam c.1 < j := hj c.1
  omega

end AlgebraicCombinatorics
