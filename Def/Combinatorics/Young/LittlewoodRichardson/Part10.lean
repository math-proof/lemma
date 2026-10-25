/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Def.Combinatorics.Enumerative.Partition.NPartition.Part9
import Def.Combinatorics.Young.MonomialSymmetric.Part6
import Theorem.Combinatorics.Young.LittlewoodRichardson.Part5
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

/-- Equivalence between elements with bounded filter count and positions with bounded index.
    This is the key bijection for counting matched cells. -/
noncomputable def count_filter_equiv (S : Finset ℕ) (n : ℕ) : 
    {s : S // (S.filter (· ≤ s.val)).card ≤ n} ≃ {j : Fin S.card // j.val + 1 ≤ n} := by
  classical
  let g := S.orderIsoOfFin rfl
  refine {
    toFun := fun ⟨s, hcount⟩ => ⟨g.symm s, ?_⟩
    invFun := fun ⟨j, hj⟩ => ⟨g j, ?_⟩
    left_inv := ?_
    right_inv := ?_
  }
  · rw [← filter_card_eq_symm_val S s]; exact hcount
  · have h := filter_card_eq_symm_val S (g j)
    have hj_eq : (g.symm (g j)) = j := g.symm_apply_apply j
    rw [hj_eq] at h; omega
  · intro ⟨s, hs⟩; simp only [Subtype.mk.injEq]; exact g.apply_symm_apply s
  · intro ⟨j, hj⟩; simp only [Subtype.mk.injEq]; exact g.symm_apply_apply j

/-! ### Free k cells and column ordering

The following section documents the structure needed to prove `matchedFreeK_card_eq_matchedFreeKSucc_card`.

**Key insight:** Free k cells in a given row can be ordered by column. If we denote the
columns of free k cells in row i as c₁ < c₂ < ... < cₘ, then:
- `freeKCountUpTo(cⱼ) = j` for each j (by definition of freeKCountUpTo)
- A free k cell at column cⱼ is matched iff `freeKCountUpTo(cⱼ) ≤ freeKSuccCount`, i.e., `j ≤ n`
- There are `min(m, n)` such cells

The formal proof requires:
1. Showing that free k columns in row i form a finset S
2. Using `S.orderEmbOfFin` to establish the bijection with `Fin m`
3. Showing that `freeKCountUpTo` at the j-th column equals j+1 (via `count_le_nth_smallest`)
4. Applying `matched_position_count` to count matched cells

The helper lemmas `count_le_nth_smallest` and `matched_position_count` provide the counting
infrastructure. The remaining work is to formalize the bijection between free k cells and
their position in the column ordering.
-/

/-- The finset of columns of free k cells in row i.
    This is the key connection between the subtype-based definition of freeKCountUpTo
    and the finset-based counting lemmas. -/
noncomputable def freeKCols {lam mu : Fin N → ℕ} (T : Tableau lam mu) 
    (i : Fin N) (k : Fin N) (hk : k.val + 1 < N) : Finset ℕ := by
  classical
  haveI : Fintype {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} := skewYoungDiagram_fintype lam mu
  exact (Finset.univ.filter (fun c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} =>
    c.val.1 = i ∧ T c = k ∧ ¬isForcedK T k hk c)).image (fun c => c.val.2)

/-- Given a column in freeKCols, return the corresponding free k cell.
    This is the inverse of the column map used in the bijection. -/
noncomputable def cellOfFreeKCol {lam mu : Fin N → ℕ} (T : Tableau lam mu) 
    (i : Fin N) (k : Fin N) (hk : k.val + 1 < N) 
    (s : ↑(freeKCols T i k hk)) : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} := by
  classical
  haveI : Fintype {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} := skewYoungDiagram_fintype lam mu
  have hs : s.val ∈ freeKCols T i k hk := s.property
  simp only [freeKCols, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hs
  exact Classical.choose hs

/-! ### Free (k+1) cells and column ordering

Similar to the free k cell infrastructure, we define helpers for free (k+1) cells.
The key difference is that for free (k+1) cells, the matched condition involves
`freeKCountBefore` rather than `freeKSuccCount`. -/


/-- The finset of columns of free (k+1) cells in row i. -/
noncomputable def freeKSuccCols {lam mu : Fin N → ℕ} (T : Tableau lam mu) 
    (i : Fin N) (k : Fin N) (hk : k.val + 1 < N) : Finset ℕ := by
  classical
  haveI : Fintype {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} := skewYoungDiagram_fintype lam mu
  exact (Finset.univ.filter (fun c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} =>
    c.val.1 = i ∧ T c = ⟨k.val + 1, hk⟩ ∧ ¬isForcedKSucc T k hk c)).image (fun c => c.val.2)

/-- Given a column in freeKSuccCols, return the corresponding free (k+1) cell. -/
noncomputable def cellOfFreeKSuccCol {lam mu : Fin N → ℕ} (T : Tableau lam mu) 
    (i : Fin N) (k : Fin N) (hk : k.val + 1 < N) 
    (s : ↑(freeKSuccCols T i k hk)) : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} := by
  classical
  haveI : Fintype {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} := skewYoungDiagram_fintype lam mu
  have hs : s.val ∈ freeKSuccCols T i k hk := s.property
  simp only [freeKSuccCols, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hs
  exact Classical.choose hs

end AlgebraicCombinatorics
