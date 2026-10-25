/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Def.Combinatorics.Enumerative.Partition.NPartition.Part9
import Def.Combinatorics.Young.MonomialSymmetric.Part6
import Def.Combinatorics.Young.LittlewoodRichardson.Part9
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

/-- For an element s of a finset S, the filter cardinality equals its position + 1. -/
theorem filter_card_eq_symm_val (S : Finset ℕ) (s : S) :
    (S.filter (· ≤ s.val)).card = ((S.orderIsoOfFin rfl).symm s).val + 1 := by
  classical
  let g := S.orderIsoOfFin rfl
  let j := g.symm s
  have hs_eq : s = g j := (g.apply_symm_apply s).symm
  have s_val_eq : s.val = S.orderEmbOfFin rfl j := by rw [hs_eq]; rfl
  rw [s_val_eq]
  let f := S.orderEmbOfFin rfl
  have hf_strict_mono : StrictMono f := f.strictMono
  have h_eq2 : S.filter (· ≤ f j) = ((Finset.univ : Finset (Fin S.card)).filter (· ≤ j)).image f := by
    ext x
    simp only [mem_filter, mem_image, mem_univ, true_and]
    constructor
    · intro ⟨hx, hle⟩
      have hx_range : x ∈ Set.range f := by rw [range_orderEmbOfFin]; exact hx
      obtain ⟨i, rfl⟩ := hx_range
      refine ⟨i, ?_, rfl⟩
      by_contra h; push Not at h
      have : f j < f i := hf_strict_mono h
      omega
    · intro ⟨i, hi, hxi⟩
      constructor
      · rw [← hxi]; exact orderEmbOfFin_mem S rfl i
      · rw [← hxi]; exact hf_strict_mono.monotone hi
  rw [h_eq2, card_image_of_injective _ f.injective]
  have h3 : (Finset.univ : Finset (Fin S.card)).filter (· ≤ j) = Finset.Iic j := by
    ext i; simp [mem_filter, mem_Iic]
  rw [h3, Fin.card_Iic]

end AlgebraicCombinatorics
