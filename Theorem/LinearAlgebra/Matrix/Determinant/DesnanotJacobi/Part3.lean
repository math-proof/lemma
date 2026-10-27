/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Def.Data.Fin.SkipTwo
import Def.LinearAlgebra.Matrix.Determinant.PermFinset
import Lemma.Finset.PermFinset
import Def.LinearAlgebra.Matrix.Determinant.DesnanotJacobi.Part3
open Matrix BigOperators Finset

/-!
# Determinants: Factor Hunting and Desnanot-Jacobi Identity

This file formalizes results from the "Factor hunting" and "Desnanot-Jacobi and Dodgson
condensation" sections of the determinants chapter.

## Main definitions

* `vandermondeMat`: The Vandermonde matrix with entries `a i ^ (n - j)`
* `cauchyMat`: The Cauchy matrix with entries `1 / (x i + y j)`

## Main results

### Vandermonde determinant (Theorem thm.det.vander)
* `vandermonde_det_a`: det(aᵢⁿ⁻ʲ) = ∏_{i<j} (aᵢ - aⱼ)
* `vandermonde_det_b`: det(aⱼⁿ⁻ⁱ) = ∏_{i<j} (aᵢ - aⱼ)
* `vandermonde_det_c`: det(aᵢʲ⁻¹) = ∏_{j<i} (aᵢ - aⱼ)
* `vandermonde_det_d`: det(aⱼⁱ⁻¹) = ∏_{j<i} (aᵢ - aⱼ)

### Proposition prop.det.(xi+yj)n-1
* `det_sum_pow`: det((xᵢ + yⱼ)ⁿ⁻¹) = (∏ₖ C(n-1,k)) · (∏_{i<j}(xᵢ-xⱼ)) · (∏_{i<j}(yⱼ-yᵢ))

### Laplace expansion (Theorem thm.det.laplace)
* `det_laplace_row`: det A = ∑_q (-1)^(p+q) A_{p,q} det(A_{~p,~q})
* `det_laplace_col`: det A = ∑_p (-1)^(p+q) A_{p,q} det(A_{~p,~q})

### Proposition prop.det.laplace.0
* `det_laplace_row_zero`: 0 = ∑_q (-1)^(p+q) A_{r,q} det(A_{~p,~q}) when p ≠ r
* `det_laplace_col_zero`: 0 = ∑_p (-1)^(p+q) A_{p,r} det(A_{~p,~q}) when q ≠ r

### Adjugate matrix (Definition def.det.adj, Theorem thm.det.adj.inverse)
* `adjugate`: The adjugate (classical adjoint) of a matrix
* `adjugate_mul`: A · adj(A) = det(A) · I
* `mul_adjugate`: adj(A) · A = det(A) · I

### Desnanot-Jacobi identity (Theorem thm.det.des-jac-1, thm.det.des-jac-2)
* `desnanot_jacobi`: det(A) · det(A') = det(A_{~1,~1}) · det(A_{~n,~n}) - det(A_{~1,~n}) · det(A_{~n,~1})
* `desnanot_jacobi_general`: Generalization with arbitrary rows p,q and columns u,v

### Cauchy determinant (Theorem thm.det.cauchy)
* `cauchy_det`: det(1/(xᵢ+yⱼ)) = ∏_{i<j}((xᵢ-xⱼ)(yᵢ-yⱼ)) / ∏_{i,j}(xᵢ+yⱼ)

### Jacobi's complementary minor theorem (Theorem thm.det.jacobi-complement)
* `jacobi_complementary_minor`: det(sub_P^Q(adj A)) = (-1)^(sum P + sum Q) · (det A)^(|Q|-1) · det(sub_{~Q}^{~P} A)

## References

* Source: DesnanotJacobi.tex (Factor hunting and Desnanot-Jacobi sections)

## Implementation notes

Many of these results are already in Mathlib under `Matrix.det_vandermonde`, `Matrix.adjugate`,
`Matrix.det_laplace_row`, etc. This file provides the statements matching the textbook
presentation and connects them to Mathlib's API.
-/


/-!
## Fin.succAbove computation lemmas

These simp lemmas allow efficient computation of `Fin.succAbove` for concrete Fin types.
They are used throughout this file for determinant expansions involving submatrices.
All lemmas are proved by `rfl` for maximum efficiency.
-/


/-!
## Fin 3 product lemmas

These lemmas simplify products over pairs and singletons in `Fin 3`.
They are used in Cauchy determinant computations for the n = 3 case.
-/


namespace AlgebraicCombinatorics

namespace Determinants

variable {R : Type*} [CommRing R]

variable {n : ℕ}

section SuccAboveLemmas

end SuccAboveLemmas

section Fin3ProductLemmas

variable {R : Type*} [CommMonoid R]

end Fin3ProductLemmas

/-- constructPermFromPair maps P to Q. -/
theorem constructPermFromPair_image {m : ℕ} (P Q : Finset (Fin m)) (hPQ : P.card = Q.card)
    (τ : Equiv.Perm (Fin P.card)) (ρ : Equiv.Perm (Fin Pᶜ.card)) :
    PermFinset.imageFinset (constructPermFromPair P Q hPQ τ ρ) P = Q := by
  have hPcQc : Pᶜ.card = Qᶜ.card := by rw [Finset.card_compl, Finset.card_compl, hPQ]
  simp only [PermFinset.imageFinset, constructPermFromPair]
  ext x
  simp only [Finset.mem_map, Function.Embedding.coeFn_mk]
  constructor
  · intro ⟨y, hy, hxy⟩
    have hy' : (finSumEquivOfFinset (m := P.card) (n := Pᶜ.card) rfl rfl).symm y = 
               Sum.inl ((P.orderIsoOfFin rfl).symm ⟨y, hy⟩) := by
      apply (finSumEquivOfFinset rfl rfl).injective
      simp only [Equiv.apply_symm_apply, finSumEquivOfFinset_inl]
      rw [← Finset.coe_orderIsoOfFin_apply]
      simp only [OrderIso.apply_symm_apply, Subtype.coe_mk]
    rw [Equiv.trans_apply, Equiv.trans_apply, Equiv.trans_apply, hy'] at hxy
    simp only [Equiv.sumCongr_apply, Sum.map_inl, finSumEquivOfFinset_inl] at hxy
    rw [← hxy]
    exact Finset.orderEmbOfFin_mem Q rfl _
  · intro hx
    let j : Fin Q.card := (Q.orderIsoOfFin rfl).symm ⟨x, hx⟩
    let k : Fin P.card := τ.symm (finCongr hPQ.symm j)
    use P.orderEmbOfFin rfl k
    constructor
    · exact Finset.orderEmbOfFin_mem P rfl k
    · simp only [Equiv.trans_apply]
      have hk' : (finSumEquivOfFinset (m := P.card) (n := Pᶜ.card) rfl rfl).symm 
                 (P.orderEmbOfFin rfl k) = Sum.inl k := by
        apply (finSumEquivOfFinset rfl rfl).injective
        simp only [Equiv.apply_symm_apply, finSumEquivOfFinset_inl]
      rw [hk']
      simp only [Equiv.sumCongr_apply, Sum.map_inl, finSumEquivOfFinset_inl]
      rw [← Finset.coe_orderIsoOfFin_apply]
      simp only [k, j, Equiv.apply_symm_apply, finCongr_apply, Fin.cast_cast,
                 Fin.cast_eq_self, OrderIso.apply_symm_apply, Subtype.coe_mk]

end Determinants
end AlgebraicCombinatorics
