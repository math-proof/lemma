/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Def.Data.Fin.SkipTwo
import Def.LinearAlgebra.Matrix.Determinant.PermFinset
import Lemma.Finset.PermFinset
import Theorem.LinearAlgebra.Matrix.Determinant.DesnanotJacobi.Part2
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

/-- Restriction to Pᶜ: given σ with σ '' P = Q, extract ρ : Perm (Fin Pᶜ.card). -/
noncomputable def restrictToPermCompl {m : ℕ} (P Q : Finset (Fin m)) (hPQ : P.card = Q.card) 
    (σ : Equiv.Perm (Fin m)) (hσ : PermFinset.imageFinset σ P = Q) : Equiv.Perm (Fin Pᶜ.card) := by
  have hPcQc : Pᶜ.card = Qᶜ.card := by rw [Finset.card_compl, Finset.card_compl, hPQ]
  have hσc : PermFinset.imageFinset σ Pᶜ = Qᶜ := imageFinset_compl' hσ
  exact restrictToPerm Pᶜ Qᶜ hPcQc σ hσc

/-- Construct σ from (τ, ρ): given τ : Perm (Fin P.card) and ρ : Perm (Fin Pᶜ.card),
    construct σ : Perm (Fin m) such that σ '' P = Q. -/
noncomputable def constructPermFromPair {m : ℕ} (P Q : Finset (Fin m)) (hPQ : P.card = Q.card)
    (τ : Equiv.Perm (Fin P.card)) (ρ : Equiv.Perm (Fin Pᶜ.card)) : Equiv.Perm (Fin m) := by
  have hPcQc : Pᶜ.card = Qᶜ.card := by rw [Finset.card_compl, Finset.card_compl, hPQ]
  let ePsum : Fin P.card ⊕ Fin Pᶜ.card ≃ Fin m := finSumEquivOfFinset rfl rfl
  let eQsum : Fin Q.card ⊕ Fin Qᶜ.card ≃ Fin m := finSumEquivOfFinset rfl rfl
  let castSum : Fin P.card ⊕ Fin Pᶜ.card ≃ Fin Q.card ⊕ Fin Qᶜ.card := 
    Equiv.sumCongr (finCongr hPQ) (finCongr hPcQc)
  let inner : Equiv.Perm (Fin P.card ⊕ Fin Pᶜ.card) := Equiv.sumCongr τ ρ
  exact ePsum.symm.trans (inner.trans (castSum.trans eQsum))

end Determinants
end AlgebraicCombinatorics
