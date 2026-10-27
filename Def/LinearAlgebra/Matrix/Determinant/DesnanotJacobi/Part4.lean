/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Def.Data.Fin.SkipTwo
import Def.LinearAlgebra.Matrix.Determinant.PermFinset
import Lemma.Finset.PermFinset
import Theorem.LinearAlgebra.Matrix.Determinant.DesnanotJacobi.Part3
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

/-- The bijection between permutations mapping P to Q and pairs of permutations.
    
    Given σ with σ(P) = Q, we can extract:
    - τ : Perm (Fin |P|), the restriction of σ to P (viewed via orderIsoOfFin)
    - ρ : Perm (Fin |Pᶜ|), the restriction of σ to Pᶜ
    
    This bijection is the key to decomposing the sum over PermFinset.permsMapping. -/
noncomputable def permsMappingEquiv {m : ℕ} (P Q : Finset (Fin m)) 
    (hPQ : P.card = Q.card) :
    PermFinset.permsMapping P Q ≃ Equiv.Perm (Fin P.card) × Equiv.Perm (Fin Pᶜ.card) where
  toFun := fun ⟨σ, hσ⟩ => 
    let hσ' : PermFinset.imageFinset σ P = Q := by simp only [PermFinset.permsMapping, Finset.mem_filter] at hσ; exact hσ.2
    (restrictToPerm P Q hPQ σ hσ', restrictToPermCompl P Q hPQ σ hσ')
  invFun := fun ⟨τ, ρ⟩ => 
    ⟨constructPermFromPair P Q hPQ τ ρ, by
      simp only [PermFinset.permsMapping, Finset.mem_filter, Finset.mem_univ, true_and]
      exact constructPermFromPair_image P Q hPQ τ ρ⟩
  left_inv := fun ⟨σ, hσ⟩ => by
    simp only
    -- Need to show: constructPermFromPair P Q hPQ (restrictToPerm ...) (restrictToPermCompl ...) = σ
    have hσ' : PermFinset.imageFinset σ P = Q := by simp only [PermFinset.permsMapping, Finset.mem_filter] at hσ; exact hσ.2
    ext x
    unfold constructPermFromPair
    simp only [Equiv.trans_apply]
    -- Case split on whether x ∈ P or x ∈ Pᶜ
    by_cases hxP : x ∈ P
    · -- Case: x ∈ P
      have hx' : (finSumEquivOfFinset rfl rfl).symm x = Sum.inl ((P.orderIsoOfFin rfl).symm ⟨x, hxP⟩) := by
        apply (finSumEquivOfFinset rfl rfl).injective
        simp only [Equiv.apply_symm_apply, finSumEquivOfFinset_inl]
        rw [← Finset.coe_orderIsoOfFin_apply]
        simp only [OrderIso.apply_symm_apply, Subtype.coe_mk]
      rw [hx']
      simp only [Equiv.sumCongr_apply, Sum.map_inl, finSumEquivOfFinset_inl]
      have hk : (P.orderIsoOfFin rfl) ((P.orderIsoOfFin rfl).symm ⟨x, hxP⟩) = ⟨x, hxP⟩ := 
        OrderIso.apply_symm_apply _ _
      have hspec := restrictToPerm_spec P Q hPQ σ hσ' ((P.orderIsoOfFin rfl).symm ⟨x, hxP⟩)
      simp only [hk, Subtype.coe_mk] at hspec
      rw [← Finset.coe_orderIsoOfFin_apply Q rfl]
      simp only [hspec]
    · -- Case: x ∈ Pᶜ
      have hxPc : x ∈ Pᶜ := Finset.mem_compl.mpr hxP
      have hx' : (finSumEquivOfFinset rfl rfl).symm x = Sum.inr ((Pᶜ.orderIsoOfFin rfl).symm ⟨x, hxPc⟩) := by
        apply (finSumEquivOfFinset rfl rfl).injective
        simp only [Equiv.apply_symm_apply, finSumEquivOfFinset_inr]
        rw [← Finset.coe_orderIsoOfFin_apply]
        simp only [OrderIso.apply_symm_apply, Subtype.coe_mk]
      rw [hx']
      simp only [Equiv.sumCongr_apply, Sum.map_inr, finSumEquivOfFinset_inr]
      have hPcQc : Pᶜ.card = Qᶜ.card := by rw [Finset.card_compl, Finset.card_compl, hPQ]
      have hσc : PermFinset.imageFinset σ Pᶜ = Qᶜ := imageFinset_compl' hσ'
      have hk : (Pᶜ.orderIsoOfFin rfl) ((Pᶜ.orderIsoOfFin rfl).symm ⟨x, hxPc⟩) = ⟨x, hxPc⟩ := 
        OrderIso.apply_symm_apply _ _
      have hspec := restrictToPerm_spec Pᶜ Qᶜ hPcQc σ hσc ((Pᶜ.orderIsoOfFin rfl).symm ⟨x, hxPc⟩)
      simp only [hk, Subtype.coe_mk] at hspec
      unfold restrictToPermCompl
      rw [← Finset.coe_orderIsoOfFin_apply Qᶜ rfl]
      simp only [hspec]
  right_inv := fun ⟨τ, ρ⟩ => by
    simp only
    -- Need to show: (restrictToPerm ..., restrictToPermCompl ...) = (τ, ρ)
    -- This requires showing both components are equal
    have hPcQc : Pᶜ.card = Qᶜ.card := by rw [Finset.card_compl, Finset.card_compl, hPQ]
    ext1
    · -- Show restrictToPerm gives back τ
      ext i
      -- The key is that constructPermFromPair maps eP i to eQ (finCongr hPQ (τ i))
      have hi : (finSumEquivOfFinset (m := P.card) (n := Pᶜ.card) rfl rfl).symm 
                (P.orderIsoOfFin rfl i) = Sum.inl i := by
        apply (finSumEquivOfFinset rfl rfl).injective
        simp only [Equiv.apply_symm_apply, finSumEquivOfFinset_inl]; rfl
      have hσi : constructPermFromPair P Q hPQ τ ρ (P.orderIsoOfFin rfl i) = 
                 Q.orderIsoOfFin rfl (finCongr hPQ (τ i)) := by
        simp only [constructPermFromPair, Equiv.trans_apply, hi, Equiv.sumCongr_apply, 
                   Sum.map_inl, finSumEquivOfFinset_inl]
        rfl
      -- Now unfold restrictToPerm and show it extracts τ i
      unfold restrictToPerm
      simp only [Equiv.ofBijective_apply]
      have h_in_Q : constructPermFromPair P Q hPQ τ ρ (P.orderIsoOfFin rfl i) ∈ Q := by
        rw [hσi]; exact Finset.coe_mem _
      have h1 : ((Q.orderIsoOfFin rfl).symm ⟨constructPermFromPair P Q hPQ τ ρ 
                 (P.orderIsoOfFin rfl i), h_in_Q⟩ : Fin Q.card) = finCongr hPQ (τ i) := by
        have heq : (⟨_, h_in_Q⟩ : Q) = Q.orderIsoOfFin rfl (finCongr hPQ (τ i)) := 
          Subtype.ext hσi
        rw [heq]
        simp only [OrderIso.symm_apply_apply]
      simp only [h1, finCongr_apply, Fin.val_cast, Equiv.ofBijective_apply]
    · -- Show restrictToPermCompl gives back ρ (similar structure)
      ext j
      have hj : (finSumEquivOfFinset (m := P.card) (n := Pᶜ.card) rfl rfl).symm 
                (Pᶜ.orderIsoOfFin rfl j) = Sum.inr j := by
        apply (finSumEquivOfFinset rfl rfl).injective
        simp only [Equiv.apply_symm_apply, finSumEquivOfFinset_inr]; rfl
      have hσj : constructPermFromPair P Q hPQ τ ρ (Pᶜ.orderIsoOfFin rfl j) = 
                 Qᶜ.orderIsoOfFin rfl (finCongr hPcQc (ρ j)) := by
        simp only [constructPermFromPair, Equiv.trans_apply, hj, Equiv.sumCongr_apply, 
                   Sum.map_inr, finSumEquivOfFinset_inr]
        rfl
      unfold restrictToPermCompl restrictToPerm
      simp only [Equiv.ofBijective_apply]
      have h_in_Qc : constructPermFromPair P Q hPQ τ ρ (Pᶜ.orderIsoOfFin rfl j) ∈ Qᶜ := by
        rw [hσj]; exact Finset.coe_mem _
      have h1 : ((Qᶜ.orderIsoOfFin rfl).symm ⟨constructPermFromPair P Q hPQ τ ρ 
                 (Pᶜ.orderIsoOfFin rfl j), h_in_Qc⟩ : Fin Qᶜ.card) = finCongr hPcQc (ρ j) := by
        have heq : (⟨_, h_in_Qc⟩ : (Qᶜ : Finset (Fin m))) = Qᶜ.orderIsoOfFin rfl (finCongr hPcQc (ρ j)) := 
          Subtype.ext hσj
        rw [heq]
        simp only [OrderIso.symm_apply_apply]
      simp only [h1, finCongr_apply, Fin.val_cast, Equiv.ofBijective_apply]

/-!
## Desnanot-Jacobi Identity (Theorem thm.det.des-jac-1)

The Desnanot-Jacobi identity relates the determinant of a matrix to determinants
of its submatrices. This is the foundation of Dodgson condensation.

For an n×n matrix A with n ≥ 2, let A' be the (n-2)×(n-2) matrix obtained by
removing the first row, last row, first column, and last column. Then:

det(A) · det(A') = det(A_{~1,~1}) · det(A_{~n,~n}) - det(A_{~1,~n}) · det(A_{~n,~1})

The proof uses the relationship between the adjugate matrix and submatrix determinants.
The key insight is that the 2×2 determinant of the corner submatrix of adj(A)
equals det(A) · det(A') by Jacobi's complementary minor theorem.
-/


/-- The inner submatrix A' in the Desnanot-Jacobi identity:
    the (n-2)×(n-2) matrix obtained by removing first/last rows and columns.
    Label: thm.det.des-jac-1 -/
def innerSubmatrix {m : ℕ} (A : Matrix (Fin (m + 2)) (Fin (m + 2)) R) :
    Matrix (Fin m) (Fin m) R :=
  A.submatrix (fun i => i.succ.castSucc) (fun j => j.succ.castSucc)

end Determinants
end AlgebraicCombinatorics
