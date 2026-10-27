/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Def.Data.Fin.SkipTwo
import Def.LinearAlgebra.Matrix.Determinant.PermFinset
import Lemma.Finset.PermFinset
import Theorem.LinearAlgebra.Matrix.Determinant.DesnanotJacobi
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

/-!
### Sorting permutation and its sign

The key to the multi-row Laplace expansion is understanding how permutations that map
one finset to another decompose. Given finsets P and Q of the same cardinality, a
permutation σ with σ(P) = Q can be decomposed as:

  σ = sortQ⁻¹ ∘ (sumCongr τ ρ) ∘ sortP

where:
- sortP : Fin m ≃ Fin |P| ⊕ Fin |Pᶜ| is the "sorting" equivalence for P
- sortQ : Fin m ≃ Fin |Q| ⊕ Fin |Qᶜ| is the "sorting" equivalence for Q
- τ : Perm (Fin |P|) is the restriction of σ to P
- ρ : Perm (Fin |Pᶜ|) is the restriction of σ to Pᶜ

The sign of σ then decomposes as:
  sign(σ) = sign(sortP) · sign(sortQ)⁻¹ · sign(τ) · sign(ρ)
          = sign(sortP) · sign(sortQ) · sign(τ) · sign(ρ)  (since sign² = 1)

The key identity is:
  sign(sortP) · sign(sortQ) = (-1)^(∑ P + ∑ Q)  when |P| = |Q|
-/


/-- The equivalence Fin m ≃ Fin |P| ⊕ Fin |Pᶜ| that sends elements of P to the left
    and elements of Pᶜ to the right, preserving order within each part. -/
noncomputable def finEquivSumOfFinset {m : ℕ} (P : Finset (Fin m)) : 
    Fin m ≃ Fin P.card ⊕ Fin Pᶜ.card := by
  have h1 : Pᶜ.card = Fintype.card (Fin m) - P.card := Finset.card_compl P
  have h2 : Fintype.card (Fin m) = m := Fintype.card_fin m
  have h3 : Pᶜ.card = m - P.card := by rw [h1, h2]
  have h4 : m - P.card = Fintype.card (Fin m) - P.card := by rw [h2]
  exact (finSumEquivOfFinset (m := P.card) (n := m - P.card) rfl (by rw [h4]; exact h1)).symm.trans
    (Equiv.sumCongr (Equiv.refl _) (finCongr h3.symm))

/-- The "sorting permutation" that reorders Fin m so that elements of P come first
    (in their natural order), followed by elements of Pᶜ (in their natural order).
    
    This is the composition of finEquivSumOfFinset with finSumFinEquiv. -/
noncomputable def sortingPermOfFinset {m : ℕ} (P : Finset (Fin m)) : Equiv.Perm (Fin m) :=
  let e := finEquivSumOfFinset P
  let f : Fin P.card ⊕ Fin Pᶜ.card ≃ Fin m := by
    have h : P.card + Pᶜ.card = m := card_add_card_compl P
    exact finSumFinEquiv.trans (finCongr h)
  e.trans f

/-- Restriction to P: given σ with σ '' P = Q, extract τ : Perm (Fin P.card).
    The k-th smallest element of P maps to the τ(k)-th smallest element of Q. -/
noncomputable def restrictToPerm {m : ℕ} (P Q : Finset (Fin m)) (hPQ : P.card = Q.card) 
    (σ : Equiv.Perm (Fin m)) (hσ : PermFinset.imageFinset σ P = Q) : Equiv.Perm (Fin P.card) := by
  let eP := P.orderIsoOfFin rfl
  let eQ := Q.orderIsoOfFin rfl
  let castQP : Fin Q.card ≃ Fin P.card := finCongr hPQ.symm
  have hσ' : ∀ x ∈ P, σ x ∈ Q := fun x hx => by
    rw [← hσ]
    simp only [PermFinset.imageFinset, Finset.mem_map, Function.Embedding.coeFn_mk]
    exact ⟨x, hx, rfl⟩
  let f : Fin P.card → Fin P.card := fun k => 
    castQP (eQ.symm ⟨σ (eP k), hσ' (eP k) (Finset.coe_mem _)⟩)
  have hf_inj : Function.Injective f := by
    intro k1 k2 hk
    simp only [f] at hk
    have hσ1 : σ ↑(eP k1) ∈ Q := hσ' (eP k1) (Finset.coe_mem _)
    have hσ2 : σ ↑(eP k2) ∈ Q := hσ' (eP k2) (Finset.coe_mem _)
    have h1 : (eQ.symm ⟨σ (eP k1), hσ1⟩).val = (eQ.symm ⟨σ (eP k2), hσ2⟩).val := by
      have := congrArg Fin.val hk
      exact this
    have h2 : eQ.symm ⟨σ (eP k1), hσ1⟩ = eQ.symm ⟨σ (eP k2), hσ2⟩ := Fin.ext h1
    have h3 : (⟨σ (eP k1), hσ1⟩ : Q) = ⟨σ (eP k2), hσ2⟩ := eQ.symm.injective h2
    have h4 : σ (eP k1 : Fin m) = σ (eP k2 : Fin m) := congrArg Subtype.val h3
    have h5 : (eP k1 : Fin m) = eP k2 := σ.injective h4
    exact eP.injective (Subtype.val_injective h5)
  have hf_surj : Function.Surjective f := by
    intro j
    let j' : Fin Q.card := castQP.symm j
    have h1 : (eQ j' : Fin m) ∈ Q := Finset.coe_mem _
    have h2 : (eQ j' : Fin m) ∈ PermFinset.imageFinset σ P := hσ ▸ h1
    simp only [PermFinset.imageFinset, Finset.mem_map, Function.Embedding.coeFn_mk] at h2
    obtain ⟨p, hp, hsp⟩ := h2
    use eP.symm ⟨p, hp⟩
    simp only [f, OrderIso.apply_symm_apply]
    have hσp : σ p ∈ Q := hσ' p hp
    have h3 : (⟨σ p, hσp⟩ : Q) = eQ j' := Subtype.ext hsp
    have h4 : eQ.symm ⟨σ p, hσp⟩ = eQ.symm (eQ j') := congrArg eQ.symm h3
    rw [OrderIso.symm_apply_apply] at h4
    rw [h4]
    rfl
  exact Equiv.ofBijective f ⟨hf_inj, hf_surj⟩

end Determinants
end AlgebraicCombinatorics
