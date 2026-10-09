import Mathlib
import sympy.Basic

open scoped TensorProduct

/--
[Algebra_TensorProduct_nonempty_algEquiv_tensor_quotient_of_isScalarTower](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_TensorProduct_nonempty_algEquiv_tensor_quotient_of_isScalarTower.lean)
-/

private lemma  Algebra.TensorProduct.nonempty_algEquiv_tensor_quotient_of_isScalarTower
    (Λ : Type*) [CommRing Λ] (I : Ideal Λ) (k : Type*) [CommRing k] [Algebra Λ k]
    [Algebra (Λ ⧸ I) k] [IsScalarTower Λ (Λ ⧸ I) k]
    (A : Type*) [CommRing A] [Algebra Λ A] :
    Nonempty (k ⊗[Λ] A ≃ₐ[k] k ⊗[Λ ⧸ I] (A ⧸ I.map (algebraMap Λ A))) := by
  let e2 : (Λ ⧸ I) ⊗[Λ] A ≃ₐ[Λ] A ⧸ I.map (algebraMap Λ A) :=
    (Algebra.TensorProduct.comm Λ (Λ ⧸ I) A).trans
      ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot A I).symm.restrictScalars Λ)
  let e2' : (Λ ⧸ I) ⊗[Λ] A ≃ₐ[Λ ⧸ I] A ⧸ I.map (algebraMap Λ A) :=
    AlgEquiv.ofRingEquiv (f := e2.toRingEquiv) (fun x => by
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [← Ideal.Quotient.algebraMap_eq, ← IsScalarTower.algebraMap_apply,
        ← IsScalarTower.algebraMap_apply]
      exact e2.commutes a)
  exact ⟨(Algebra.TensorProduct.cancelBaseChange Λ (Λ ⧸ I) k k A).symm.trans
    (Algebra.TensorProduct.congr AlgEquiv.refl e2')⟩
@[path]
private lemma main
  [CommRing Λ] [CommRing k] [Algebra Λ k] [CommRing A] [Algebra Λ A]
  {I : Ideal Λ} [Algebra (Λ ⧸ I) k] [IsScalarTower Λ (Λ ⧸ I) k] :
-- imply
  Nonempty (k ⊗[Λ] A ≃ₐ[k] k ⊗[Λ ⧸ I] (A ⧸ I.map (algebraMap Λ A))) :=
-- proof
  Algebra.TensorProduct.nonempty_algEquiv_tensor_quotient_of_isScalarTower Λ I k A


-- created on 2026-10-05
