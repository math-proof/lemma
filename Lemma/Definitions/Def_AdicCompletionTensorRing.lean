import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Lemma.Definitions.Def_AdicCompletionRingFunctoriality
import Lemma.Definitions.Def_AdicCompletionRestrictScalars

universe u₁ u₂

open scoped TensorProduct

namespace AdicCompletion

variable {A : Type u₁} [CommRing A] (B : Type u₂) [CommRing B] [Algebra A B] (𝔭 : Ideal A)

noncomputable def completionBaseChangeHom :
    AdicCompletion 𝔭 A →ₐ[A] AdicCompletion (𝔭.map (algebraMap A B)) B :=
  mapₐ 𝔭 (𝔭.map (algebraMap A B)) (Algebra.ofId A B)
    (le_of_eq (rfl : 𝔭.map (Algebra.ofId A B) = 𝔭.map (algebraMap A B)))

@[simp]
theorem completionBaseChangeHom_of (x : A) :
    completionBaseChangeHom B 𝔭 (of 𝔭 A x) =
      of (𝔭.map (algebraMap A B)) B (algebraMap A B x) := by
  simp [completionBaseChangeHom, Algebra.ofId_apply]

noncomputable def completionOfAlgHom :
    B →ₐ[A] AdicCompletion (𝔭.map (algebraMap A B)) B :=
  IsScalarTower.toAlgHom A B _

@[simp]
theorem completionOfAlgHom_apply (b : B) :
    completionOfAlgHom B 𝔭 b = of (𝔭.map (algebraMap A B)) B b := rfl

noncomputable def tensorRingHom :
    (AdicCompletion 𝔭 A) ⊗[A] B →ₐ[A] AdicCompletion (𝔭.map (algebraMap A B)) B :=
  Algebra.TensorProduct.productMap (completionBaseChangeHom B 𝔭) (completionOfAlgHom B 𝔭)

@[simp]
theorem tensorRingHom_tmul (x : AdicCompletion 𝔭 A) (b : B) :
    tensorRingHom B 𝔭 (x ⊗ₜ[A] b) =
      completionBaseChangeHom B 𝔭 x * of (𝔭.map (algebraMap A B)) B b := by
  simp [tensorRingHom]

theorem tensorRingHom_tmul_eq_symm_smul (x : AdicCompletion 𝔭 A) (b : B) :
    tensorRingHom B 𝔭 (x ⊗ₜ[A] b) =
      (restrictScalarsEquiv B 𝔭).symm (x • of 𝔭 B b) := by
  induction x using AdicCompletion.induction_on with
  | _ a =>
    refine ext_evalₐ fun n => ?_

    rw [tensorRingHom_tmul, map_mul]
    simp only [completionBaseChangeHom, evalₐ_mapₐ, evalₐ_mk, levelMapₐ_mk,
      Algebra.ofId_apply, evalₐ_of]

    have hval : (mk 𝔭 A a • of 𝔭 B b).val n =
        Submodule.Quotient.mk (a.val n • b) := by
      rw [smul_eval]
      show Ideal.Quotient.mk (𝔭 ^ n • ⊤ : Ideal A) (a.val n) •
          Submodule.Quotient.mk (p := (𝔭 ^ n • ⊤ : Submodule A B)) b = _
      rw [mk_smul_mk, ← Submodule.Quotient.mk_smul]
    have hsymmval : ((restrictScalarsEquiv B 𝔭).symm (mk 𝔭 A a • of 𝔭 B b)).val n =
        Submodule.Quotient.mk (p :=
          ((𝔭.map (algebraMap A B)) ^ n • ⊤ : Submodule B B)) (a.val n • b) := by
      show (levelRestrictScalarsEquiv B 𝔭 n).symm ((mk 𝔭 A a • of 𝔭 B b).val n) = _
      rw [hval, LinearEquiv.symm_apply_eq, levelRestrictScalarsEquiv_mk]
    rw [← factor_eval_eq_evalₐ _ _ (le_of_eq (by ext x; simp)),
      show eval (𝔭.map (algebraMap A B)) B n
        ((restrictScalarsEquiv B 𝔭).symm (mk 𝔭 A a • of 𝔭 B b)) =
        ((restrictScalarsEquiv B 𝔭).symm (mk 𝔭 A a • of 𝔭 B b)).val n from rfl,
      hsymmval,
      show Submodule.Quotient.mk (p :=
          ((𝔭.map (algebraMap A B)) ^ n • ⊤ : Submodule B B)) (a.val n • b) =
        Submodule.mkQ ((𝔭.map (algebraMap A B)) ^ n • ⊤ : Submodule B B) (a.val n • b)
        from rfl,
      Submodule.factor_mk, ← map_mul, Algebra.smul_def]
    rfl

theorem restrictScalarsEquiv_tensorRingHom (z : AdicCompletion 𝔭 A ⊗[A] B) :
    restrictScalarsEquiv B 𝔭 (tensorRingHom B 𝔭 z) = ofTensorProduct 𝔭 B z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x b =>
    rw [tensorRingHom_tmul_eq_symm_smul, LinearEquiv.apply_symm_apply,
      ofTensorProduct_tmul]
  | add u v hu hv => simp [map_add, hu, hv]

end AdicCompletion

section SameUniverse

namespace AdicCompletion

variable {A : Type u₁} [CommRing A] (B : Type u₁) [CommRing B] [Algebra A B] (𝔭 : Ideal A)

theorem tensorRingHom_bijective [IsNoetherianRing A] [Module.Finite A B] :
    Function.Bijective (tensorRingHom B 𝔭) := by
  have hfun : ⇑(tensorRingHom B 𝔭) =
      ⇑(restrictScalarsEquiv B 𝔭).symm ∘ ⇑(ofTensorProduct 𝔭 B) := by
    funext z
    rw [Function.comp_apply, ← restrictScalarsEquiv_tensorRingHom B 𝔭 z,
      LinearEquiv.symm_apply_apply]
  rw [hfun]
  exact (restrictScalarsEquiv B 𝔭).symm.bijective.comp
    (ofTensorProduct_bijective_of_finite_of_isNoetherian 𝔭 B)

noncomputable def tensorRingEquiv [IsNoetherianRing A] [Module.Finite A B] :
    (AdicCompletion 𝔭 A ⊗[A] B) ≃ₐ[A] AdicCompletion (𝔭.map (algebraMap A B)) B :=
  AlgEquiv.ofBijective (tensorRingHom B 𝔭) (tensorRingHom_bijective B 𝔭)

@[simp]
theorem tensorRingEquiv_tmul [IsNoetherianRing A] [Module.Finite A B]
    (x : AdicCompletion 𝔭 A) (b : B) :
    tensorRingEquiv B 𝔭 (x ⊗ₜ[A] b) =
      completionBaseChangeHom B 𝔭 x * of (𝔭.map (algebraMap A B)) B b :=
  tensorRingHom_tmul B 𝔭 x b

end AdicCompletion

end SameUniverse

set_option pp.universes true in
#check @AdicCompletion.tensorRingEquiv
#print axioms AdicCompletion.completionBaseChangeHom
#print axioms AdicCompletion.completionBaseChangeHom_of
#print axioms AdicCompletion.tensorRingHom
#print axioms AdicCompletion.tensorRingHom_tmul
#print axioms AdicCompletion.tensorRingHom_tmul_eq_symm_smul
#print axioms AdicCompletion.restrictScalarsEquiv_tensorRingHom
#print axioms AdicCompletion.tensorRingHom_bijective
#print axioms AdicCompletion.tensorRingEquiv
#print axioms AdicCompletion.tensorRingEquiv_tmul
