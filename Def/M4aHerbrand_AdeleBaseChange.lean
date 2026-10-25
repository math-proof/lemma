import Def.M4aHerbrand_IdeleClassVocab
import Structure.M4aHerbrand_AdeleBaseChange

set_option autoImplicit false

open NumberField TensorProduct

namespace M4aHerbrand

noncomputable section

variable (R E : Type*) [CommRing R] [IsDedekindDomain R] [Field E] [Algebra R E]
  [IsFractionRing R E]
variable (S F : Type*) [CommRing S] [IsDedekindDomain S] [Field F] [Algebra S F]
  [IsFractionRing S F]
variable [Algebra E F]

def actOf [Algebra (AdeleRing R E) (AdeleRing S F)]
    (te : ((AdeleRing R E) ⊗[E] F) ≃ₐ[AdeleRing R E] AdeleRing S F)
    (σ : F ≃ₐ[E] F) : AdeleRing S F ≃+* AdeleRing S F :=
  (te.symm.trans ((Algebra.TensorProduct.congr AlgEquiv.refl σ).trans te)).toRingEquiv

theorem actOf_algebraMap [Algebra (AdeleRing R E) (AdeleRing S F)]
    (te : ((AdeleRing R E) ⊗[E] F) ≃ₐ[AdeleRing R E] AdeleRing S F)
    (hte : ∀ f : F, te (1 ⊗ₜ[E] f) = algebraMap F (AdeleRing S F) f)
    (σ : F ≃ₐ[E] F) (f : F) :
    actOf R E S F te σ (algebraMap F (AdeleRing S F) f) =
      algebraMap F (AdeleRing S F) (σ f) := by
  show te ((Algebra.TensorProduct.congr AlgEquiv.refl σ) (te.symm (algebraMap F _ f))) = _
  rw [← hte f, AlgEquiv.symm_apply_apply, Algebra.TensorProduct.congr_apply,
    Algebra.TensorProduct.map_tmul]
  exact hte (σ f)

theorem actOf_one [Algebra (AdeleRing R E) (AdeleRing S F)]
    (te : ((AdeleRing R E) ⊗[E] F) ≃ₐ[AdeleRing R E] AdeleRing S F) :
    actOf R E S F te 1 = 1 := by
  have h1 : (1 : F ≃ₐ[E] F) = AlgEquiv.refl := rfl
  ext x
  show te ((Algebra.TensorProduct.congr AlgEquiv.refl 1) (te.symm x)) = x
  rw [h1, Algebra.TensorProduct.congr_refl]
  exact te.apply_symm_apply x

theorem actOf_mul [Algebra (AdeleRing R E) (AdeleRing S F)]
    (te : ((AdeleRing R E) ⊗[E] F) ≃ₐ[AdeleRing R E] AdeleRing S F)
    (σ τ : F ≃ₐ[E] F) :
    actOf R E S F te (σ * τ) = actOf R E S F te σ * actOf R E S F te τ := by
  ext x
  show te ((Algebra.TensorProduct.congr AlgEquiv.refl (σ * τ)) (te.symm x)) =
    te ((Algebra.TensorProduct.congr AlgEquiv.refl σ)
      (te.symm (te ((Algebra.TensorProduct.congr AlgEquiv.refl τ) (te.symm x)))))
  rw [AlgEquiv.symm_apply_apply]
  have hmul : (σ * τ : F ≃ₐ[E] F) = τ.trans σ := rfl
  have key : Algebra.TensorProduct.congr
      (AlgEquiv.refl : AdeleRing R E ≃ₐ[AdeleRing R E] _) (σ * τ) =
    (Algebra.TensorProduct.congr AlgEquiv.refl τ).trans
      (Algebra.TensorProduct.congr AlgEquiv.refl σ) := by
    rw [hmul]
    exact Algebra.TensorProduct.congr_trans AlgEquiv.refl AlgEquiv.refl τ σ
  rw [key, AlgEquiv.trans_apply]


namespace AdeleBaseChange

variable {R E S F}

def adelicNorm (B : AdeleBaseChange R E S F) : AdeleRing S F →* AdeleRing R E :=
  letI := B.β.toAlgebra
  Algebra.norm (AdeleRing R E)

def idelicNorm (B : AdeleBaseChange R E S F) :
    (AdeleRing S F)ˣ →* (AdeleRing R E)ˣ :=
  Units.map B.adelicNorm

def actHom (B : AdeleBaseChange R E S F) :
    (F ≃ₐ[E] F) →* RingAut (AdeleRing S F) where
  toFun σ := letI := B.β.toAlgebra; actOf R E S F B.tensorEquiv σ
  map_one' := by letI := B.β.toAlgebra; exact actOf_one R E S F B.tensorEquiv
  map_mul' σ τ := by letI := B.β.toAlgebra; exact actOf_mul R E S F B.tensorEquiv σ τ

def toIdeleGaloisDescent (B : AdeleBaseChange R E S F)
    (hcont : ∀ σ : F ≃ₐ[E] F,
      letI := B.β.toAlgebra; Continuous (actOf R E S F B.tensorEquiv σ)) :
    IdeleGaloisDescent S E F where
  act := B.actHom
  compat g x := by
    letI := B.β.toAlgebra
    show (actOf R E S F B.tensorEquiv g) (algebraMap F (AdeleRing S F) x) = _
    exact actOf_algebraMap R E S F B.tensorEquiv B.tensorEquiv_one_tmul g x
  continuous_act := hcont

end AdeleBaseChange

section SelfInhabitant

variable (R E : Type*) [CommRing R] [IsDedekindDomain R] [Field E] [Algebra R E]
  [IsFractionRing R E]

def selfBaseChange : AdeleBaseChange R E R E where
  β := RingHom.id _
  β_compat e := rfl
  tensorEquiv := letI := (RingHom.id (AdeleRing R E)).toAlgebra
    Algebra.TensorProduct.rid E (AdeleRing R E) (AdeleRing R E)
  tensorEquiv_one_tmul f := by
    letI := (RingHom.id (AdeleRing R E)).toAlgebra
    show (f • (1 : AdeleRing R E)) = algebraMap E (AdeleRing R E) f
    exact (Algebra.algebraMap_eq_smul_one f).symm

end SelfInhabitant

end

end M4aHerbrand
