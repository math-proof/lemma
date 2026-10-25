import Lemma.M4aHerbrand.GenuineBeta
import Instance.M4aHerbrand_FiniteTensorEquiv
import Mathlib.LinearAlgebra.TensorProduct.Prod

noncomputable section

namespace M4aHerbrand.Bridge

open NumberField IsDedekindDomain TensorProduct M4aHerbrand.ArchSemilocal

open scoped TensorProduct

section ProdSplit

variable (K P Q L : Type*) [CommRing K] [CommRing P] [CommRing Q] [CommRing L]
  [Algebra K P] [Algebra K Q] [Algebra K L]

theorem prodLeft_tmul_proj (x : P × Q) (l : L) :
    TensorProduct.prodLeft K K P Q L (x ⊗ₜ[K] l) = (x.1 ⊗ₜ[K] l, x.2 ⊗ₜ[K] l) := by
  obtain ⟨p, q⟩ := x
  rfl

def prodTensorAlgEquiv : ((P × Q) ⊗[K] L) ≃ₐ[K] ((P ⊗[K] L) × (Q ⊗[K] L)) :=
  AlgEquiv.ofLinearEquiv (TensorProduct.prodLeft K K P Q L)
    (by
      rw [Algebra.TensorProduct.one_def, prodLeft_tmul_proj]
      exact Prod.ext rfl rfl)
    (fun x y => by
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul p a =>
        induction y using TensorProduct.induction_on with
        | zero => simp
        | tmul q b =>
          simp only [Algebra.TensorProduct.tmul_mul_tmul, prodLeft_tmul_proj,
            Prod.mk_mul_mk, Prod.fst_mul, Prod.snd_mul]
        | add y₁ y₂ h₁ h₂ => simp only [mul_add, map_add, h₁, h₂]
      | add x₁ x₂ h₁ h₂ => simp only [add_mul, map_add, h₁, h₂])

@[simp] theorem prodTensorAlgEquiv_tmul (x : P × Q) (l : L) :
    prodTensorAlgEquiv K P Q L (x ⊗ₜ[K] l) = (x.1 ⊗ₜ[K] l, x.2 ⊗ₜ[K] l) :=
  prodLeft_tmul_proj K P Q L x l

end ProdSplit

section Genuine

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

omit [NumberField K] in

theorem moduleFinite_ringOfIntegers : Module.Finite (𝓞 K) (𝓞 L) :=
  Module.Finite.of_restrictScalars_finite ℤ (𝓞 K) (𝓞 L)

attribute [local instance] moduleFinite_ringOfIntegers

def genuineRingEquiv : ((AdeleRing (𝓞 K) K) ⊗[K] L) ≃+* AdeleRing (𝓞 L) L :=
  ((prodTensorAlgEquiv K (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K) L).toRingEquiv).trans
    (RingEquiv.prodCongr (genuineInfinitePlaceData (K := K) (L := L)).baseChangeRingEquiv
      (finiteBaseChangeRingEquiv (𝓞 K) K L (𝓞 L)))

theorem genuineRingEquiv_one_tmul (l : L) :
    genuineRingEquiv K L ((1 : AdeleRing (𝓞 K) K) ⊗ₜ[K] l) = algebraMap L (AdeleRing (𝓞 L) L) l :=
  Prod.ext ((genuineInfinitePlaceData (K := K) (L := L)).baseChangeRingEquiv_one_tmul l)
    (finiteBaseChangeRingEquiv_one_tmul (𝓞 K) K L (𝓞 L) l)

theorem genuineRingEquiv_tmul_one (x : AdeleRing (𝓞 K) K) :
    genuineRingEquiv K L (x ⊗ₜ[K] (1 : L)) = genuineβ K L x :=
  Prod.ext ((genuineInfinitePlaceData (K := K) (L := L)).baseChangeRingEquiv_tmul_one x.1)
    (finiteBaseChangeRingEquiv_tmul_one (𝓞 K) K L (𝓞 L) x.2)

def genuineTensorEquiv :
    letI := (genuineβ K L).toAlgebra
    ((AdeleRing (𝓞 K) K) ⊗[K] L) ≃ₐ[AdeleRing (𝓞 K) K] AdeleRing (𝓞 L) L :=
  letI := (genuineβ K L).toAlgebra
  AlgEquiv.ofRingEquiv (f := genuineRingEquiv K L) (fun x => by
    exact genuineRingEquiv_tmul_one K L x)

theorem genuineTensorEquiv_apply (z : (AdeleRing (𝓞 K) K) ⊗[K] L) :
    genuineTensorEquiv K L z = genuineRingEquiv K L z := rfl

theorem genuineTensorEquiv_one_tmul (l : L) :
    genuineTensorEquiv K L ((1 : AdeleRing (𝓞 K) K) ⊗ₜ[K] l) = algebraMap L (AdeleRing (𝓞 L) L) l :=
  genuineRingEquiv_one_tmul K L l

theorem genuineTensorEquiv_tmul_one (x : AdeleRing (𝓞 K) K) :
    genuineTensorEquiv K L (x ⊗ₜ[K] (1 : L)) = genuineβ K L x :=
  genuineRingEquiv_tmul_one K L x

end Genuine

end M4aHerbrand.Bridge

end
