import Mathlib
import Class.Mathlib_IsModuleTopology
import Lemma.Algebra.IsBiscalar.commutes


section

section linear

variable {A B : Type*} (S' : Type*) {S : Type*}
    [Semiring S'] [Semiring S] [AddCommMonoid A] [AddCommMonoid B] [Module S A]
    [Module S B] [Module S' A] [Module S' B]

def LinearMap.changeScalars (f : A →ₗ[S] B) [IsBiscalar S S' f] :
    A →ₗ[S'] B where
  __ := f
  map_smul' s x := by simpa using IsBiscalar.map_smul₂ S s x

def LinearEquiv.changeScalars (f : A ≃ₗ[S] B) [IsBiscalar S S' f] :
    A ≃ₗ[S'] B where
  __ := LinearMap.changeScalars S' f.toLinearMap
  invFun := f.invFun
  left_inv (a : A) := by simp [LinearMap.changeScalars]
  right_inv (b : B) := by simp [LinearMap.changeScalars]

end linear

section algebra

@[simps! apply symm_apply]
def AlgEquiv.extendScalars {A C D : Type*} (B : Type*) [CommSemiring A] [CommSemiring C]
    [CommSemiring D] [Algebra A C] [Algebra A D] [CommSemiring B] [Algebra A B] [Algebra B C]
    [IsScalarTower A B C] (f : C ≃ₐ[A] D) :
    letI := (f.toAlgHom.restrictDomain B).toRingHom.toAlgebra
    C ≃ₐ[B] D where
  __ := (f.toAlgHom.restrictDomain B).toRingHom.toAlgebra
  __ := f
  invFun := f.symm
  commutes' := fun _ => rfl

variable {A B : Type*} (S' : Type*) {S : Type*}
    [CommSemiring A] [CommSemiring B] [CommSemiring S'] [CommSemiring S] [Algebra S A]
    [Algebra S B] [Algebra S' A] [Algebra S' B]

def AlgHom.changeScalars (f : A →ₐ[S] B) [IsBiscalar S S' f] :
    A →ₐ[S'] B where
  __ := f
  commutes' (r : _) := by simp [IsBiscalar.commutes]

def AlgEquiv.changeScalars (f : A ≃ₐ[S] B) [IsBiscalar S S' f.toAlgHom] :
    A ≃ₐ[S'] B where
  __ := AlgHom.changeScalars S' f.toAlgHom
  invFun := f.invFun
  left_inv (a : A) := by simp [AlgHom.changeScalars]
  right_inv (b : B) := by simp [AlgHom.changeScalars]
  commutes' := fun _ => by simp

end algebra

section diamond_checks

example {S A B : Type*} [CommSemiring S] [CommSemiring A] [CommSemiring B]
    [Algebra S A] [Algebra S B] (f : A →ₐ[S] B) [IsBiscalar S S f] :
    AlgHom.changeScalars S f = f := rfl

example {A B : Type*} (S' : Type*) {S : Type*}
    [CommSemiring A] [CommSemiring B] [CommSemiring S'] [CommSemiring S] [Algebra S A]
    [Algebra S B] [Algebra S' A] [Algebra S' B] (f : A →ₐ[S] B) [IsBiscalar S S' f]
    [IsBiscalar S' S (AlgHom.changeScalars S' f)] :
    (AlgHom.changeScalars S' f).changeScalars S = f := rfl

end diamond_checks

end

namespace IsModuleTopology

@[simps!]
def continuousLinearEquiv {A B R : Type*} [TopologicalSpace A]
    [TopologicalSpace B] [TopologicalSpace R] [Semiring R] [AddCommMonoid A] [AddCommMonoid B]
    [Module R A] [Module R B] [IsModuleTopology R A] [IsModuleTopology R B]
    (e : A ≃ₗ[R] B) :
    A ≃L[R] B where
  toFun := e
  __ := e
  continuous_toFun :=
    letI := IsModuleTopology.toContinuousAdd
    IsModuleTopology.continuous_of_linearMap e.toLinearMap
  continuous_invFun :=
    letI := IsModuleTopology.toContinuousAdd
    IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap

def continuousLinearEquivOfIsBiscalar {A B : Type*} (S' : Type*) {S : Type*}
    [Semiring S'] [Semiring S] [AddCommMonoid A] [AddCommMonoid B] [Module S A]
    [Module S B] [Module S' A] [Module S' B] [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalSpace S'] [IsModuleTopology S' A] [IsModuleTopology S' B] (e : A ≃ₗ[S] B)
    [IsBiscalar S S' e] :
    A ≃L[S] B where
  toLinearEquiv := e
  continuous_toFun := by
    change Continuous (e.changeScalars S')
    letI := IsModuleTopology.toContinuousAdd
    exact IsModuleTopology.continuous_of_linearMap _
  continuous_invFun := by
    change Continuous (e.changeScalars S').symm
    letI := IsModuleTopology.toContinuousAdd
    exact IsModuleTopology.continuous_of_linearMap _

def continuousAlgEquivOfIsBiscalar {A B : Type*} (S' : Type*) {S : Type*}
    [CommSemiring A] [CommSemiring B] [CommSemiring S'] [CommSemiring S]
    [Algebra S A] [Algebra S B] [Algebra S' A] [Algebra S' B] [TopologicalSpace A]
    [TopologicalSpace B] [TopologicalSpace S'] [IsModuleTopology S' A]
    [IsModuleTopology S' B] (e : A ≃ₐ[S] B) [IsBiscalar S S' e.toAlgHom] :
    A ≃A[S] B where
  toAlgEquiv := e
  continuous_toFun := by
    change Continuous (e.changeScalars S').toLinearEquiv
    letI := IsModuleTopology.toContinuousAdd
    exact IsModuleTopology.continuous_of_linearMap _
  continuous_invFun := by
    change Continuous (e.changeScalars S').toLinearEquiv.symm
    letI := IsModuleTopology.toContinuousAdd
    exact IsModuleTopology.continuous_of_linearMap _

def continuousAlgEquivOfAlgEquiv {A B R : Type*} [TopologicalSpace A]
    [TopologicalSpace B] [TopologicalSpace R] [CommSemiring R] [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B] [IsModuleTopology R A] [IsModuleTopology R B]
    (e : A ≃ₐ[R] B) :
    A ≃A[R] B where
  __ := e
  continuous_toFun :=
    letI := IsModuleTopology.toContinuousAdd
    IsModuleTopology.continuous_of_linearMap e.toLinearMap
  continuous_invFun :=
    letI := IsModuleTopology.toContinuousAdd
    IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap

section ModuleFinite

@[simps!]
noncomputable
def Module.Basis.equivFun_homeo (K R : Type*) [Field K] [Ring R] [Module K R]
    [Module.Finite K R] [TopologicalSpace K] [TopologicalSpace R] [IsTopologicalRing R]
    [IsTopologicalRing K] [IsModuleTopology K R] : R ≃L[K] (Fin (Module.finrank K R) → K) where
  __ := Module.Basis.equivFun (Module.finBasisOfFinrankEq K R (rfl))
  continuous_toFun :=
    IsModuleTopology.continuous_of_linearMap
      (Module.Basis.equivFun (Module.finBasisOfFinrankEq K R (rfl))).toLinearMap
  continuous_invFun :=
    IsModuleTopology.continuous_of_linearMap
      (Module.Basis.equivFun (Module.finBasisOfFinrankEq K R (rfl))).symm.toLinearMap

end ModuleFinite

end IsModuleTopology
