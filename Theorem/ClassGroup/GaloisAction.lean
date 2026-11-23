module

public import Mathlib
public import Theorem.ClassGroup.ModP

public section

set_option autoImplicit false

open scoped NumberField nonZeroDivisors
open Polynomial

section MapNonZero
variable {R : Type*} [CommRing R] [IsDomain R]
variable {R' : Type*} [CommRing R'] [IsDomain R']


@[simp] public theorem Ideal.coe_mapNonZero (g : R ≃+* R') (P : (Ideal R)⁰) :
    (Ideal.mapNonZero g P : Ideal R') = (P : Ideal R).map (g : R →+* R') := rfl

end MapNonZero

section ClassGroupFunctoriality
variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable {R' : Type*} [CommRing R'] [IsDedekindDomain R']


public theorem ClassGroup.mulEquiv_mk0_mapNonZero (g : R ≃+* R') (P : (Ideal R)⁰) :
    ClassGroup.mulEquiv g (ClassGroup.mk0 P) = ClassGroup.mk0 (Ideal.mapNonZero g P) := by
  rw [ClassGroup.mulEquiv_mk0]
  congr 1


public theorem ClassGroup.mulEquiv_refl_apply (C : ClassGroup R) :
    ClassGroup.mulEquiv (RingEquiv.refl R) C = C := by
  obtain ⟨P, rfl⟩ := ClassGroup.mk0_surjective C
  rw [ClassGroup.mulEquiv_mk0_mapNonZero]
  congr 1
  exact Subtype.ext (by
    rw [Ideal.coe_mapNonZero]
    simp [Ideal.map_id])


public theorem ClassGroup.mulEquiv_trans_apply {R'' : Type*} [CommRing R''] [IsDedekindDomain R'']
    (g : R ≃+* R') (h : R' ≃+* R'') (C : ClassGroup R) :
    ClassGroup.mulEquiv (g.trans h) C = ClassGroup.mulEquiv h (ClassGroup.mulEquiv g C) := by
  obtain ⟨P, rfl⟩ := ClassGroup.mk0_surjective C
  rw [ClassGroup.mulEquiv_mk0_mapNonZero, ClassGroup.mulEquiv_mk0_mapNonZero,
    ClassGroup.mulEquiv_mk0_mapNonZero]
  congr 1
  exact Subtype.ext (by
    rw [Ideal.coe_mapNonZero, Ideal.coe_mapNonZero, Ideal.coe_mapNonZero]
    simp [Ideal.map_map])

end ClassGroupFunctoriality

section GalRestrict


@[simp] public theorem algAutToRingAut_apply {A B : Type*} [CommSemiring A] [Semiring B] [Algebra A B]
    (e : B ≃ₐ[A] B) (x : B) : algAutToRingAut A B e x = e x := rfl

variable (A K L B : Type*) [CommRing A] [CommRing B] [Algebra A B]
  [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
  [Algebra K L] [Algebra A L] [IsScalarTower A K L] [Algebra.IsAlgebraic K L]
  [Algebra B L] [IsScalarTower A B L] [IsIntegralClosure B A L]


@[simp] public theorem galRestrictionDatum_apply (g : L ≃ₐ[K] L) (x : B) :
    galRestrictionDatum A K L B g x = galRestrict A K L B g x := rfl

end GalRestrict

namespace JacobiSumStickelberger

section ClassGroupCarrier

variable (p : ℕ) [NeZero p]

section DedekindAction

variable (R : Type*) [CommRing R] [IsDedekindDomain R]

variable {R} in

public theorem clEnd_clProj_mk0 (g : R ≃+* R) (P : (Ideal R)⁰) :
    clEnd p g (clProj p R (Additive.ofMul (ClassGroup.mk0 P))) =
      clProj p R (Additive.ofMul (ClassGroup.mk0 (Ideal.mapNonZero g P))) := by
  rw [clEnd_clProj, ClassGroup.mulEquiv_mk0_mapNonZero]

variable {R} in


public theorem clGalAction_clProj_mk0 [IsCyclotomicExtension {p} ℚ K] (d : (ZMod p)ˣ)
    (P : (Ideal (𝓞 K))⁰) :
    clGalAction p K d (clProj p (𝓞 K) (Additive.ofMul (ClassGroup.mk0 P))) =
      clProj p (𝓞 K) (Additive.ofMul (ClassGroup.mk0
        (Ideal.mapNonZero (clRingAction p K d) P))) :=
  clEnd_clProj_mk0 p (clRingAction p K d) P

end Cyclotomic

end ClassGroupCarrier

end JacobiSumStickelberger
