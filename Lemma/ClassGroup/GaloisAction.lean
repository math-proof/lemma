import Mathlib
import Lemma.ClassGroup.ModP

set_option autoImplicit false

open scoped NumberField nonZeroDivisors
open Polynomial

section MapNonZero
variable {R : Type*} [CommRing R] [IsDomain R]
variable {R' : Type*} [CommRing R'] [IsDomain R']

def Ideal.mapNonZero (g : R ≃+* R') (P : (Ideal R)⁰) : (Ideal R')⁰ :=
  ⟨(P : Ideal R).map (g : R →+* R'), by
    have hinj : Function.Injective ((g : R →+* R') : R → R') := g.injective
    refine mem_nonZeroDivisors_iff_ne_zero.mpr fun hbot => ?_
    refine mem_nonZeroDivisors_iff_ne_zero.mp P.2 ?_
    rw [Ideal.zero_eq_bot] at hbot ⊢
    exact (Ideal.map_eq_bot_iff_of_injective hinj).mp hbot⟩

@[simp] lemma Ideal.coe_mapNonZero (g : R ≃+* R') (P : (Ideal R)⁰) :
    (Ideal.mapNonZero g P : Ideal R') = (P : Ideal R).map (g : R →+* R') := rfl

end MapNonZero

section ClassGroupFunctoriality
variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable {R' : Type*} [CommRing R'] [IsDedekindDomain R']

theorem ClassGroup.mulEquiv_mk0_mapNonZero (g : R ≃+* R') (P : (Ideal R)⁰) :
    ClassGroup.mulEquiv g (ClassGroup.mk0 P) = ClassGroup.mk0 (Ideal.mapNonZero g P) := by
  rw [ClassGroup.mulEquiv_mk0]
  congr 1

theorem ClassGroup.mulEquiv_refl_apply (C : ClassGroup R) :
    ClassGroup.mulEquiv (RingEquiv.refl R) C = C := by
  obtain ⟨P, rfl⟩ := ClassGroup.mk0_surjective C
  rw [ClassGroup.mulEquiv_mk0_mapNonZero]
  congr 1
  exact Subtype.ext (by
    rw [Ideal.coe_mapNonZero]
    simp [Ideal.map_id])

theorem ClassGroup.mulEquiv_trans_apply {R'' : Type*} [CommRing R''] [IsDedekindDomain R'']
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

def algAutToRingAut (A B : Type*) [CommSemiring A] [Semiring B] [Algebra A B] :
    (B ≃ₐ[A] B) →* (B ≃+* B) where
  toFun := AlgEquiv.toRingEquiv
  map_one' := RingEquiv.ext fun _ => rfl
  map_mul' _ _ := RingEquiv.ext fun _ => rfl

@[simp] lemma algAutToRingAut_apply {A B : Type*} [CommSemiring A] [Semiring B] [Algebra A B]
    (e : B ≃ₐ[A] B) (x : B) : algAutToRingAut A B e x = e x := rfl

variable (A K L B : Type*) [CommRing A] [CommRing B] [Algebra A B]
  [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
  [Algebra K L] [Algebra A L] [IsScalarTower A K L] [Algebra.IsAlgebraic K L]
  [Algebra B L] [IsScalarTower A B L] [IsIntegralClosure B A L]

noncomputable def galRestrictionDatum : (L ≃ₐ[K] L) →* (B ≃+* B) :=
  (algAutToRingAut A B).comp (galRestrict A K L B).toMonoidHom

@[simp] lemma galRestrictionDatum_apply (g : L ≃ₐ[K] L) (x : B) :
    galRestrictionDatum A K L B g x = galRestrict A K L B g x := rfl

end GalRestrict

namespace JacobiSumStickelberger

section ClassGroupCarrier

variable (p : ℕ) [NeZero p]

section DedekindAction

variable (R : Type*) [CommRing R] [IsDedekindDomain R]

variable {R} in
theorem clEnd_clProj_mk0 (g : R ≃+* R) (P : (Ideal R)⁰) :
    clEnd p g (clProj p R (Additive.ofMul (ClassGroup.mk0 P))) =
      clProj p R (Additive.ofMul (ClassGroup.mk0 (Ideal.mapNonZero g P))) := by
  rw [clEnd_clProj, ClassGroup.mulEquiv_mk0_mapNonZero]

variable {R} in
noncomputable def clEndHom : (R ≃+* R) →* Module.End (ZMod p) (ClGalModule p R) where
  toFun := clEnd p
  map_one' := by
    refine LinearMap.ext fun a => ?_
    obtain ⟨C, rfl⟩ := clProj_surjective p R a
    rw [Module.End.one_apply]
    show clProj p R (Additive.ofMul (ClassGroup.mulEquiv (RingEquiv.refl R) C.toMul)) =
      clProj p R C
    rw [ClassGroup.mulEquiv_refl_apply]; rfl
  map_mul' g h := by
    refine LinearMap.ext fun a => ?_
    obtain ⟨C, rfl⟩ := clProj_surjective p R a
    rw [Module.End.mul_apply]
    show clProj p R (Additive.ofMul (ClassGroup.mulEquiv (h.trans g) C.toMul)) =
      clEnd p g (clProj p R (Additive.ofMul (ClassGroup.mulEquiv h C.toMul)))
    rw [clEnd_clProj, ClassGroup.mulEquiv_trans_apply]

end DedekindAction

section Cyclotomic

variable (K : Type*) [Field K] [NumberField K]

noncomputable def cycloGalEquiv [IsCyclotomicExtension {p} ℚ K] :
    (K ≃ₐ[ℚ] K) ≃* (ZMod p)ˣ :=
  IsCyclotomicExtension.autEquivPow K
    (Polynomial.cyclotomic.irreducible_rat (Nat.pos_of_ne_zero (NeZero.ne p)))

noncomputable def clRingAction [IsCyclotomicExtension {p} ℚ K] :
    (ZMod p)ˣ →* ((𝓞 K) ≃+* (𝓞 K)) :=
  (galRestrictionDatum ℤ ℚ K (𝓞 K)).comp (cycloGalEquiv p K).symm.toMonoidHom

noncomputable def clGalAction [IsCyclotomicExtension {p} ℚ K] :
    (ZMod p)ˣ →* Module.End (ZMod p) (ClGalModule p (𝓞 K)) :=
  (clEndHom p).comp (clRingAction p K)

theorem clGalAction_clProj_mk0 [IsCyclotomicExtension {p} ℚ K] (d : (ZMod p)ˣ)
    (P : (Ideal (𝓞 K))⁰) :
    clGalAction p K d (clProj p (𝓞 K) (Additive.ofMul (ClassGroup.mk0 P))) =
      clProj p (𝓞 K) (Additive.ofMul (ClassGroup.mk0
        (Ideal.mapNonZero (clRingAction p K d) P))) :=
  clEnd_clProj_mk0 p (clRingAction p K d) P

end Cyclotomic

end ClassGroupCarrier

end JacobiSumStickelberger
