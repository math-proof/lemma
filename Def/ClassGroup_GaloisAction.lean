module

public import Mathlib
public import Def.ClassGroup_ModP

@[expose] public section

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

end MapNonZero


section GalRestrict

def algAutToRingAut (A B : Type*) [CommSemiring A] [Semiring B] [Algebra A B] :
    (B ≃ₐ[A] B) →* (B ≃+* B) where
  toFun := AlgEquiv.toRingEquiv
  map_one' := RingEquiv.ext fun _ => rfl
  map_mul' _ _ := RingEquiv.ext fun _ => rfl

variable (A K L B : Type*) [CommRing A] [CommRing B] [Algebra A B]
  [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
  [Algebra K L] [Algebra A L] [IsScalarTower A K L] [Algebra.IsAlgebraic K L]
  [Algebra B L] [IsScalarTower A B L] [IsIntegralClosure B A L]

noncomputable def galRestrictionDatum : (L ≃ₐ[K] L) →* (B ≃+* B) :=
  (algAutToRingAut A B).comp (galRestrict A K L B).toMonoidHom

end GalRestrict

namespace JacobiSumStickelberger

section ClassGroupCarrier

variable (p : ℕ) [NeZero p]

section DedekindAction

variable (R : Type*) [CommRing R] [IsDedekindDomain R]

variable {R} in
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

end Cyclotomic

end ClassGroupCarrier

end JacobiSumStickelberger

end
