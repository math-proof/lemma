module
public import Def.LanglandsTunnell_LiftTraceSeed
public import Def.Matrix_Lift48
set_option autoImplicit false


public section

noncomputable section

namespace LanglandsTunnell.P2

open NumberField IsDedekindDomain FLT.ExplicitLift Matrix.Lift48

def C8 : List Mat := (List.range 8).map (pw Tlift)

section C8Sub

variable {L : Type*} [Field L] [NumberField L] (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))

def c8H : Subgroup (L ≃ₐ[ℚ] L) where
  carrier := {γ | ∃ M ∈ C8,
    M.map red = ((e γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3))}
  one_mem' := ⟨1, one_mem_C8, by rw [map_one, Units.val_one, Matrix.map_one _ (map_zero red) (map_one red)]⟩
  mul_mem' := by
    rintro a b ⟨M, hM, hMa⟩ ⟨N, hN, hNb⟩
    exact ⟨M * N, C8_mul_closed M hM N hN, by rw [Matrix.map_mul, hMa, hNb, map_mul, Units.val_mul]⟩
  inv_mem' := by
    rintro a ⟨M, hM, hMa⟩
    refine ⟨pw M 7, C8_pw_seven_mem M hM, ?_⟩
    rw [map_inv]
    refine (Units.inv_eq_of_mul_eq_one_right ?_).symm
    rw [← hMa, ← Matrix.map_mul, C8_mul_pw_seven M hM, Matrix.map_one _ (map_zero red) (map_one red)]

def tbarGL : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (Tlift.map red) (by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, Tlift_det_eq_neg_one, map_neg, map_one]; decide)

def gammaT : L ≃ₐ[ℚ] L := e.symm tbarGL

def gammaTMem : ↥(c8H e) := ⟨gammaT e, gammaT_mem e⟩

end C8Sub

section ChiGal

variable {L : Type*} [Field L] [NumberField L] (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
  {ζ : ℂ} (hζ : ζ ^ 4 = -1)

include hζ in
def zetaUnit : ℂˣ := Units.mk0 ζ (zeta_ne_zero hζ)

def chiGal : ↥(c8H e) →* ℂˣ :=
  monoidHomOfForallMemZpowers (mem_zpowers_gammaTMem e) (orderOf_zetaUnit_dvd e hζ)

end ChiGal

section Artin

variable {L : Type*} [Field L] [NumberField L] [IsGalois ℚ L]
  (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) {ζ : ℂ} (hζ : ζ ^ 4 = -1)

open Classical in

def artinValue (v : HeightOneSpectrum (𝓞 (FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L))) : ℂˣ :=
  chiGal e hζ ⟨seedFrob (c8H e) v, seedFrob_mem (c8H e) v⟩

end Artin

end LanglandsTunnell.P2

end
