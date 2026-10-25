import Mathlib
import Lemma.Definitions.Def_AlgebraicCurve_Correspondence
import Def.AlgebraicCurve_DifferentialPushPull
set_option autoImplicit false


noncomputable section

open KaehlerDifferential TensorProduct

namespace AlgebraicCurve

namespace Differential

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']


theorem pullbackAlong_D (φ : F →ₐ[K] F') (f : F) :
    pullbackAlong φ (D K F f) = D K F' (φ f) := by
  let := algebraAlong φ
  have := isScalarTower_along φ
  exact KaehlerDifferential.map_D K K F F' f

theorem pullbackAlong_smul (φ : F →ₐ[K] F') (f : F) (ω : Ω[F⁄K]) :
    pullbackAlong φ (f • ω) = φ f • pullbackAlong φ ω := by
  let := algebraAlong φ
  have := isScalarTower_along φ
  show KaehlerDifferential.map K K F F' (f • ω) = _
  rw [LinearMap.map_smul_of_tower]
  rfl

open Classical in


theorem traceAlong_smul_pullbackAlong (φ : F →ₐ[K] F') (h : SeparableAlong K φ) (u : F')
    (ω : Ω[F⁄K]) :
    traceAlong φ (u • pullbackAlong φ ω) =
      (let := algebraAlong φ; Algebra.trace F F' u) • ω := by
  let := algebraAlong φ
  have := isScalarTower_along φ
  have : Algebra.IsSeparable F F' := h
  have : Algebra.FormallyEtale F F' := Algebra.FormallyEtale.of_isSeparable F F'
  rw [traceAlong, dite_eq_left h]
  simp only [LinearMap.coe_restrictScalars, LinearMap.coe_comp, LinearEquiv.coe_coe,
    Function.comp_apply]
  have hsymm : (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K F F').symm
      (u • pullbackAlong φ ω) = u ⊗ₜ ω := by
    rw [LinearEquiv.symm_apply_eq, KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply,
      KaehlerDifferential.mapBaseChange_tmul]
    rfl
  rw [hsymm, LinearMap.rTensor_tmul, TensorProduct.lid_tmul]

theorem traceAlong_of_not (φ : F →ₐ[K] F') (h : ¬ SeparableAlong K φ) : traceAlong φ = 0 := by
  rw [traceAlong, dite_eq_right h]


theorem correspondence_apply (φ ψ : F →ₐ[K] F') (ω : Ω[F⁄K]) :
    correspondence φ ψ ω = traceAlong φ (pullbackAlong ψ ω) := rfl

end Differential
end AlgebraicCurve
end
