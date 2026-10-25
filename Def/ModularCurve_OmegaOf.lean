import Lemma.ModularCurve.QAdicPlace
import Instance.ModularCurve_ArithmeticGalois
import Def.ModularCurve_QExpansionDiff
import Theorems.Thm_ModularCurve_theta_coeff
import Theorems.Thm_ModularCurve_coeffMap_injective
import Mathlib.NumberTheory.ModularForms.QExpansion

set_option autoImplicit false

noncomputable section

open UpperHalfPlane

namespace ModularCurve

variable (N : ℕ) [NeZero N]

open scoped Classical in

def omegaOf (f : ℍ → ℂ) (σ : AlgebraicClosure ℚ →+* ℂ) :
    Ω[modularFunctionFieldBar N⁄AlgebraicClosure ℚ] :=
  if h : ∃ x : modularFunctionFieldBar N,
      coeffMap σ ((x : LaurentSeries (AlgebraicClosure ℚ)) *
          thetaL (AlgebraicClosure ℚ) (coeffEmb (AlgebraicClosure ℚ) jq)) =
        ((qExpansion 1 f : PowerSeries ℂ) : LaurentSeries ℂ)
  then
    h.choose •
      KaehlerDifferential.D (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
        (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
          modularFunctionFieldBar N)
  else 0

end ModularCurve

end
