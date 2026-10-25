import Structure.ModularCurve_ShimuraSubgroup
import Lemma.ModularCurve.ShimuraGenerator
import Lemma.AlgebraicCurve.Correspondence

set_option autoImplicit false

noncomputable section

namespace AlgebraicCurve

namespace Pic0

open Divisor

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
variable [HasPrincipalDivisors K F']
variable (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
variable (hFI : FundamentalIdentityAlong K φ hφ)


end Pic0

end AlgebraicCurve

namespace ModularCurve

open AlgebraicCurve IntermediateField

variable (p : ℕ)

abbrev shimuraFunctionFieldBar :
    IntermediateField (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) :=
  laurentBaseChange (AlgebraicClosure ℚ) (shimuraFunctionField p)

theorem modularFunctionFieldBar_le_shimuraFunctionFieldBar :
    modularFunctionFieldBar p ≤ shimuraFunctionFieldBar p := by
  show laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull p)
    ≤ laurentBaseChange (AlgebraicClosure ℚ) (shimuraFunctionField p)
  unfold laurentBaseChange
  exact IntermediateField.adjoin.mono _ _ _
    (Set.image_mono (modularFunctionFieldFull_le_shimuraFunctionField p))

def shimuraInclusion :
    (modularFunctionFieldBar p) →ₐ[AlgebraicClosure ℚ] (shimuraFunctionFieldBar p) :=
  IntermediateField.inclusion (modularFunctionFieldBar_le_shimuraFunctionFieldBar p)

structure ShimuraCoveringInputs : Prop where

  hint : (shimuraInclusion p).toRingHom.IsIntegral

  hpd : HasPrincipalDivisors (AlgebraicClosure ℚ) (shimuraFunctionFieldBar p)

  hFI : haveI := hpd; FundamentalIdentityAlong (AlgebraicClosure ℚ) (shimuraInclusion p) hint

variable {p} in


variable {p} in


end ModularCurve

end
