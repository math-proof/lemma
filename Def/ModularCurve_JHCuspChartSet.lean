import Mathlib
import Instance.ModularCurve_JHNeronObjectAtP
import Def.ModularCurve_JHPlaceSpecialization

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open scoped MatrixGroups

namespace ModularCurve.JHPlaceSpecialization

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}

def integralOverPoleChart (A : ValuationSubring (AlgebraicClosure ℚ))
    (x' : ↥(xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM))) :
    Set ↥(xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM)) :=
  letI : Algebra ↥A ↥(xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM)) :=
    ((algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM))).comp A.subtype).toAlgebra
  {s | IsIntegral ↥(Algebra.adjoin ↥A ({x'⁻¹} : Set ↥(xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM)))) s}

def cuspChartSetInf (A : ValuationSubring (AlgebraicClosure ℚ))
    (α : ↥(xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (x' : ↥(xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM))) (t : ↥(xHFunctionFieldBar M H)) :
    Set ↥(xHFunctionFieldBar M H) :=
  (α '' integralOverPoleChart (p := p) A x') ∪
    Set.range (fun a : ↥A => t - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (a : AlgebraicClosure ℚ))

end ModularCurve.JHPlaceSpecialization
