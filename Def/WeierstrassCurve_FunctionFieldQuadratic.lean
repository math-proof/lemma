import Mathlib
import Instance.WeierstrassCurve_FunctionFieldQuadratic

set_option autoImplicit false

noncomputable section

open Polynomial

open scoped Polynomial.Bivariate

namespace WeierstrassCurve.Affine

open CoordinateRing

variable {F : Type*} [Field F] {W : Affine F}

def polyToFunctionField (W : Affine F) : F[X] →+* W.FunctionField :=
  (algebraMap W.CoordinateRing W.FunctionField).comp (algebraMap F[X] W.CoordinateRing)

variable (W) in

def ratFuncToFunctionField : RatFunc F →+* W.FunctionField :=
  IsFractionRing.lift algebraMap_polynomial_injective

variable (W) in

def yCoord : W.FunctionField :=
  algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W Y)

variable (W) in

def weierstrassQuadratic : Polynomial (RatFunc F) :=
  X ^ 2 + (C (algebraMap F[X] (RatFunc F) (C W.a₁ * X + C W.a₃)) * X
    - C (algebraMap F[X] (RatFunc F) (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆)))

end WeierstrassCurve.Affine

end
