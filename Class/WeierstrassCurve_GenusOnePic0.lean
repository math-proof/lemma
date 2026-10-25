import Mathlib
import Class.AlgebraicCurve_DivisorClassGroup

set_option autoImplicit false

noncomputable section

open AlgebraicCurve

namespace WeierstrassCurve.Affine

universe u

variable {F : Type u} [Field F] [DecidableEq F]

variable (W : Affine F) in

class GenusOnePlaceGate : Type u where
  pointEquivPlace : W.Point ≃ AlgebraicCurve.Place F W.FunctionField
  deg_eq_one : ∀ v : AlgebraicCurve.Place F W.FunctionField, v.deg = 1

variable {W : Affine F} [GenusOnePlaceGate W]

noncomputable def divisorSum : AlgebraicCurve.Divisor F W.FunctionField →+ W.Point :=
  Finsupp.liftAddHom fun v =>
    zmultiplesHom W.Point ((GenusOnePlaceGate.pointEquivPlace (W := W)).symm v)

variable (W) in

class AbelTheorem : Prop where
  isPrincipal_iff_divisorSum_eq_zero :
    ∀ D : AlgebraicCurve.Divisor F W.FunctionField, Divisor.degree D = 0 →
      (Divisor.IsPrincipal D ↔ divisorSum D = 0)

end WeierstrassCurve.Affine
