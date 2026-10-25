import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Data.Rat.Defs
import Def.EllipticCurve_FifteenA1
set_option autoImplicit false


namespace ModularCurve

namespace FifteenA1

open WeierstrassCurve Affine


@[simp] theorem shortW_a₁ : shortW.a₁ = 0 := rfl

@[simp] theorem shortW_a₂ : shortW.a₂ = 5 := rfl

@[simp] theorem shortW_a₃ : shortW.a₃ = 0 := rfl

@[simp] theorem shortW_a₄ : shortW.a₄ = -152 := rfl

@[simp] theorem shortW_a₆ : shortW.a₆ = -624 := rfl


@[simp] theorem deltaPair_zero : deltaPair 0 = (1, 1) := rfl

theorem deltaPair_some {X Y : ℚ} (h : shortW.Nonsingular X Y) :
    deltaPair (.some X Y h) =
      (if X = 12 then 400 else X - 12, if X = -4 then -144 else X + 4) := rfl


end FifteenA1
end ModularCurve
