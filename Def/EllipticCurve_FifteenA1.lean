import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Data.Rat.Defs

set_option autoImplicit false

namespace ModularCurve

namespace FifteenA1

open WeierstrassCurve Affine

def shortW : WeierstrassCurve.Affine ℚ := ⟨0, 5, 0, -152, -624⟩


def IsSqClass (d a : ℚ) : Prop := ∃ c : ℚ, c ≠ 0 ∧ a = d * c ^ 2

def deltaPair : shortW.Point → ℚ × ℚ
  | .zero => (1, 1)
  | .some X _ _ =>
      (if X = 12 then 400 else X - 12, if X = -4 then -144 else X + 4)


def V₀ : Finset (ℚ × ℚ) := {(1, 1), (-5, -1), (-1, -1), (5, 1)}

end FifteenA1

end ModularCurve
