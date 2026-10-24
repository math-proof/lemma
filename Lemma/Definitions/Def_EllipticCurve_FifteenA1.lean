import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Data.Rat.Defs

set_option autoImplicit false

namespace ModularCurve

namespace FifteenA1

open WeierstrassCurve Affine

def shortW : WeierstrassCurve.Affine ℚ := ⟨0, 5, 0, -152, -624⟩

@[simp] theorem shortW_a₁ : shortW.a₁ = 0 := rfl
@[simp] theorem shortW_a₂ : shortW.a₂ = 5 := rfl
@[simp] theorem shortW_a₃ : shortW.a₃ = 0 := rfl
@[simp] theorem shortW_a₄ : shortW.a₄ = -152 := rfl
@[simp] theorem shortW_a₆ : shortW.a₆ = -624 := rfl

def IsSqClass (d a : ℚ) : Prop := ∃ c : ℚ, c ≠ 0 ∧ a = d * c ^ 2

def deltaPair : shortW.Point → ℚ × ℚ
  | .zero => (1, 1)
  | .some X _ _ =>
      (if X = 12 then 400 else X - 12, if X = -4 then -144 else X + 4)

@[simp] theorem deltaPair_zero : deltaPair 0 = (1, 1) := rfl

theorem deltaPair_some {X Y : ℚ} (h : shortW.Nonsingular X Y) :
    deltaPair (.some X Y h) =
      (if X = 12 then 400 else X - 12, if X = -4 then -144 else X + 4) := rfl

def V₀ : Finset (ℚ × ℚ) := {(1, 1), (-5, -1), (-1, -1), (5, 1)}

end FifteenA1

end ModularCurve
