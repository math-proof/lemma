/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/VariableChangePoint.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Def.AlgebraicGeometry.EllipticCurve.PointCount
import Lemma.Nat.FrobeniusTrace.eq.SubAddCardF1CardPoint.of.AffineF
import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
import Mathlib.Tactic.Ring
import Def.AlgebraicGeometry.EllipticCurve.VariableChangePoint
/-!
# Variable changes on affine Weierstrass points

This file transports affine solutions and rational points along an admissible variable change.
-/


namespace WeierstrassCurve.VariableChange

universe u

variable {F : Type u} [Field F]

theorem mapAffineCoordinates_mul (C C' : VariableChange F) (xy : F × F) :
    mapAffineCoordinates (C * C') xy =
      mapAffineCoordinates C' (mapAffineCoordinates C xy) := by
  ext <;> simp only [mapAffineCoordinates, mul_def, Units.val_mul]
  · ring
  · ring

@[simp]
theorem mapAffineCoordinates_inv_apply (C : VariableChange F) (xy : F × F) :
    mapAffineCoordinates C⁻¹ (mapAffineCoordinates C xy) = xy := by
  rw [← mapAffineCoordinates_mul]
  simp

@[simp]
theorem mapAffineCoordinates_apply_inv (C : VariableChange F) (xy : F × F) :
    mapAffineCoordinates C (mapAffineCoordinates C⁻¹ xy) = xy := by
  rw [← mapAffineCoordinates_mul]
  simp

end WeierstrassCurve.VariableChange
