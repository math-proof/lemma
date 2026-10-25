/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/VariableChangePoint.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Def.AlgebraicGeometry.EllipticCurve.PointCount
import Lemma.Nat.FrobeniusTrace.eq.SubAddCardF1CardPoint.of.AffineF
import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
import Mathlib.Tactic.Ring
import Theorem.AlgebraicGeometry.EllipticCurve.VariableChangePoint
/-!
# Variable changes on affine Weierstrass points

This file transports affine solutions and rational points along an admissible variable change.
-/


namespace WeierstrassCurve.VariableChange

universe u

variable {F : Type u} [Field F]

/-- Affine coordinates form an equivalence under an admissible Weierstrass variable change. -/
def affineCoordinatesEquiv (C : VariableChange F) : F × F ≃ F × F where
  toFun := mapAffineCoordinates C
  invFun := mapAffineCoordinates C⁻¹
  left_inv := mapAffineCoordinates_inv_apply C
  right_inv := mapAffineCoordinates_apply_inv C

end WeierstrassCurve.VariableChange
