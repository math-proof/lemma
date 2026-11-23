/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/VariableChangePoint.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Def.AlgebraicGeometry.EllipticCurve.PointCount
public import Theorem.Nat.FrobeniusTrace.eq.SubAddCardF1CardPoint.of.AffineF
public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
public import Mathlib.Tactic.Ring
public import Theorem.AlgebraicGeometry.EllipticCurve.VariableChangePoint

@[expose] public section

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
