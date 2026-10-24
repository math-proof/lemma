/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/AlgebraicGeometry/EllipticCurve/VariableChangePoint.lean -/

import sympy.atlas.AlgebraicGeometry.EllipticCurve.VariableChangePoint
import Lemma.Scheme.EllipticCurve.VariableChangePoint
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum

namespace MathlibExtTest.AlgebraicGeometry.EllipticCurve.VariableChangePoint

open WeierstrassCurve

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The test curve `y² = x³ + x` over `ZMod 5`. -/
private def curve : WeierstrassCurve (ZMod 5) :=
  ⟨0, 0, 0, 1, 0⟩

private instance : curve.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff]
  norm_num [curve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, isUnit_iff_ne_zero]
  decide

/-- Translation by one in the affine `x` coordinate. -/
private def change : VariableChange (ZMod 5) :=
  ⟨1, 1, 0, 0⟩

set_option maxHeartbeats 400000 in
-- Elaborating both concrete point types needs more than the default deterministic budget.
/-- A nontrivial translation preserves the number of points of a concrete curve over `ZMod 5`. -/
example : Nat.card ((change • curve).toAffine.Point) = Nat.card curve.toAffine.Point :=
  VariableChange.natCard_point_eq change curve

end MathlibExtTest.AlgebraicGeometry.EllipticCurve.VariableChangePoint
