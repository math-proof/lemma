module
public import Def.AlgebraicGeometry.EllipticCurve.VariableChangePoint.Part3
public import Theorem.Scheme.EllipticCurve.VariableChangePoint
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Tactic.NormNum
public import Def.MathlibExtTest.AlgebraicGeometry.EllipticCurve.VariableChangePoint.Part2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/AlgebraicGeometry/EllipticCurve/VariableChangePoint.lean -/
namespace MathlibExtTest.AlgebraicGeometry.EllipticCurve.VariableChangePoint

open WeierstrassCurve

set_option maxHeartbeats 400000 in
-- Elaborating both concrete point types needs more than the default deterministic budget.
/-- A nontrivial translation preserves the number of points of a concrete curve over `ZMod 5`. -/
example : Nat.card ((change • curve).toAffine.Point) = Nat.card curve.toAffine.Point :=
  VariableChange.natCard_point_eq change curve

end MathlibExtTest.AlgebraicGeometry.EllipticCurve.VariableChangePoint
