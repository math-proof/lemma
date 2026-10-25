/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/AlgebraicGeometry/EllipticCurve/VariableChangePoint.lean -/

import Def.AlgebraicGeometry.EllipticCurve.VariableChangePoint.Part3
import Lemma.Scheme.EllipticCurve.VariableChangePoint
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum
import Def.MathlibExtTest.AlgebraicGeometry.EllipticCurve.VariableChangePoint.Part2


namespace MathlibExtTest.AlgebraicGeometry.EllipticCurve.VariableChangePoint

open WeierstrassCurve

set_option maxHeartbeats 400000 in
-- Elaborating both concrete point types needs more than the default deterministic budget.
/-- A nontrivial translation preserves the number of points of a concrete curve over `ZMod 5`. -/
example : Nat.card ((change • curve).toAffine.Point) = Nat.card curve.toAffine.Point :=
  VariableChange.natCard_point_eq change curve

end MathlibExtTest.AlgebraicGeometry.EllipticCurve.VariableChangePoint
