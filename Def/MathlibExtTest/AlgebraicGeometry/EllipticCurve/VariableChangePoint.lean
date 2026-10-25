/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/AlgebraicGeometry/EllipticCurve/VariableChangePoint.lean -/

import Def.AlgebraicGeometry.EllipticCurve.VariableChangePoint.Part3
import Lemma.Scheme.EllipticCurve.VariableChangePoint
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum
import Instance.MathlibExtTest.AlgebraicGeometry.EllipticCurve.VariableChangePoint


namespace MathlibExtTest.AlgebraicGeometry.EllipticCurve.VariableChangePoint

open WeierstrassCurve

/-- The test curve `y² = x³ + x` over `ZMod 5`. -/
def curve : WeierstrassCurve (ZMod 5) :=
  ⟨0, 0, 0, 1, 0⟩

end MathlibExtTest.AlgebraicGeometry.EllipticCurve.VariableChangePoint
