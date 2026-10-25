/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/AlgebraicGeometry/EllipticCurve/VariableChangePoint.lean -/

import Def.AlgebraicGeometry.EllipticCurve.VariableChangePoint.Part3
import Lemma.Scheme.EllipticCurve.VariableChangePoint
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum
import Instance.MathlibExtTest.AlgebraicGeometry.EllipticCurve.VariableChangePoint.Part2


namespace MathlibExtTest.AlgebraicGeometry.EllipticCurve.VariableChangePoint

open WeierstrassCurve

/-- Translation by one in the affine `x` coordinate. -/
def change : VariableChange (ZMod 5) :=
  ⟨1, 1, 0, 0⟩

end MathlibExtTest.AlgebraicGeometry.EllipticCurve.VariableChangePoint
