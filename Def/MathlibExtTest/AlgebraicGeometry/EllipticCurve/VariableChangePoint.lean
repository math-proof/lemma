/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/AlgebraicGeometry/EllipticCurve/VariableChangePoint.lean -/

module

public import Def.AlgebraicGeometry.EllipticCurve.VariableChangePoint.Part3
public import Theorem.Scheme.EllipticCurve.VariableChangePoint
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Tactic.NormNum
public import Instance.MathlibExtTest.AlgebraicGeometry.EllipticCurve.VariableChangePoint

@[expose] public section

namespace MathlibExtTest.AlgebraicGeometry.EllipticCurve.VariableChangePoint

open WeierstrassCurve

/-- The test curve `y² = x³ + x` over `ZMod 5`. -/
def curve : WeierstrassCurve (ZMod 5) :=
  ⟨0, 0, 0, 1, 0⟩

end MathlibExtTest.AlgebraicGeometry.EllipticCurve.VariableChangePoint
