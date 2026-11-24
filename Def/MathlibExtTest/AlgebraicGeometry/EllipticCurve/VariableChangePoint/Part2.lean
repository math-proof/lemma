module
public import Def.AlgebraicGeometry.EllipticCurve.VariableChangePoint.Part3
public import Theorem.Scheme.EllipticCurve.VariableChangePoint
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Tactic.NormNum
public import Instance.MathlibExtTest.AlgebraicGeometry.EllipticCurve.VariableChangePoint.Part2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/AlgebraicGeometry/EllipticCurve/VariableChangePoint.lean -/
namespace MathlibExtTest.AlgebraicGeometry.EllipticCurve.VariableChangePoint

open WeierstrassCurve

/-- Translation by one in the affine `x` coordinate. -/
def change : VariableChange (ZMod 5) :=
  ⟨1, 1, 0, 0⟩

end MathlibExtTest.AlgebraicGeometry.EllipticCurve.VariableChangePoint
