module
public import Def.AlgebraicGeometry.EllipticCurve.VariableChangePoint.Part3
public import Theorem.Scheme.EllipticCurve.VariableChangePoint
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Tactic.NormNum
public import Def.MathlibExtTest.AlgebraicGeometry.EllipticCurve.VariableChangePoint


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/AlgebraicGeometry/EllipticCurve/VariableChangePoint.lean -/
namespace MathlibExtTest.AlgebraicGeometry.EllipticCurve.VariableChangePoint

open WeierstrassCurve

instance : curve.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff]
  norm_num [curve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, isUnit_iff_ne_zero]
  decide

end MathlibExtTest.AlgebraicGeometry.EllipticCurve.VariableChangePoint
