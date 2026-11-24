module
public import Theorem.Scheme.EllipticCurve.HasseBound
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Tactic.NormNum
public import Def.MathlibExtTest.AlgebraicGeometry.EllipticCurve.HasseBound


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/AlgebraicGeometry/EllipticCurve/HasseBound.lean -/
namespace MathlibExtTest.AlgebraicGeometry.EllipticCurve.HasseBound

open WeierstrassCurve

open MathlibExt.AlgebraicGeometry.EllipticCurve

instance : curve.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff]
  norm_num [curve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈,
    isUnit_iff_ne_zero]
  decide

end MathlibExtTest.AlgebraicGeometry.EllipticCurve.HasseBound
