module
public import Theorem.Scheme.EllipticCurve.HasseBound
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Tactic.NormNum
public import Instance.MathlibExtTest.AlgebraicGeometry.EllipticCurve.HasseBound


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/AlgebraicGeometry/EllipticCurve/HasseBound.lean -/
namespace MathlibExtTest.AlgebraicGeometry.EllipticCurve.HasseBound

open WeierstrassCurve

open MathlibExt.AlgebraicGeometry.EllipticCurve

def curve : WeierstrassCurve (ZMod 2) :=
  ⟨1, 0, 0, 0, 1⟩

end MathlibExtTest.AlgebraicGeometry.EllipticCurve.HasseBound
