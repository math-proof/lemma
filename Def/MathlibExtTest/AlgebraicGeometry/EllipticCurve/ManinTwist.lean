module
public import Theorem.AlgebraicGeometry.EllipticCurve.ManinTwist.Part15
public import Theorem.Scheme.EllipticCurve.ManinTwist
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Tactic.NormNum
public import Theorem.MathlibExtTest.AlgebraicGeometry.EllipticCurve.ManinTwist


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/AlgebraicGeometry/EllipticCurve/ManinTwist.lean -/
namespace MathlibExtTest.AlgebraicGeometry.EllipticCurve.ManinTwist

open WeierstrassCurve

open MathlibExt.AlgebraicGeometry.EllipticCurve

/-- The test curve `y² = x³ + x + 1` over `ZMod 5`. -/
def curve : WeierstrassCurve (ZMod 5) :=
  ⟨0, 0, 0, 1, 1⟩

end MathlibExtTest.AlgebraicGeometry.EllipticCurve.ManinTwist
