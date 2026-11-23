/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/AlgebraicGeometry/EllipticCurve/PointCount.lean -/

module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
public import Def.AlgebraicGeometry.EllipticCurve.PointCount
public import Theorem.Nat.FrobeniusTrace.eq.SubAddCardF1CardPoint.of.AffineF
public import Instance.MathlibExtTest.AlgebraicGeometry.EllipticCurve.PointCount

@[expose] public section

namespace WeierstrassCurve.Affine.PointCountTest.ZModFive

open WeierstrassCurve

/-- The curve `y² = x³ + 1` over `ZMod 5`. -/
def curve : WeierstrassCurve.Affine (ZMod 5) :=
  ⟨0, 0, 0, 0, 1⟩

end WeierstrassCurve.Affine.PointCountTest.ZModFive
