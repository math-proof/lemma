/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/AlgebraicGeometry/EllipticCurve/PointCount.lean -/

module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
public import Def.AlgebraicGeometry.EllipticCurve.PointCount
public import Theorem.Nat.FrobeniusTrace.eq.SubAddCardF1CardPoint.of.AffineF
public import Theorem.MathlibExtTest.AlgebraicGeometry.EllipticCurve.PointCount
@[expose] public section

namespace WeierstrassCurve.Affine.PointCountTest.ZModFive

open WeierstrassCurve

instance : Fact (Nat.Prime 5) := ⟨by decide⟩

end WeierstrassCurve.Affine.PointCountTest.ZModFive
