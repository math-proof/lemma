/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/AlgebraicGeometry/EllipticCurve/PointCount.lean -/

import Mathlib.Algebra.Field.ZMod
import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
import Def.AlgebraicGeometry.EllipticCurve.PointCount
import Lemma.Nat.FrobeniusTrace.eq.SubAddCardF1CardPoint.of.AffineF
import Instance.MathlibExtTest.AlgebraicGeometry.EllipticCurve.PointCount


namespace WeierstrassCurve.Affine.PointCountTest.ZModFive

open WeierstrassCurve

/-- The curve `y² = x³ + 1` over `ZMod 5`. -/
def curve : WeierstrassCurve.Affine (ZMod 5) :=
  ⟨0, 0, 0, 0, 1⟩

end WeierstrassCurve.Affine.PointCountTest.ZModFive
