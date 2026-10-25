/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/AlgebraicGeometry/EllipticCurve/PointCount.lean -/

import Mathlib.Algebra.Field.ZMod
import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
import Def.AlgebraicGeometry.EllipticCurve.PointCount
import Lemma.Nat.FrobeniusTrace.eq.SubAddCardF1CardPoint.of.AffineF
import Instance.MathlibExtTest.AlgebraicGeometry.EllipticCurve.PointCount.Part2


namespace WeierstrassCurve.Affine.PointCountTest.ZModFive

open WeierstrassCurve

abbrev AffineSolution :=
  {xy : ZMod 5 × ZMod 5 // xy.2 ^ 2 = xy.1 ^ 3 + 1}

end WeierstrassCurve.Affine.PointCountTest.ZModFive
