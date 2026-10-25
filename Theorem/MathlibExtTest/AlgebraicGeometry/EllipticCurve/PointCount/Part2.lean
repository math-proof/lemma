/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/AlgebraicGeometry/EllipticCurve/PointCount.lean -/

import Mathlib.Algebra.Field.ZMod
import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
import Def.AlgebraicGeometry.EllipticCurve.PointCount
import Lemma.Nat.FrobeniusTrace.eq.SubAddCardF1CardPoint.of.AffineF
import Instance.MathlibExtTest.AlgebraicGeometry.EllipticCurve.PointCount.Part3


namespace WeierstrassCurve.Affine.PointCountTest.ZModFive

open WeierstrassCurve

example : Fintype.card AffineSolution = 5 := by
  decide

example : Nat.card curve.Point = 6 := by
  rw [curve.natCard_point_eq_natCard_affineSolutions_add_one, natCard_affineSolutions]

example : Nat.card curve.Point ≤ 11 := by
  simpa using curve.natCard_point_le_two_mul_natCard_add_one

example : curve.frobeniusTrace = 0 := by
  rw [curve.frobeniusTrace_eq]
  norm_num [show Nat.card curve.Point = 6 by
    rw [curve.natCard_point_eq_natCard_affineSolutions_add_one, natCard_affineSolutions]]

end WeierstrassCurve.Affine.PointCountTest.ZModFive
