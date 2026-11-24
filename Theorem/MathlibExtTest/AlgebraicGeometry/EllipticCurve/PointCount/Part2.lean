module
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
public import Def.AlgebraicGeometry.EllipticCurve.PointCount
public import Theorem.Nat.FrobeniusTrace.eq.SubAddCardF1CardPoint.of.AffineF
public import Instance.MathlibExtTest.AlgebraicGeometry.EllipticCurve.PointCount.Part3


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/AlgebraicGeometry/EllipticCurve/PointCount.lean -/
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
