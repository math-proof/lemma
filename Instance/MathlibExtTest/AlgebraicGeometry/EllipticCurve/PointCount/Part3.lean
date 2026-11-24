module
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
public import Def.AlgebraicGeometry.EllipticCurve.PointCount
public import Theorem.Nat.FrobeniusTrace.eq.SubAddCardF1CardPoint.of.AffineF
public import Abbrev.MathlibExtTest.AlgebraicGeometry.EllipticCurve.PointCount


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/AlgebraicGeometry/EllipticCurve/PointCount.lean -/
namespace WeierstrassCurve.Affine.PointCountTest.ZModFive

open WeierstrassCurve

instance : Fintype AffineSolution :=
  Fintype.subtype (Finset.univ.filter fun xy : ZMod 5 × ZMod 5 => xy.2 ^ 2 = xy.1 ^ 3 + 1)
    (by simp)

end WeierstrassCurve.Affine.PointCountTest.ZModFive
