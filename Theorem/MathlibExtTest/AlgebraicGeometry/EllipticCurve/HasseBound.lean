module
public import Theorem.Scheme.EllipticCurve.HasseBound
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Tactic.NormNum
public import Instance.MathlibExtTest.AlgebraicGeometry.EllipticCurve.HasseBound.Part2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/AlgebraicGeometry/EllipticCurve/HasseBound.lean -/
namespace MathlibExtTest.AlgebraicGeometry.EllipticCurve.HasseBound

open WeierstrassCurve

open MathlibExt.AlgebraicGeometry.EllipticCurve

/-- The general Hasse theorem applies to an explicit characteristic-two elliptic curve. -/
example :
    (((Nat.card (ZMod 2) : ℤ) + 1 -
        (Nat.card curve.toAffine.Point : ℤ)) ^ 2 ≤
      4 * (Nat.card (ZMod 2) : ℤ)) :=
  HasseBoundWanted.hasse_bound curve

end MathlibExtTest.AlgebraicGeometry.EllipticCurve.HasseBound
