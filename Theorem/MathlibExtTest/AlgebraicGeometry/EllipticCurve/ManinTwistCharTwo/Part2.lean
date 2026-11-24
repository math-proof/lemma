module
public import Theorem.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo.Part22
public import Theorem.Scheme.EllipticCurve.ManinTwistCharTwo
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.Tactic.NormNum
public import Instance.MathlibExtTest.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo.Part3


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean -/
namespace MathlibExtTest.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

open WeierstrassCurve

open MathlibExt.AlgebraicGeometry.EllipticCurve

/-- The supersingular characteristic-two case applies over `ZMod 2`. -/
example :
    (((Nat.card (ZMod 2) : ℤ) + 1 -
        (Nat.card supersingularCurve.toAffine.Point : ℤ)) ^ 2 ≤
      4 * (Nat.card (ZMod 2) : ℤ)) :=
  ManinTwistCharTwo.hasse_bound_of_isCharTwoJEqZeroNF supersingularCurve

end MathlibExtTest.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo
