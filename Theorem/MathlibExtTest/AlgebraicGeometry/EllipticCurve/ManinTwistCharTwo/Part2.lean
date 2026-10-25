/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean -/

import Theorem.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo.Part22
import Lemma.Scheme.EllipticCurve.ManinTwistCharTwo
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Tactic.NormNum
import Instance.MathlibExtTest.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo.Part3


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
