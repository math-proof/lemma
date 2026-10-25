/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/AlgebraicGeometry/EllipticCurve/ManinTwist.lean -/

import Theorem.AlgebraicGeometry.EllipticCurve.ManinTwist.Part15
import Lemma.Scheme.EllipticCurve.ManinTwist
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum
import Instance.MathlibExtTest.AlgebraicGeometry.EllipticCurve.ManinTwist.Part2


namespace MathlibExtTest.AlgebraicGeometry.EllipticCurve.ManinTwist

open WeierstrassCurve

open MathlibExt.AlgebraicGeometry.EllipticCurve

/-- Manin's odd-characteristic construction produces the complete degree data. -/
example : Nonempty (ManinDegreeData
    (Nat.card (ZMod 5)) (Nat.card curve.toAffine.Point)) :=
  ManinTwist.manin_degree_data_of_isCharNeTwoNF curve

/-- Manin's odd-characteristic theorem applies to a concrete elliptic curve over `ZMod 5`. -/
example :
    (((Nat.card (ZMod 5) : ℤ) + 1 - (Nat.card curve.toAffine.Point : ℤ)) ^ 2 ≤
      4 * (Nat.card (ZMod 5) : ℤ)) :=
  MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist.hasse_bound_of_isCharNeTwoNF curve

end MathlibExtTest.AlgebraicGeometry.EllipticCurve.ManinTwist
