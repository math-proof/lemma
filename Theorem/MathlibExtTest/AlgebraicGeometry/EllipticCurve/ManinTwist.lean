module
public import Theorem.AlgebraicGeometry.EllipticCurve.ManinTwist.Part15
public import Theorem.Scheme.EllipticCurve.ManinTwist
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Tactic.NormNum
public import Instance.MathlibExtTest.AlgebraicGeometry.EllipticCurve.ManinTwist


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/AlgebraicGeometry/EllipticCurve/ManinTwist.lean -/
namespace MathlibExtTest.AlgebraicGeometry.EllipticCurve.ManinTwist

open WeierstrassCurve

open MathlibExt.AlgebraicGeometry.EllipticCurve

/-- The elementary small-field construction covers every equation over `ZMod 3`. -/
example (W : WeierstrassCurve (ZMod 3)) : Nonempty (ManinDegreeData
    (Nat.card (ZMod 3)) (Nat.card W.toAffine.Point)) :=
  ManinTwist.manin_degree_data_of_card_eq_three (by norm_num) W

end MathlibExtTest.AlgebraicGeometry.EllipticCurve.ManinTwist
