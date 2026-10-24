/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/AlgebraicGeometry/EllipticCurve/ManinTwist.lean -/

import sympy.atlas.AlgebraicGeometry.EllipticCurve.ManinTwist
import Lemma.Scheme.EllipticCurve.ManinTwist
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum

namespace MathlibExtTest.AlgebraicGeometry.EllipticCurve.ManinTwist

open WeierstrassCurve
open MathlibExt.AlgebraicGeometry.EllipticCurve

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private instance : Fact (Nat.Prime 3) := ⟨by decide⟩

/-- The elementary small-field construction covers every equation over `ZMod 3`. -/
example (W : WeierstrassCurve (ZMod 3)) : Nonempty (ManinDegreeData
    (Nat.card (ZMod 3)) (Nat.card W.toAffine.Point)) :=
  ManinTwist.manin_degree_data_of_card_eq_three (by norm_num) W

/-- The test curve `y² = x³ + x + 1` over `ZMod 5`. -/
private def curve : WeierstrassCurve (ZMod 5) :=
  ⟨0, 0, 0, 1, 1⟩

private instance : curve.IsCharNeTwoNF := ⟨rfl, rfl⟩

private instance : curve.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff]
  norm_num [curve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, isUnit_iff_ne_zero]
  decide

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
