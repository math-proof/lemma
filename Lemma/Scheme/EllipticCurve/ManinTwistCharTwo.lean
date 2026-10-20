import Mathlib
import sympy.Basic
import sympy.atlas.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo
open Polynomial
open scoped CharTwo
open MathlibExt.AlgebraicGeometry.EllipticCurve.ManinProjectiveDegree
open MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo


/--
[manin_degree_data_of_card_eq_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
private lemma manin_degree_data_of_card_eq_two_eq
  {F : Type u} [Field F] [Finite F]
  {W : WeierstrassCurve F}
-- given
  (hF : Nat.card F = 2) :
-- imply
  Nonempty (MathlibExt.AlgebraicGeometry.EllipticCurve.ManinDegreeData
    (Nat.card F) (Nat.card W.toAffine.Point)) := by
-- proof
  apply MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo.manin_degree_data_of_card_eq_two hF W

/--
[manin_degree_data_of_card_eq_four](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
private lemma manin_degree_data_of_card_eq_four_eq
  {F : Type u} [Field F] [Finite F]
  {W : WeierstrassCurve F}
-- given
  (hF : Nat.card F = 4) :
-- imply
  Nonempty (MathlibExt.AlgebraicGeometry.EllipticCurve.ManinDegreeData
    (Nat.card F) (Nat.card W.toAffine.Point)) := by
-- proof
  apply MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo.manin_degree_data_of_card_eq_four hF W

/--
[manin_degree_data_of_isCharTwoNF](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
private lemma manin_degree_data_of_isCharTwoNF_eq
  {F : Type u} [Field F] [Finite F] [CharP F 2]
  {W : WeierstrassCurve F} [W.IsElliptic] [W.IsCharTwoNF] :
-- imply
  Nonempty (MathlibExt.AlgebraicGeometry.EllipticCurve.ManinDegreeData
    (Nat.card F) (Nat.card W.toAffine.Point)) := by
-- proof
  apply MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo.manin_degree_data_of_isCharTwoNF W

/--
[hasse_bound_of_isCharTwoNF](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
private lemma hasse_bound_of_isCharTwoNF_eq
  {F : Type u} [Field F] [Finite F] [CharP F 2]
  {W : WeierstrassCurve F} [W.IsElliptic] [W.IsCharTwoNF] :
-- imply
  (((Nat.card F : ℤ) + 1 - (Nat.card W.toAffine.Point : ℤ)) ^ 2 ≤
    4 * (Nat.card F : ℤ)) := by
-- proof
  apply MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo.hasse_bound_of_isCharTwoNF W

/--
[hasse_bound_of_isCharTwoJNeZeroNF](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
private lemma hasse_bound_of_isCharTwoJNeZeroNF_eq
  {F : Type u} [Field F] [Finite F] [CharP F 2]
  {W : WeierstrassCurve F} [W.IsElliptic] [W.IsCharTwoJNeZeroNF] :
-- imply
  (((Nat.card F : ℤ) + 1 - (Nat.card W.toAffine.Point : ℤ)) ^ 2 ≤
    4 * (Nat.card F : ℤ)) := by
-- proof
  apply MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo.hasse_bound_of_isCharTwoJNeZeroNF W

/--
[hasse_bound_of_isCharTwoJEqZeroNF](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
private lemma hasse_bound_of_isCharTwoJEqZeroNF_eq
  {F : Type u} [Field F] [Finite F] [CharP F 2]
  {W : WeierstrassCurve F} [W.IsElliptic] [W.IsCharTwoJEqZeroNF] :
-- imply
  (((Nat.card F : ℤ) + 1 - (Nat.card W.toAffine.Point : ℤ)) ^ 2 ≤
    4 * (Nat.card F : ℤ)) := by
-- proof
  apply MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo.hasse_bound_of_isCharTwoJEqZeroNF W


-- created on 2026-10-20
