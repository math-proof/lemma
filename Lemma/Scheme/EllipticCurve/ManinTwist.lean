import Mathlib
import sympy.Basic
import sympy.atlas.AlgebraicGeometry.EllipticCurve.ManinTwist
open Polynomial
open MathlibExt.AlgebraicGeometry.EllipticCurve.ManinProjectiveDegree
open MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist


/--
[manin_degree_data_of_card_eq_three](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwist.lean)
-/
@[path]
private lemma manin_degree_data_of_card_eq_three_eq
  {F : Type u} [Field F] [Finite F]
  {W : WeierstrassCurve F}
-- given
  (hF : Nat.card F = 3) :
-- imply
  Nonempty (MathlibExt.AlgebraicGeometry.EllipticCurve.ManinDegreeData
    (Nat.card F) (Nat.card W.toAffine.Point)) := by
-- proof
  apply MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist.manin_degree_data_of_card_eq_three hF W

/--
[manin_degree_data_of_isCharNeTwoNF](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwist.lean)
-/
@[path]
private lemma manin_degree_data_of_isCharNeTwoNF_eq
  {F : Type u} [Field F] [Finite F]
  {W : WeierstrassCurve F} [W.IsElliptic] [W.IsCharNeTwoNF] :
-- imply
  Nonempty (MathlibExt.AlgebraicGeometry.EllipticCurve.ManinDegreeData
    (Nat.card F) (Nat.card W.toAffine.Point)) := by
-- proof
  apply MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist.manin_degree_data_of_isCharNeTwoNF W

/--
[hasse_bound_of_isCharNeTwoNF](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwist.lean)
-/
@[path]
private lemma hasse_bound_of_isCharNeTwoNF_eq
  {F : Type u} [Field F] [Finite F]
  {W : WeierstrassCurve F} [W.IsElliptic] [W.IsCharNeTwoNF] :
-- imply
  (((Nat.card F : ℤ) + 1 - (Nat.card W.toAffine.Point : ℤ)) ^ 2 ≤
    4 * (Nat.card F : ℤ)) := by
-- proof
  apply MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist.hasse_bound_of_isCharNeTwoNF W


-- created on 2026-10-20
