import Mathlib
import sympy.Basic
import sympy.atlas.AlgebraicGeometry.EllipticCurve.VariableChangePoint
open WeierstrassCurve.VariableChange


/--
[mapAffineCoordinates_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/VariableChangePoint.lean)
-/
@[path]
private lemma mapAffineCoordinates_one_eq
  {F : Type u} [Field F]
  {xy : F × F} :
-- imply
  mapAffineCoordinates (1 : VariableChange F) xy = xy := by
-- proof
  apply WeierstrassCurve.VariableChange.mapAffineCoordinates_one xy

/--
[mapAffineCoordinates_mul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/VariableChangePoint.lean)
-/
@[path]
private lemma mapAffineCoordinates_mul_eq
  {F : Type u} [Field F]
  {C C' : VariableChange F}
  {xy : F × F} :
-- imply
  mapAffineCoordinates (C * C') xy =
    mapAffineCoordinates C' (mapAffineCoordinates C xy) := by
-- proof
  apply WeierstrassCurve.VariableChange.mapAffineCoordinates_mul C C' xy

/--
[mapAffineCoordinates_inv_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/VariableChangePoint.lean)
-/
@[path]
private lemma mapAffineCoordinates_inv_apply_eq
  {F : Type u} [Field F]
  {C : VariableChange F}
  {xy : F × F} :
-- imply
  mapAffineCoordinates C⁻¹ (mapAffineCoordinates C xy) = xy := by
-- proof
  apply WeierstrassCurve.VariableChange.mapAffineCoordinates_inv_apply C xy

/--
[mapAffineCoordinates_apply_inv](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/VariableChangePoint.lean)
-/
@[path]
private lemma mapAffineCoordinates_apply_inv_eq
  {F : Type u} [Field F]
  {C : VariableChange F}
  {xy : F × F} :
-- imply
  mapAffineCoordinates C (mapAffineCoordinates C⁻¹ xy) = xy := by
-- proof
  apply WeierstrassCurve.VariableChange.mapAffineCoordinates_apply_inv C xy

/--
[equation_mapAffineCoordinates_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/VariableChangePoint.lean)
-/
@[path]
private lemma equation_mapAffineCoordinates_iff_eq
  {F : Type u} [Field F]
  {C : VariableChange F}
  {W : WeierstrassCurve F}
  {xy : F × F} :
-- imply
  (C • W).toAffine.Equation xy.1 xy.2 ↔
    W.toAffine.Equation (mapAffineCoordinates C xy).1
    (mapAffineCoordinates C xy).2 := by
-- proof
  apply WeierstrassCurve.VariableChange.equation_mapAffineCoordinates_iff C W xy

/--
[natCard_point_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/VariableChangePoint.lean)
-/
@[path]
private lemma natCard_point_eq_eq
  {F : Type u} [Field F] [Finite F]
  {C : VariableChange F}
  {W : WeierstrassCurve F} [W.IsElliptic] :
-- imply
  Nat.card ((C • W).toAffine.Point) = Nat.card W.toAffine.Point := by
-- proof
  apply WeierstrassCurve.VariableChange.natCard_point_eq C W


-- created on 2026-10-20
