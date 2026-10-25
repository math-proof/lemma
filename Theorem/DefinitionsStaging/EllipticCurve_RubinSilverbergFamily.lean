import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Def.EllipticCurve_RubinSilverbergFamily
set_option autoImplicit false


section KleinForms

variable {R : Type*} [CommRing R]


end KleinForms

namespace RubinSilverberg

section KleinCurve

variable {K : Type*} [Field K]


theorem pt_eq_some {W : WeierstrassCurve K} {x y : K} (h : W.toAffine.Nonsingular x y) :
    pt W x y = WeierstrassCurve.Affine.Point.some x y h := by
  unfold pt
  exact dif_pos h

theorem pt_eq_zero {W : WeierstrassCurve K} {x y : K} (h : ¬ W.toAffine.Nonsingular x y) :
    pt W x y = 0 := by
  unfold pt
  exact dif_neg h

end KleinCurve

section Datum

variable {K : Type*} [Field K]


end Datum

section Icosahedral

variable {K : Type*} [Field K]


theorem moeb_eq_div (g : Matrix (Fin 2) (Fin 2) K) (u : K) : moeb g u = moebNum g u / moebDen g u := rfl


end Icosahedral
end RubinSilverberg
