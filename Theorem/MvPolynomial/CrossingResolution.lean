module

public import Mathlib
public import Theorem.MvPolynomial.CrossingQuotient
public import Abbrev.MvPolynomial_CrossingResolution

public noncomputable section

set_option autoImplicit false

noncomputable section

namespace MvPolynomial

namespace CrossingQuotient

variable {W : Type*} [CommRing W] (t : W)

public theorem U_mul_V : U t * V t = algebraMap W (CrossingQuotient W t) t := mk_X_mul_mk_X t


public theorem aeval_rel_eq_zero {A : Type*} [CommRing A] [Algebra W A] (a b : A)
    (h : a * b = algebraMap W A t) :
    aeval ![a, b] (X 0 * X 1 - C t : MvPolynomial (Fin 2) W) = 0 := by
  rw [map_sub, map_mul, aeval_X, aeval_X, aeval_C]
  simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [h, sub_self]


public theorem lift_mk {A : Type*} [CommRing A] [Algebra W A] (a b : A) (h : a * b = algebraMap W A t)
    (p : MvPolynomial (Fin 2) W) : lift t a b h (mk t p) = aeval ![a, b] p := rfl


@[simp] public theorem lift_U {A : Type*} [CommRing A] [Algebra W A] (a b : A)
    (h : a * b = algebraMap W A t) : lift t a b h (U t) = a := by
  rw [lift_mk, aeval_X]; rfl


@[simp] public theorem lift_V {A : Type*} [CommRing A] [Algebra W A] (a b : A)
    (h : a * b = algebraMap W A t) : lift t a b h (V t) = b := by
  rw [lift_mk, aeval_X]; rfl


public theorem resolutionChart_U (e : ℕ) (i : Fin e) :
    resolutionChart t e i (U (t ^ e)) = algebraMap W _ (t ^ (i : ℕ)) * U t := lift_U _ _ _ _


public theorem resolutionChart_V (e : ℕ) (i : Fin e) :
    resolutionChart t e i (V (t ^ e)) = algebraMap W _ (t ^ (e - 1 - i)) * V t := lift_V _ _ _ _


public theorem transitionUp_U :
    transitionUp t (U t) = IsLocalization.Away.invSelf (V t) := lift_U _ _ _ _


public theorem transitionUp_V : transitionUp t (V t) =
    algebraMap W _ t * algebraMap (CrossingQuotient W t) (Localization.Away (V t)) (V t) :=
  lift_V _ _ _ _


public theorem transitionDown_U : transitionDown t (U t) =
    algebraMap W _ t * algebraMap (CrossingQuotient W t) (Localization.Away (U t)) (U t) :=
  lift_U _ _ _ _


public theorem transitionDown_V :
    transitionDown t (V t) = IsLocalization.Away.invSelf (U t) := lift_V _ _ _ _

end CrossingQuotient

end MvPolynomial

end
