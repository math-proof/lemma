import Mathlib
import Lemma.Definitions.Def_MvPolynomial_CrossingQuotient

set_option autoImplicit false

noncomputable section

namespace MvPolynomial

namespace CrossingQuotient

variable {W : Type*} [CommRing W] (t : W)

abbrev U : CrossingQuotient W t := mk t (X 0)

abbrev V : CrossingQuotient W t := mk t (X 1)

theorem U_mul_V : U t * V t = algebraMap W (CrossingQuotient W t) t := mk_X_mul_mk_X t

theorem aeval_rel_eq_zero {A : Type*} [CommRing A] [Algebra W A] (a b : A)
    (h : a * b = algebraMap W A t) :
    aeval ![a, b] (X 0 * X 1 - C t : MvPolynomial (Fin 2) W) = 0 := by
  rw [map_sub, map_mul, aeval_X, aeval_X, aeval_C]
  simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [h, sub_self]

def lift {A : Type*} [CommRing A] [Algebra W A] (a b : A) (h : a * b = algebraMap W A t) :
    CrossingQuotient W t →ₐ[W] A :=
  Ideal.Quotient.liftₐ (Ideal.span {(X 0 * X 1 - C t : MvPolynomial (Fin 2) W)}) (aeval ![a, b])
    (fun p hp => by
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hp
      rw [map_mul, aeval_rel_eq_zero t a b h, mul_zero])

theorem lift_mk {A : Type*} [CommRing A] [Algebra W A] (a b : A) (h : a * b = algebraMap W A t)
    (p : MvPolynomial (Fin 2) W) : lift t a b h (mk t p) = aeval ![a, b] p := rfl

@[simp] theorem lift_U {A : Type*} [CommRing A] [Algebra W A] (a b : A)
    (h : a * b = algebraMap W A t) : lift t a b h (U t) = a := by
  rw [lift_mk, aeval_X]; rfl

@[simp] theorem lift_V {A : Type*} [CommRing A] [Algebra W A] (a b : A)
    (h : a * b = algebraMap W A t) : lift t a b h (V t) = b := by
  rw [lift_mk, aeval_X]; rfl

def resolutionChart (e : ℕ) (i : Fin e) : CrossingQuotient W (t ^ e) →ₐ[W] CrossingQuotient W t :=
  lift (t ^ e) (algebraMap W _ (t ^ (i : ℕ)) * U t) (algebraMap W _ (t ^ (e - 1 - i)) * V t) (by
    have hi : (i : ℕ) + (e - 1 - i) + 1 = e := by have := i.2; omega
    rw [mul_mul_mul_comm, U_mul_V, ← map_mul, ← map_mul, ← pow_add, ← pow_succ, hi])

theorem resolutionChart_U (e : ℕ) (i : Fin e) :
    resolutionChart t e i (U (t ^ e)) = algebraMap W _ (t ^ (i : ℕ)) * U t := lift_U _ _ _ _

theorem resolutionChart_V (e : ℕ) (i : Fin e) :
    resolutionChart t e i (V (t ^ e)) = algebraMap W _ (t ^ (e - 1 - i)) * V t := lift_V _ _ _ _

def transitionUp : CrossingQuotient W t →ₐ[W] Localization.Away (V t) :=
  lift t (IsLocalization.Away.invSelf (V t))
    (algebraMap W _ t * algebraMap (CrossingQuotient W t) _ (V t)) (by
      rw [mul_left_comm, mul_comm (IsLocalization.Away.invSelf (V t)),
        IsLocalization.Away.mul_invSelf, mul_one,
        IsScalarTower.algebraMap_apply W (CrossingQuotient W t) (Localization.Away (V t))])

theorem transitionUp_U :
    transitionUp t (U t) = IsLocalization.Away.invSelf (V t) := lift_U _ _ _ _

theorem transitionUp_V : transitionUp t (V t) =
    algebraMap W _ t * algebraMap (CrossingQuotient W t) (Localization.Away (V t)) (V t) :=
  lift_V _ _ _ _

def transitionDown : CrossingQuotient W t →ₐ[W] Localization.Away (U t) :=
  lift t (algebraMap W _ t * algebraMap (CrossingQuotient W t) _ (U t))
    (IsLocalization.Away.invSelf (U t)) (by
      rw [mul_assoc, IsLocalization.Away.mul_invSelf, mul_one,
        IsScalarTower.algebraMap_apply W (CrossingQuotient W t) (Localization.Away (U t))])

theorem transitionDown_U : transitionDown t (U t) =
    algebraMap W _ t * algebraMap (CrossingQuotient W t) (Localization.Away (U t)) (U t) :=
  lift_U _ _ _ _

theorem transitionDown_V :
    transitionDown t (V t) = IsLocalization.Away.invSelf (U t) := lift_V _ _ _ _

end CrossingQuotient

end MvPolynomial

end
