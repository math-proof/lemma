module

public import Mathlib
public import Def.MvPolynomial_CrossingQuotient
public import Abbrev.MvPolynomial_CrossingResolution

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace MvPolynomial

namespace CrossingQuotient

variable {W : Type*} [CommRing W] (t : W)

def lift {A : Type*} [CommRing A] [Algebra W A] (a b : A) (h : a * b = algebraMap W A t) :
    CrossingQuotient W t →ₐ[W] A :=
  Ideal.Quotient.liftₐ (Ideal.span {(X 0 * X 1 - C t : MvPolynomial (Fin 2) W)}) (aeval ![a, b])
    (fun p hp => by
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hp
      rw [map_mul, aeval_rel_eq_zero t a b h, mul_zero])

def resolutionChart (e : ℕ) (i : Fin e) : CrossingQuotient W (t ^ e) →ₐ[W] CrossingQuotient W t :=
  lift (t ^ e) (algebraMap W _ (t ^ (i : ℕ)) * U t) (algebraMap W _ (t ^ (e - 1 - i)) * V t) (by
    have hi : (i : ℕ) + (e - 1 - i) + 1 = e := by have := i.2; omega
    rw [mul_mul_mul_comm, U_mul_V, ← map_mul, ← map_mul, ← pow_add, ← pow_succ, hi])

def transitionUp : CrossingQuotient W t →ₐ[W] Localization.Away (V t) :=
  lift t (IsLocalization.Away.invSelf (V t))
    (algebraMap W _ t * algebraMap (CrossingQuotient W t) _ (V t)) (by
      rw [mul_left_comm, mul_comm (IsLocalization.Away.invSelf (V t)),
        IsLocalization.Away.mul_invSelf, mul_one,
        IsScalarTower.algebraMap_apply W (CrossingQuotient W t) (Localization.Away (V t))])

def transitionDown : CrossingQuotient W t →ₐ[W] Localization.Away (U t) :=
  lift t (algebraMap W _ t * algebraMap (CrossingQuotient W t) _ (U t))
    (IsLocalization.Away.invSelf (U t)) (by
      rw [mul_assoc, IsLocalization.Away.mul_invSelf, mul_one,
        IsScalarTower.algebraMap_apply W (CrossingQuotient W t) (Localization.Away (U t))])

end CrossingQuotient

end MvPolynomial

end

end
