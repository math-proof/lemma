import Mathlib
import Def.Algebra.AdicCompletion.PolynomialCompletion.Part4
set_option autoImplicit false


namespace Localization.AtPrime

variable {R : Type*} [CommRing R] (q : Ideal R) [hq : q.IsMaximal]

open IsLocalRing

@[simp] theorem quotientPowEquiv_mk (n : ℕ) (x : R) :
    quotientPowEquiv q n (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (algebraMap R _ x) :=
  quotientPowMap_mk q n x

theorem factorPow_quotientPowEquiv {m n : ℕ} (h : m ≤ n) (x : R ⧸ q ^ n) :
    Ideal.Quotient.factorPow _ h (quotientPowEquiv q n x)
      = quotientPowEquiv q m (Ideal.Quotient.factorPow q h x) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  show Ideal.Quotient.factor _ (quotientPowEquiv q n (Ideal.Quotient.mk _ x))
    = quotientPowEquiv q m (Ideal.Quotient.factor _ (Ideal.Quotient.mk _ x))
  rw [quotientPowEquiv_mk, Ideal.Quotient.factor_mk, Ideal.Quotient.factor_mk, quotientPowEquiv_mk]

end Localization.AtPrime
