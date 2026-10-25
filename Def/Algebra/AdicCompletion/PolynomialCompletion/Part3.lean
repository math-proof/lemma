import Mathlib
import Theorem.Algebra.AdicCompletion.PolynomialCompletion.Part3
set_option autoImplicit false


namespace Localization.AtPrime

variable {R : Type*} [CommRing R] (q : Ideal R) [hq : q.IsMaximal]

open IsLocalRing

def quotientPowMap (n : ℕ) :
    R ⧸ q ^ n →+* Localization.AtPrime q ⧸ (maximalIdeal (Localization.AtPrime q)) ^ n :=
  Ideal.quotientMap _ (algebraMap R (Localization.AtPrime q)) (pow_le_comap_maximalIdeal_pow q n)

end Localization.AtPrime
