import Mathlib
import Theorem.Algebra.AdicCompletion.PolynomialCompletion.Part4
set_option autoImplicit false


namespace Localization.AtPrime

variable {R : Type*} [CommRing R] (q : Ideal R) [hq : q.IsMaximal]

open IsLocalRing

noncomputable def quotientPowEquiv (n : ℕ) :
    R ⧸ q ^ n ≃+* Localization.AtPrime q ⧸ (maximalIdeal (Localization.AtPrime q)) ^ n :=
  RingEquiv.ofBijective _ (quotientPowMap_bijective q n)

end Localization.AtPrime
