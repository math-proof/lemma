import Mathlib
import Theorem.Algebra.AdicCompletion.PolynomialCompletion.Part5
set_option autoImplicit false


namespace AdicCompletion

variable {R : Type*} [CommRing R] (q : Ideal R) [q.IsMaximal]

open IsLocalRing

noncomputable def localizationEquiv :
    AdicCompletion q R ≃+*
      AdicCompletion (maximalIdeal (Localization.AtPrime q)) (Localization.AtPrime q) :=
  ofLevelwiseEquiv q _ (Localization.AtPrime.quotientPowEquiv q)
    (Localization.AtPrime.factorPow_quotientPowEquiv q)

end AdicCompletion
