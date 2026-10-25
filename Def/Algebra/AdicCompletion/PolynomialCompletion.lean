import Mathlib
import Theorem.Algebra.AdicCompletion.PolynomialCompletion
set_option autoImplicit false


namespace AdicCompletion

section Levelwise

variable {R S : Type*} [CommRing R] [CommRing S] (I : Ideal R) (J : Ideal S)

variable (e : ∀ n, R ⧸ I ^ n ≃+* S ⧸ J ^ n)
  (he : ∀ {m n : ℕ} (h : m ≤ n) (x : R ⧸ I ^ n),
    Ideal.Quotient.factorPow J h (e n x) = e m (Ideal.Quotient.factorPow I h x))

noncomputable def levelwiseHom : AdicCompletion I R →+* AdicCompletion J S :=
  liftRingHom J (fun n => (e n).toRingHom.comp (evalₐ I n).toRingHom) (levelwise_compat I J e he)

end Levelwise
end AdicCompletion
