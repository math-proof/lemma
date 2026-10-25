import Mathlib
import Def.Algebra.AdicCompletion.PolynomialCompletion
set_option autoImplicit false


namespace AdicCompletion

section Levelwise

variable {R S : Type*} [CommRing R] [CommRing S] (I : Ideal R) (J : Ideal S)

variable (e : ∀ n, R ⧸ I ^ n ≃+* S ⧸ J ^ n)
  (he : ∀ {m n : ℕ} (h : m ≤ n) (x : R ⧸ I ^ n),
    Ideal.Quotient.factorPow J h (e n x) = e m (Ideal.Quotient.factorPow I h x))

@[simp] theorem evalₐ_levelwiseHom (n : ℕ) (x : AdicCompletion I R) :
    evalₐ J n (levelwiseHom I J e he x) = e n (evalₐ I n x) :=
  evalₐ_liftRingHom J (fun n => (e n).toRingHom.comp (evalₐ I n).toRingHom)
    (levelwise_compat I J e he) n x

include he in
theorem he_symm {m n : ℕ} (h : m ≤ n) (y : S ⧸ J ^ n) :
    Ideal.Quotient.factorPow I h ((e n).symm y) = (e m).symm (Ideal.Quotient.factorPow J h y) := by
  apply (e m).injective
  rw [RingEquiv.apply_symm_apply, ← he, RingEquiv.apply_symm_apply]

end Levelwise
end AdicCompletion
