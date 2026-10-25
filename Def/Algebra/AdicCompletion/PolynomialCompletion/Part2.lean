import Mathlib
import Theorem.Algebra.AdicCompletion.PolynomialCompletion.Part2
set_option autoImplicit false


namespace AdicCompletion

section Levelwise

variable {R S : Type*} [CommRing R] [CommRing S] (I : Ideal R) (J : Ideal S)

variable (e : ∀ n, R ⧸ I ^ n ≃+* S ⧸ J ^ n)
  (he : ∀ {m n : ℕ} (h : m ≤ n) (x : R ⧸ I ^ n),
    Ideal.Quotient.factorPow J h (e n x) = e m (Ideal.Quotient.factorPow I h x))

noncomputable def ofLevelwiseEquiv : AdicCompletion I R ≃+* AdicCompletion J S :=
  RingEquiv.ofRingHom (levelwiseHom I J e he)
    (levelwiseHom J I (fun n => (e n).symm) (he_symm I J e he))
    (RingHom.ext fun y => ext_evalₐ fun n => by simp)
    (RingHom.ext fun x => ext_evalₐ fun n => by simp)

end Levelwise
end AdicCompletion
