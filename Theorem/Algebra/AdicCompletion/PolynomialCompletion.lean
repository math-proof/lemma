import Mathlib
set_option autoImplicit false


namespace AdicCompletion

section Levelwise

variable {R S : Type*} [CommRing R] [CommRing S] (I : Ideal R) (J : Ideal S)

theorem factorPow_evalₐ {m n : ℕ} (h : m ≤ n) (x : AdicCompletion I R) :
    Ideal.Quotient.factorPow I h (evalₐ I n x) = evalₐ I m x := by
  induction x using AdicCompletion.induction_on with
  | _ a =>
    rw [evalₐ_mk, evalₐ_mk]
    simp only [Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk]
    exact Ideal.mk_eq_mk I h a

variable (e : ∀ n, R ⧸ I ^ n ≃+* S ⧸ J ^ n)
  (he : ∀ {m n : ℕ} (h : m ≤ n) (x : R ⧸ I ^ n),
    Ideal.Quotient.factorPow J h (e n x) = e m (Ideal.Quotient.factorPow I h x))

include he in
theorem levelwise_compat {m n : ℕ} (h : m ≤ n) :
    (Ideal.Quotient.factorPow J h).comp ((e n).toRingHom.comp (evalₐ I n).toRingHom)
      = (e m).toRingHom.comp (evalₐ I m).toRingHom := by
  ext x
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
  rw [he, factorPow_evalₐ]

end Levelwise
end AdicCompletion
