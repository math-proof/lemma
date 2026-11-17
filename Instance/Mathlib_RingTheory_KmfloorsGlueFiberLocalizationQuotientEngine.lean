-- Carved from Lemma/Definitions/Def_Mathlib_RingTheory_KmfloorsGlueFiberLocalizationQuotientEngine.lean: instance decls only.

module

public import Mathlib

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

universe u v w

open TensorProduct


section SatGates

variable {A : Type u} [CommRing A]

instance kmfloorsGlue_int_three_isPrime : (Ideal.span {(3 : ℤ)}).IsPrime :=
  (Ideal.span_singleton_prime (by norm_num)).mpr Int.prime_three

end SatGates

instance kmfloorsGlue_int_bot_isPrime : (⊥ : Ideal ℤ).IsPrime := Ideal.isPrime_bot


end
