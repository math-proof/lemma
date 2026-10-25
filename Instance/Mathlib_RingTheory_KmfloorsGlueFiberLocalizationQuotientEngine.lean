-- Carved from Lemma/Definitions/Def_Mathlib_RingTheory_KmfloorsGlueFiberLocalizationQuotientEngine.lean: instance decls only.
import Mathlib

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


/--
info: 'kmfloorsGlue_one_tmul_eq_zero_of_mem_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/

/--
info: 'kmfloorsGlue_isUnit_algebraMap_fiber_of_notMem' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/

/--
info: 'kmfloorsGlue_mem_iff_one_tmul_mem' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/

/--
info: 'kmfloorsGlue_fiberEval' depends on axioms: [propext, Classical.choice, Quot.sound]
-/

/--
info: 'kmfloorsGlue_isLocalization_fiberEval' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/

/--
info: 'kmfloorsGlue_fiberLocalizationAtPrimeQuotientEquiv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/

/--
info: 'kmfloorsGlue_isRegularLocalRing_localizationQuotient_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/

/--
info: 'kmfloorsGlue_maximalIdeal_map_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/

/--
info: 'kmfloorsGlue_satGate_identityChart' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/

/--
info: 'kmfloorsGlue_satGate_production_chartPair_int_three' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/

/--
info: 'kmfloorsGlue_falsifGate_wrongPrime_targetCollapses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/

end
