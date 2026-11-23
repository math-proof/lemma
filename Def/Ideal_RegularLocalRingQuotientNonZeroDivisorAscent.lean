module

public import Mathlib

@[expose] public section

set_option autoImplicit false

noncomputable section

open IsLocalRing

namespace RegularLocalRingQuotientAscent


section Gates

variable (p : ℕ) [Fact p.Prime]

def padicIntQuotientSpanPEquiv : (ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p])}) ≃+* ZMod p :=
  (Ideal.quotEquivOfEq (by rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p])).trans
    (RingHom.quotientKerEquivOfSurjective (ZMod.ringHom_surjective PadicInt.toZMod))

end Gates

section Teeth

def dualNumberFst (K : Type*) [CommRing K] : DualNumber K →+* K where
  toFun := TrivSqZeroExt.fst
  map_one' := TrivSqZeroExt.fst_one
  map_mul' := TrivSqZeroExt.fst_mul
  map_zero' := TrivSqZeroExt.fst_zero
  map_add' := TrivSqZeroExt.fst_add

def dualNumberQuotientSpanEpsEquiv (K : Type*) [CommRing K] :
    (DualNumber K ⧸ Ideal.span {(DualNumber.eps : DualNumber K)}) ≃+* K :=
  (Ideal.quotEquivOfEq (ker_dualNumberFst K).symm).trans
    (RingHom.quotientKerEquivOfSurjective (dualNumberFst_surjective K))

end Teeth

end RegularLocalRingQuotientAscent

/--
info: 'RegularLocalRingQuotientAscent.spanFinrank_comap_le_of_surjective' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms RegularLocalRingQuotientAscent.spanFinrank_comap_le_of_surjective

/--
info: 'RegularLocalRingQuotientAscent.spanFinrank_maximalIdeal_le_of_surjective' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms RegularLocalRingQuotientAscent.spanFinrank_maximalIdeal_le_of_surjective

/--
info: 'RegularLocalRingQuotientAscent.finrank_cotangentSpace_le_of_surjective' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms RegularLocalRingQuotientAscent.finrank_cotangentSpace_le_of_surjective

/--
info: 'RegularLocalRingQuotientAscent.isRegularLocalRing_of_isRegularLocalRing_quotient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms RegularLocalRingQuotientAscent.isRegularLocalRing_of_isRegularLocalRing_quotient

/--
info: 'RegularLocalRingQuotientAscent.isRegularLocalRing_of_surjective_ker_span_singleton' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms RegularLocalRingQuotientAscent.isRegularLocalRing_of_surjective_ker_span_singleton

/--
info: 'RegularLocalRingQuotientAscent.gate_padicInt_hypotheses' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RegularLocalRingQuotientAscent.gate_padicInt_hypotheses

/--
info: 'RegularLocalRingQuotientAscent.gate_isRegularLocalRing_padicInt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms RegularLocalRingQuotientAscent.gate_isRegularLocalRing_padicInt

/--
info: 'RegularLocalRingQuotientAscent.gate_padicInt_conclusion_consistency' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms RegularLocalRingQuotientAscent.gate_padicInt_conclusion_consistency

/--
info: 'RegularLocalRingQuotientAscent.gate_padicInt_dimension_jump' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RegularLocalRingQuotientAscent.gate_padicInt_dimension_jump

/--
info: 'RegularLocalRingQuotientAscent.quotient_span_eps_isRegularLocalRing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms RegularLocalRingQuotientAscent.quotient_span_eps_isRegularLocalRing

/--
info: 'RegularLocalRingQuotientAscent.eps_notMem_nonZeroDivisors' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RegularLocalRingQuotientAscent.eps_notMem_nonZeroDivisors

/--
info: 'RegularLocalRingQuotientAscent.not_isRegularLocalRing_dualNumber' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms RegularLocalRingQuotientAscent.not_isRegularLocalRing_dualNumber

/--
info: 'RegularLocalRingQuotientAscent.not_forall_isRegularLocalRing_of_quotient_dropping_nonZeroDivisor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms RegularLocalRingQuotientAscent.not_forall_isRegularLocalRing_of_quotient_dropping_nonZeroDivisor

end

end
