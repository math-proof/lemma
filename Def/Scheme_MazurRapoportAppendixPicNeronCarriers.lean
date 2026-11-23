module

public import Mathlib
public import Theorem.Scheme.NeronModelPropertyBundleCarrier
public import Structure.AlgebraicGeometry_MazurRapoportAppendixPicNeronCarriers

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra Scheme

namespace MazurRapoportAppendix


section GoodReductionGate

def goodReductionTable : SpecialFibreComponentTable (Fin 1) where
  mult := fun _ => 1
  inter := fun _ _ => 0
  mult_pos := fun _ => Nat.one_pos
  inter_symm := fun _ _ => rfl
  fibre_inter_zero := fun _ => by simp

end GoodReductionGate

section TwoComponentGate

def twoComponentTable : SpecialFibreComponentTable (Fin 2) where
  mult := fun _ => 1
  inter := fun i j => if i = j then -5 else 5
  mult_pos := fun _ => Nat.one_pos
  inter_symm := by decide
  fibre_inter_zero := by decide

def twoComponentWitness : Fin 2 → ℤ := fun i => if i = 0 then 1 else -1

end TwoComponentGate


section SatGates

def twoComponentRetract : (Fin 2 → ℤ) →+ ↥(degreeZeroSublattice twoComponentTable) :=
  AddMonoidHom.mk'
    (fun v =>
      ⟨v - (multiplicityBeta twoComponentTable v) • Pi.single (0 : Fin 2) (1 : ℤ), by
        have hsingle : multiplicityBeta twoComponentTable (Pi.single (0 : Fin 2) (1 : ℤ)) = 1 := by
          decide
        have hβ : multiplicityBeta twoComponentTable
            (v - (multiplicityBeta twoComponentTable v) • Pi.single (0 : Fin 2) (1 : ℤ)) = 0 := by
          rw [map_sub, map_zsmul, hsingle, smul_eq_mul, mul_one, sub_self]
        rw [degreeZeroSublattice, AddMonoidHom.mem_ker]
        exact hβ⟩)
    (fun a b => by
      apply Subtype.ext
      show (a + b) - (multiplicityBeta twoComponentTable (a + b)) •
            Pi.single (0 : Fin 2) (1 : ℤ) =
          (a - (multiplicityBeta twoComponentTable a) • Pi.single (0 : Fin 2) (1 : ℤ)) +
          (b - (multiplicityBeta twoComponentTable b) • Pi.single (0 : Fin 2) (1 : ℤ))
      rw [map_add, add_smul]
      abel)

end SatGates

end MazurRapoportAppendix

/--
info: 'MazurRapoportAppendix.multiplicityBeta_intersectionAlpha' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MazurRapoportAppendix.multiplicityBeta_intersectionAlpha

/--
info: 'MazurRapoportAppendix.pushforwardStructureSheafIso_of_isIso' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MazurRapoportAppendix.pushforwardStructureSheafIso_of_isIso

/--
info: 'MazurRapoportAppendix.cohomologicallyFlatInDimZero_of_isIso' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MazurRapoportAppendix.cohomologicallyFlatInDimZero_of_isIso

/--
info: 'MazurRapoportAppendix.subsingleton_appendixComponentGroup_goodReductionTable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MazurRapoportAppendix.subsingleton_appendixComponentGroup_goodReductionTable

/--
info: 'MazurRapoportAppendix.appendixComponentGroupClass_twoComponentWitness_ne_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MazurRapoportAppendix.appendixComponentGroupClass_twoComponentWitness_ne_zero

/--
info: 'MazurRapoportAppendix.nontrivial_appendixComponentGroup_twoComponentTable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MazurRapoportAppendix.nontrivial_appendixComponentGroup_twoComponentTable

/--
info: 'MazurRapoportAppendix.Prop14ComponentPresentationInput.specialise_surjective' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MazurRapoportAppendix.Prop14ComponentPresentationInput.specialise_surjective

/--
info: 'MazurRapoportAppendix.Prop14ComponentPresentationInput.specialise_eq_zero_of_mem_unitClosure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MazurRapoportAppendix.Prop14ComponentPresentationInput.specialise_eq_zero_of_mem_unitClosure

/--
info: 'MazurRapoportAppendix.Prop14ComponentPresentationInput.specialise_eq_zero_at_goodReduction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MazurRapoportAppendix.Prop14ComponentPresentationInput.specialise_eq_zero_at_goodReduction

/--
info: 'MazurRapoportAppendix.gate_thm13RaynaudPicNeronInput_trivialModel_zp' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MazurRapoportAppendix.gate_thm13RaynaudPicNeronInput_trivialModel_zp

/--
info: 'MazurRapoportAppendix.gate_prop14ComponentPresentationInput_goodReduction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MazurRapoportAppendix.gate_prop14ComponentPresentationInput_goodReduction

/--
info: 'MazurRapoportAppendix.gate_prop14ComponentPresentationInput_twoComponent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MazurRapoportAppendix.gate_prop14ComponentPresentationInput_twoComponent

/--
info: 'MazurRapoportAppendix.gate_mazurRapoportAppendixPackage_trivialModel_zp' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MazurRapoportAppendix.gate_mazurRapoportAppendixPackage_trivialModel_zp

end

end
