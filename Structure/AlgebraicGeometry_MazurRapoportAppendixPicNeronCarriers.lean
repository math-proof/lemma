import Mathlib
import Structure.AlgebraicGeometry_NeronModelPropertyBundleCarrier

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

namespace MazurRapoportAppendix

section SchemeLevelClauses

variable {X Y : Scheme.{u}}

def PushforwardStructureSheafIso (f : X ⟶ Y) : Prop :=
  ∀ U : Y.Opens, IsIso (f.app U)


def CohomologicallyFlatInDimZero (f : X ⟶ Y) : Prop :=
  ∀ (T : Scheme.{u}) (g : T ⟶ Y), PushforwardStructureSheafIso (pullback.snd f g)


end SchemeLevelClauses

section ComponentTable

variable {ι : Type*} [Fintype ι]

structure SpecialFibreComponentTable (ι : Type*) [Fintype ι] where

  mult : ι → ℕ

  inter : ι → ι → ℤ

  mult_pos : ∀ i, 0 < mult i

  inter_symm : ∀ i j, inter i j = inter j i

  fibre_inter_zero : ∀ i, ∑ j, inter i j * (mult j : ℤ) = 0

def GcdOfMultiplicitiesIsOne (t : SpecialFibreComponentTable ι) : Prop :=
  Finset.univ.gcd t.mult = 1


def intersectionAlpha (t : SpecialFibreComponentTable ι) : (ι → ℤ) →+ (ι → ℤ) where
  toFun c := fun j => ∑ i, c i * t.inter i j
  map_zero' := by
    funext j
    simp
  map_add' a b := by
    funext j
    simp [add_mul, Finset.sum_add_distrib]

@[simp]

def multiplicityBeta (t : SpecialFibreComponentTable ι) : (ι → ℤ) →+ ℤ where
  toFun a := ∑ i, a i * (t.mult i : ℤ)
  map_zero' := by simp
  map_add' a b := by simp [add_mul, Finset.sum_add_distrib]

@[simp]


def degreeZeroSublattice (t : SpecialFibreComponentTable ι) : AddSubgroup (ι → ℤ) :=
  (multiplicityBeta t).ker


def imageOfIntersectionAlpha (t : SpecialFibreComponentTable ι) :
    AddSubgroup ↥(degreeZeroSublattice t) :=
  ((intersectionAlpha t).range).addSubgroupOf (degreeZeroSublattice t)


abbrev AppendixComponentGroup (t : SpecialFibreComponentTable ι) : Type _ :=
  ↥(degreeZeroSublattice t) ⧸ imageOfIntersectionAlpha t

def appendixComponentGroupClass (t : SpecialFibreComponentTable ι) :
    ↥(degreeZeroSublattice t) →+ AppendixComponentGroup t :=
  QuotientAddGroup.mk' (imageOfIntersectionAlpha t)


end ComponentTable

section GoodReductionGate


end GoodReductionGate

section TwoComponentGate


end TwoComponentGate

section HeldCarriers

variable (R K : Type u) [CommRing R] [Field K] [Algebra R K]
variable [IsDomain R] [IsDedekindDomain R] [IsFractionRing R K]
variable {X N : Scheme.{u}}

structure Thm13RaynaudPicNeronInput
    (f : X ⟶ Spec (CommRingCat.of R)) (ν : N ⟶ Spec (CommRingCat.of R))
    {ι : Type*} [Fintype ι] (t : SpecialFibreComponentTable ι) : Prop where

  model_proper : IsProper f

  model_flat : Flat f

  gcd_multiplicities : GcdOfMultiplicitiesIsOne t

  pushforward_structure_sheaf : PushforwardStructureSheafIso f

  cohomologically_flat : CohomologicallyFlatInDimZero f

  neron_bundle : NeronModelPropertyBundle R K ν

structure Prop14ComponentPresentationInput
    {ι : Type*} [Fintype ι] (t : SpecialFibreComponentTable ι)
    (P : Type*) [AddCommGroup P] (degRestrict : P →+ (ι → ℤ)) (E : AddSubgroup P)
    (Φ : Type*) [AddCommGroup Φ] (specialise : P →+ Φ) : Prop where

  unitClosure_deg_zero : ∀ x ∈ E, degRestrict x = 0

  degRestrict_surjective : Function.Surjective degRestrict

  presentation : ∃ e : AppendixComponentGroup t ≃+ Φ,
    ∀ (x : P) (hx : degRestrict x ∈ degreeZeroSublattice t),
      e (appendixComponentGroupClass t ⟨degRestrict x, hx⟩) = specialise x

structure MazurRapoportAppendixPackage
    (f : X ⟶ Spec (CommRingCat.of R)) (ν : N ⟶ Spec (CommRingCat.of R))
    {ι : Type*} [Fintype ι] (t : SpecialFibreComponentTable ι)
    (P : Type*) [AddCommGroup P] (degRestrict : P →+ (ι → ℤ)) (E : AddSubgroup P)
    (Φ : Type*) [AddCommGroup Φ] (specialise : P →+ Φ) : Prop where

  thm13 : Thm13RaynaudPicNeronInput R K f ν t

  prop14 : Prop14ComponentPresentationInput t P degRestrict E Φ specialise

end HeldCarriers

namespace Prop14ComponentPresentationInput

variable {ι : Type*} [Fintype ι] {t : SpecialFibreComponentTable ι}
variable {P : Type*} [AddCommGroup P] {degRestrict : P →+ (ι → ℤ)} {E : AddSubgroup P}
variable {Φ : Type*} [AddCommGroup Φ] {specialise : P →+ Φ}


end Prop14ComponentPresentationInput

section SatGates


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
