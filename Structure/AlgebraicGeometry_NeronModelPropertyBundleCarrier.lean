import Mathlib

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace NeronModelInfra

variable (R K : Type u) [CommRing R] [Field K] [Algebra R K]

def specGenericFibreInclusion : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R K))

@[simp]

abbrev SchemeHomOver {B Y X : Scheme.{u}} (g : Y ⟶ B) (f : X ⟶ B) :=
  {φ : Y ⟶ X // φ ≫ f = g}

variable {X Y : Scheme.{u}}

def genericFibreRestrict (f : X ⟶ Spec (CommRingCat.of R)) (g : Y ⟶ Spec (CommRingCat.of R))
    (φ : SchemeHomOver g f) :
    SchemeHomOver (pullback.snd g (specGenericFibreInclusion R K))
      (pullback.snd f (specGenericFibreInclusion R K)) :=
  ⟨pullback.lift (pullback.fst g (specGenericFibreInclusion R K) ≫ φ.1)
      (pullback.snd g (specGenericFibreInclusion R K))
      (by rw [Category.assoc, φ.2, pullback.condition]),
    pullback.lift_snd _ _ _⟩

def NeronUniqueExtension (f : X ⟶ Spec (CommRingCat.of R)) : Prop :=
  ∀ (T : Scheme.{u}) (t : T ⟶ Spec (CommRingCat.of R)), Smooth t →
    Function.Bijective (genericFibreRestrict R K f t)


structure NeronModelPropertyBundle [IsDomain R] [IsDedekindDomain R] [IsFractionRing R K]
    (f : X ⟶ Spec (CommRingCat.of R)) : Prop where

  smooth : Smooth f

  separated : IsSeparated f

  locallyOfFiniteType : LocallyOfFiniteType f

  quasiCompact : QuasiCompact f

  neronMapping : NeronUniqueExtension R K f

section ComparisonHooks

variable {R K}
variable [IsDomain R] [IsDedekindDomain R] [IsFractionRing R K]
variable {f : X ⟶ Spec (CommRingCat.of R)}


end ComparisonHooks

section RestrictHooks

variable {R K}
variable (f : X ⟶ Spec (CommRingCat.of R)) (g : Y ⟶ Spec (CommRingCat.of R))


end RestrictHooks

section IsoEngines


end IsoEngines

section SatGates


end SatGates

section TeethGate


end TeethGate

end NeronModelInfra

/--
info: 'NeronModelInfra.genericFibreRestrict_coe_eq_pullbackMap' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms NeronModelInfra.genericFibreRestrict_coe_eq_pullbackMap

/--
info: 'NeronModelInfra.neronModelPropertyBundle_iff_propertyList' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms NeronModelInfra.neronModelPropertyBundle_iff_propertyList

/--
info: 'NeronModelInfra.NeronModelPropertyBundle.existsUnique_extension' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms NeronModelInfra.NeronModelPropertyBundle.existsUnique_extension

/--
info: 'NeronModelInfra.genericFibreRestrict_bijective_of_isIso' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms NeronModelInfra.genericFibreRestrict_bijective_of_isIso

/--
info: 'NeronModelInfra.neronUniqueExtension_of_isIso' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms NeronModelInfra.neronUniqueExtension_of_isIso

/--
info: 'NeronModelInfra.neronModelPropertyBundle_id' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms NeronModelInfra.neronModelPropertyBundle_id

/--
info: 'NeronModelInfra.gate_neronModelPropertyBundle_trivialGroupScheme_zp' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms NeronModelInfra.gate_neronModelPropertyBundle_trivialGroupScheme_zp

/--
info: 'NeronModelInfra.gate_neronModelPropertyBundle_trivialGroupScheme_z3' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms NeronModelInfra.gate_neronModelPropertyBundle_trivialGroupScheme_z3

/--
info: 'NeronModelInfra.isEmpty_schemeHomOver_id_specGenericFibreInclusion_zp' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms NeronModelInfra.isEmpty_schemeHomOver_id_specGenericFibreInclusion_zp

/--
info: 'NeronModelInfra.gate_neronUniqueExtension_fails_genericFibreOnly' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms NeronModelInfra.gate_neronUniqueExtension_fails_genericFibreOnly

/--
info: 'NeronModelInfra.gate_neronModelPropertyBundle_not_genericFibreOnly' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms NeronModelInfra.gate_neronModelPropertyBundle_not_genericFibreOnly

/--
info: 'NeronModelInfra.gate_neronUniqueExtension_fails_genericFibreOnly_three' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms NeronModelInfra.gate_neronUniqueExtension_fails_genericFibreOnly_three
