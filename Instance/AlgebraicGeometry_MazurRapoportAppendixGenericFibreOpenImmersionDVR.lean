-- Carved from Lemma/Definitions/Def_AlgebraicGeometry_MazurRapoportAppendixGenericFibreOpenImmersionDVR.lean: instance decls only.
import Mathlib
set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace NeronModelInfra

section RingSide

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]


instance isLocalizationAway_uniformizer_zp (p : ℕ) [Fact p.Prime] :
    IsLocalization.Away (p : ℤ_[p]) ℚ_[p] :=
  isLocalizationAway_of_irreducible ℚ_[p] (PadicInt.irreducible_p (p := p))


end RingSide

section SchemeSide

variable (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable [Field K] [Algebra R K] [IsFractionRing R K]

instance isOpenImmersion_specGenericFibreInclusion :
    IsOpenImmersion (specGenericFibreInclusion R K) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  haveI : IsLocalization.Away ϖ K := isLocalizationAway_of_irreducible K hϖ
  rw [specGenericFibreInclusion_eq]
  exact AlgebraicGeometry.IsOpenImmersion.of_isLocalization ϖ


end SchemeSide


end NeronModelInfra

/--
info: 'NeronModelInfra.isLocalizationAway_of_irreducible' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms NeronModelInfra.isLocalizationAway_of_irreducible

/--
info: 'NeronModelInfra.isLocalizationAway_uniformizer_zp' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms NeronModelInfra.isLocalizationAway_uniformizer_zp

/--
info: 'NeronModelInfra.isLocalizationAway_uniformizer_three' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms NeronModelInfra.isLocalizationAway_uniformizer_three

/--
info: 'NeronModelInfra.isOpenImmersion_specGenericFibreInclusion' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms NeronModelInfra.isOpenImmersion_specGenericFibreInclusion

/--
info: 'NeronModelInfra.range_specGenericFibreInclusion_eq_basicOpen' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms NeronModelInfra.range_specGenericFibreInclusion_eq_basicOpen

/--
info: 'NeronModelInfra.mono_specGenericFibreInclusion_of_dvr' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms NeronModelInfra.mono_specGenericFibreInclusion_of_dvr

/--
info: 'NeronModelInfra.flat_specGenericFibreInclusion_of_dvr' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms NeronModelInfra.flat_specGenericFibreInclusion_of_dvr

/--
info: 'NeronModelInfra.gate_isOpenImmersion_specGenericFibreInclusion_zp' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms NeronModelInfra.gate_isOpenImmersion_specGenericFibreInclusion_zp

/--
info: 'NeronModelInfra.gate_isOpenImmersion_specGenericFibreInclusion_three' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms NeronModelInfra.gate_isOpenImmersion_specGenericFibreInclusion_three

/--
info: 'NeronModelInfra.not_isIso_specGenericFibreInclusion_zp' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms NeronModelInfra.not_isIso_specGenericFibreInclusion_zp

/--
info: 'NeronModelInfra.not_isIso_specGenericFibreInclusion_three' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms NeronModelInfra.not_isIso_specGenericFibreInclusion_three

/--
info: 'NeronModelInfra.gate_strictOpenImmersion_specGenericFibreInclusion_zp' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms NeronModelInfra.gate_strictOpenImmersion_specGenericFibreInclusion_zp

/--
info: 'NeronModelInfra.gate_strictOpenImmersion_specGenericFibreInclusion_three' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms NeronModelInfra.gate_strictOpenImmersion_specGenericFibreInclusion_three

end
