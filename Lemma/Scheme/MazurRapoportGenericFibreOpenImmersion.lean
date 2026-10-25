import Mathlib
import Lemma.AlgebraicGeometry.NeronModelPropertyBundleCarrier

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace NeronModelInfra

section RingSide

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]

theorem isLocalizationAway_of_irreducible {ϖ : R} (hϖ : Irreducible ϖ) :
    IsLocalization.Away ϖ K := by
  refine (IsLocalization.iff_of_le_of_exists_dvd (M := Submonoid.powers ϖ)
      (nonZeroDivisors R) ?_ ?_).mpr inferInstance
  · intro x hx
    obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff x ϖ).mp hx
    exact mem_nonZeroDivisors_of_ne_zero (pow_ne_zero n hϖ.ne_zero)
  · intro r hr
    obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible
      (nonZeroDivisors.ne_zero hr) hϖ
    exact ⟨ϖ ^ n, (Submonoid.mem_powers_iff _ ϖ).mpr ⟨n, rfl⟩, hn.dvd⟩


theorem isLocalizationAway_uniformizer_three :
    IsLocalization.Away (3 : ℤ_[3]) ℚ_[3] := by
  simpa using isLocalizationAway_uniformizer_zp 3

end RingSide

section SchemeSide

variable (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable [Field K] [Algebra R K] [IsFractionRing R K]


theorem range_specGenericFibreInclusion_eq_basicOpen {ϖ : R} (hϖ : Irreducible ϖ) :
    Set.range (specGenericFibreInclusion R K).base =
      (PrimeSpectrum.basicOpen ϖ : Set (PrimeSpectrum R)) := by
  haveI : IsLocalization.Away ϖ K := isLocalizationAway_of_irreducible K hϖ
  have h := PrimeSpectrum.localization_away_comap_range K ϖ
  rw [specGenericFibreInclusion_eq]
  exact h

theorem mono_specGenericFibreInclusion_of_dvr :
    Mono (specGenericFibreInclusion R K) :=
  inferInstance

theorem flat_specGenericFibreInclusion_of_dvr :
    Flat (specGenericFibreInclusion R K) :=
  inferInstance

end SchemeSide

section PadicGates

theorem gate_isOpenImmersion_specGenericFibreInclusion_zp (p : ℕ) [Fact p.Prime] :
    IsOpenImmersion (specGenericFibreInclusion ℤ_[p] ℚ_[p]) :=
  isOpenImmersion_specGenericFibreInclusion ℤ_[p] ℚ_[p]

theorem gate_isOpenImmersion_specGenericFibreInclusion_three :
    IsOpenImmersion (specGenericFibreInclusion ℤ_[3] ℚ_[3]) :=
  gate_isOpenImmersion_specGenericFibreInclusion_zp 3

theorem not_isIso_specGenericFibreInclusion_zp (p : ℕ) [Fact p.Prime] :
    ¬ IsIso (specGenericFibreInclusion ℤ_[p] ℚ_[p]) := by
  intro h
  exact (isEmpty_schemeHomOver_id_specGenericFibreInclusion_zp p).false
    ⟨inv (specGenericFibreInclusion ℤ_[p] ℚ_[p]),
      IsIso.inv_hom_id (specGenericFibreInclusion ℤ_[p] ℚ_[p])⟩

theorem not_isIso_specGenericFibreInclusion_three :
    ¬ IsIso (specGenericFibreInclusion ℤ_[3] ℚ_[3]) :=
  not_isIso_specGenericFibreInclusion_zp 3

theorem gate_strictOpenImmersion_specGenericFibreInclusion_zp (p : ℕ) [Fact p.Prime] :
    IsOpenImmersion (specGenericFibreInclusion ℤ_[p] ℚ_[p]) ∧
      ¬ IsIso (specGenericFibreInclusion ℤ_[p] ℚ_[p]) :=
  ⟨gate_isOpenImmersion_specGenericFibreInclusion_zp p,
    not_isIso_specGenericFibreInclusion_zp p⟩

theorem gate_strictOpenImmersion_specGenericFibreInclusion_three :
    IsOpenImmersion (specGenericFibreInclusion ℤ_[3] ℚ_[3]) ∧
      ¬ IsIso (specGenericFibreInclusion ℤ_[3] ℚ_[3]) :=
  gate_strictOpenImmersion_specGenericFibreInclusion_zp 3

end PadicGates

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
