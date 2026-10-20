import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.NumberField.PolarDensity
open Filter Topology NumberField IsDedekindDomain
open NumberField.Set


/--
[HasPolarDensity.unique](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/PolarDensity.lean)
-/
@[path]
private lemma HasPolarDensity_unique_eq
  [Field K] [NumberField K]
  {S : Set (HeightOneSpectrum (𝓞 K))}
  {ρ₁ ρ₂ : ℚ}
-- given
  (h₁ : S.HasPolarDensity ρ₁)
  (h₂ : S.HasPolarDensity ρ₂) :
-- imply
  ρ₁ = ρ₂ := by
-- proof
  apply NumberField.Set.HasPolarDensity.unique h₁ h₂

/--
[hasPolarDensity_empty](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/PolarDensity.lean)
-/
@[path]
private lemma hasPolarDensity_empty_eq
  [Field K] [NumberField K] :
-- imply
  (∅ : Set (HeightOneSpectrum (𝓞 K))).HasPolarDensity 0 := by
-- proof
  apply NumberField.Set.hasPolarDensity_empty K


-- created on 2026-10-20
