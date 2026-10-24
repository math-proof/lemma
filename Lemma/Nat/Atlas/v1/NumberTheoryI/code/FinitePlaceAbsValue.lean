import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.NumberTheoryI.code.FinitePlaceAbsValue
open NumberField IsDedekindDomain FinitePlace


/--
[toAbsoluteValue_isNontrivial](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/FinitePlaceAbsValue.lean)
-/
@[path]
private lemma toAbsoluteValue_isNontrivial_eq
  [Field K]
  [NumberField K]
  {v : HeightOneSpectrum (𝓞 K)} :
-- imply
  (toAbsoluteValue v).IsNontrivial := by
-- proof
  apply FinitePlace.toAbsoluteValue_isNontrivial v

/--
[toAbsoluteValue_pairwise_inequiv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/FinitePlaceAbsValue.lean)
-/
@[path]
private lemma toAbsoluteValue_pairwise_inequiv_eq
  [Field K]
  [NumberField K]
  {v₁ v₂ : HeightOneSpectrum (𝓞 K)}
-- given
  (h : v₁ ≠ v₂) :
-- imply
  ¬ (toAbsoluteValue v₁).IsEquiv (toAbsoluteValue v₂) := by
-- proof
  apply FinitePlace.toAbsoluteValue_pairwise_inequiv v₁ v₂ h


-- created on 2026-10-23
