import Mathlib
import sympy.Basic
open MeasureTheory Measure Set


/--
[radon_nikodym_withDensity](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/RadonNikodym.lean)
-/
@[path]
lemma radon_nikodym_withDensity
  {𝓕 : MeasurableSpace Ω}
  {μ ν : Measure Ω}
  [HaveLebesgueDecomposition ν μ]
-- given
  (hac : ν ≪ μ) :
-- imply
  μ.withDensity (ν.rnDeriv μ) = ν :=
-- proof
  Measure.withDensity_rnDeriv_eq ν μ hac

/--
[radon_nikodym_setLIntegral'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/RadonNikodym.lean)
-/
@[path]
lemma radon_nikodym_setLIntegral'
  {𝓕 : MeasurableSpace Ω}
  {μ ν : Measure Ω}
  [HaveLebesgueDecomposition ν μ]
  [SFinite μ]
  {A : Set Ω}
-- given
  (hac : ν ≪ μ) :
-- imply
  ∫⁻ x in A, ν.rnDeriv μ x ∂μ = ν A :=
-- proof
  Measure.setLIntegral_rnDeriv hac A


-- created on 2026-10-23
