/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/PartialDedekindZeta.lean -/

import Mathlib.NumberTheory.NumberField.DedekindZeta

/-!
# Partial Dedekind zeta functions

This file defines the Euler product over a selected set of prime ideals of a number field.
-/

namespace NumberField

variable (K : Type*) [Field K] [NumberField K]

/-- The partial Dedekind zeta function associated to a set `S` of prime ideals of `K`.

It is the Euler product `∏ 𝔭 ∈ S, (1 - N(𝔭) ^ (-s))⁻¹`. As usual for `tprod`, this
definition is meaningful without a convergence hypothesis; analytic results should state the
required convergence region explicitly. -/
noncomputable def partialDedekindZeta
    (S : Set (IsDedekindDomain.HeightOneSpectrum (RingOfIntegers K))) : ℂ → ℂ :=
  fun s ↦ ∏' (𝔭 : S), (1 - (Ideal.absNorm 𝔭.1.asIdeal : ℂ) ^ (-s))⁻¹

@[simp]
theorem partialDedekindZeta_empty (s : ℂ) :
    partialDedekindZeta K ∅ s = 1 := by
  simp [partialDedekindZeta]

@[simp]
theorem partialDedekindZeta_singleton
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (RingOfIntegers K)) (s : ℂ) :
    partialDedekindZeta K {𝔭} s =
      (1 - (Ideal.absNorm 𝔭.asIdeal : ℂ) ^ (-s))⁻¹ := by
  simp [partialDedekindZeta]

end NumberField
