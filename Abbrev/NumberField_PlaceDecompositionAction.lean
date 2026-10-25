import Mathlib

set_option autoImplicit false

open IsDedekindDomain NumberField
open scoped Pointwise

namespace NumberField.PlaceDecomp

section general
variable {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

end general

variable (E K : Type*) [Field E] [Field K] [NumberField K] [Algebra E K] (w : HeightOneSpectrum (𝓞 K))

noncomputable abbrev decomp : Subgroup (K ≃ₐ[E] K) := ((w.valuation K).valuationSubring).decompositionSubgroup E

variable {E K w}

section integers

end integers

end NumberField.PlaceDecomp
