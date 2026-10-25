import Mathlib
import Def.NumberField_PlaceAbove
import Instance.NumberField_PlaceDecompositionAction

set_option autoImplicit false

open IsDedekindDomain NumberField CategoryTheory
open scoped NumberField.PlaceDecomp

namespace NumberField.SUnits

variable (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]

section diag
variable (S : Finset (HeightOneSpectrum (𝓞 E)))

noncomputable abbrev loc (v : HeightOneSpectrum (𝓞 E)) : K →+* (NumberField.PlaceAbove.above E K v).adicCompletion K :=
  algebraMap K _

end diag

end NumberField.SUnits
