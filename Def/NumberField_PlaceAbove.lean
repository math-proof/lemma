import Mathlib
import Lemma.Matrix.Any_EqComapAsIdealAsIdeal

set_option autoImplicit false
open IsDedekindDomain NumberField


namespace NumberField.PlaceAbove

variable (E K : Type*) [Field E] [NumberField E] [Field K] [Algebra E K]

noncomputable def above (v : HeightOneSpectrum (𝓞 E)) : HeightOneSpectrum (𝓞 K) :=
  (Matrix.Any_EqComapAsIdealAsIdeal (E := E) (K := K) v).choose

end NumberField.PlaceAbove
