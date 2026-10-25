import Mathlib
import Lemma.Matrix.Any_EqComapAsIdealAsIdeal
import Def.NumberField_PlaceAbove
set_option autoImplicit false
open IsDedekindDomain NumberField


namespace NumberField.PlaceAbove

variable (E K : Type*) [Field E] [NumberField E] [Field K] [Algebra E K]


theorem comap_above (v : HeightOneSpectrum (𝓞 E)) :
    (above E K v).asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal :=
  (Matrix.Any_EqComapAsIdealAsIdeal (E := E) (K := K) v).choose_spec

end NumberField.PlaceAbove
