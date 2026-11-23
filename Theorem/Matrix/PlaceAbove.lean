module

public import Mathlib
public import Theorem.Matrix.Any_EqComapAsIdealAsIdeal
public import Def.NumberField_PlaceAbove

public section

set_option autoImplicit false
open IsDedekindDomain NumberField Matrix
open NumberField.PlaceAbove

namespace Matrix.PlaceAbove

export NumberField.PlaceAbove (above)

variable (E K : Type*) [Field E] [NumberField E] [Field K] [Algebra E K]


public theorem comap_above (v : HeightOneSpectrum (𝓞 E)) :
    (above E K v).asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal :=
  (Matrix.Any_EqComapAsIdealAsIdeal (E := E) (K := K) v).choose_spec

end Matrix.PlaceAbove
