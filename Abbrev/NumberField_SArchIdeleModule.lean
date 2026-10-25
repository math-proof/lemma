import Mathlib
import Abbrev.NumberField_SIdeleModule

set_option autoImplicit false

open IsDedekindDomain NumberField CategoryTheory
open scoped NumberField.PlaceDecomp NumberField.InfPlaceDecomp

namespace NumberField.SArchIdele

variable (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]
variable (S : Finset (HeightOneSpectrum (𝓞 E)))

abbrev Index : Type := {v // v ∈ S} ⊕ InfinitePlace E

end NumberField.SArchIdele
