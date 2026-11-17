import Mathlib
import Lemma.Rep.RepPi
import Def.NumberField_PlaceAbove
import Instance.NumberField_PlaceDecompositionAction
import Abbrev.NumberField_FiniteSIdeleModule

set_option autoImplicit false

open IsDedekindDomain NumberField CategoryTheory
open scoped NumberField.PlaceDecomp

namespace NumberField.FiniteSIdele

variable (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]


section local_modules


noncomputable def integerUnitsToUnits (v : HeightOneSpectrum (𝓞 E)) : localIntegerUnits E K v ⟶ localUnits E K v :=
  Rep.ofHom ⟨(Units.map ((NumberField.PlaceAbove.above E K v).adicCompletionIntegers K).subtype.toMonoidHom).toAdditive.toIntLinearMap,
    fun _ => rfl⟩

end local_modules


end NumberField.FiniteSIdele
