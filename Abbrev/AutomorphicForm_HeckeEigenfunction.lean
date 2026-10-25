import Structure.AutomorphicForm_CarrierPins
import Structure.AutomorphicForm_HeckeEigensystem
import Structure.NumberField_AdelicLevel
import Instance.AbstractHeckeOperator
import Instance.AbstractHeckeOperator

set_option autoImplicit false

open IsDedekindDomain NumberField MulAction NumberField.AdelicLevel
open scoped Pointwise

noncomputable section

namespace AutomorphicForm

section Defs

variable (F : Type) [Field F] [NumberField F]

abbrev RightTranslationGroup : Type _ :=
  DomMulAct ((AdelicGL2 (𝓞 F) F)ᵐᵒᵖ)

end Defs

variable {F : Type} [Field F] [NumberField F]


end AutomorphicForm

end
