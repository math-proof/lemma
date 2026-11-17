module

public import Structure.AutomorphicForm_CarrierPins
public import Structure.AutomorphicForm_HeckeEigensystem
public import Structure.NumberField_AdelicLevel
public import Instance.AbstractHeckeOperator

set_option autoImplicit false

open IsDedekindDomain NumberField MulAction NumberField.AdelicLevel
open scoped Pointwise

@[expose] public noncomputable section

namespace AutomorphicForm

section Defs

variable (F : Type) [Field F] [NumberField F]

abbrev RightTranslationGroup : Type _ :=
  DomMulAct ((AdelicGL2 (𝓞 F) F)ᵐᵒᵖ)

end Defs

variable {F : Type} [Field F] [NumberField F]


end AutomorphicForm

end
