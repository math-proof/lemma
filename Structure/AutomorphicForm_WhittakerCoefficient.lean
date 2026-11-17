module

public import Structure.AutomorphicForm_CarrierPins
public import Def.AutomorphicForm_ConstantTerm
public import Def.AutomorphicForm_WhittakerCoefficient

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory
open AutomorphicForm

public noncomputable section

namespace AutomorphicForm

variable (F : Type) [Field F] [NumberField F]


structure IsGlobalAddChar (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) : Prop where
  principalInvariant : IsPrincipalInvariantAddChar F ψ
  continuous : Continuous ψ
  nontrivial : ψ ≠ 1


end AutomorphicForm

end
