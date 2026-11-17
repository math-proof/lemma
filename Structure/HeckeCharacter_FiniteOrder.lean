module

public import Structure.AutomorphicForm_AdelicLsXi
public import Def.HeckeCharacter_FiniteOrder

set_option autoImplicit false

open NumberField AutomorphicForm IsDedekindDomain WithZero

public noncomputable section

namespace HeckeCharacter

variable (K : Type*) [Field K] [NumberField K]

structure IsFiniteOrderHeckeChar (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) : Prop where
  isIdeleClassChar : IsIdeleClassChar (𝓞 K) K χ
  continuous : Continuous χ
  isOfFinOrder : IsOfFinOrder χ

end HeckeCharacter

end
