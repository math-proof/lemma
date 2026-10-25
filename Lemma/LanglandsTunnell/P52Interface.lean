import Def.AutomorphicForm_HeckeEigensystem
import Def.AutomorphicForm_FormalBaseChange
import Def.ModularForm_EisensteinChiNegThree
import Def.LanglandsTunnell_P52Interface

set_option autoImplicit false

namespace LanglandsTunnell

open NumberField AutomorphicForm IsDedekindDomain


theorem p52InterfaceRow_self (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (Φ : HeckeEigensystem ℚ (ℤ√(-2))) :
    P52InterfaceRow K Φ (formalBaseChange ℚ K Φ) :=
  ⟨0, ∅, fun _ _ => by simp⟩

end LanglandsTunnell
