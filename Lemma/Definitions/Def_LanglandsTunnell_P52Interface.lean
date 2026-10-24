import Lemma.Definitions.Def_AutomorphicForm_HeckeEigensystem
import Lemma.Definitions.Def_AutomorphicForm_FormalBaseChange
import Lemma.Definitions.Def_ModularForm_EisensteinChiNegThree

set_option autoImplicit false

namespace LanglandsTunnell

open NumberField AutomorphicForm IsDedekindDomain

noncomputable def chiNegThreeWeight : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ) → ℤ√(-2) :=
  fun v =>
    ((EisensteinWeightOne.chiNegThree
      ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)) v : ℕ) : ℤ) : ℤ√(-2))

def P52InterfaceRow (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (Φ : HeckeEigensystem ℚ (ℤ√(-2))) (ΦK : HeckeEigensystem K (ℤ√(-2))) : Prop :=
  ∃ i : Fin 2,
    HeckeEigensystem.AgreesAwayFromFinite
      (formalBaseChange ℚ K (if i = 0 then Φ else Φ.twist chiNegThreeWeight)) ΦK

theorem p52InterfaceRow_self (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (Φ : HeckeEigensystem ℚ (ℤ√(-2))) :
    P52InterfaceRow K Φ (formalBaseChange ℚ K Φ) :=
  ⟨0, ∅, fun _ _ => by simp⟩

end LanglandsTunnell
