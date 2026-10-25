import Mathlib
import Def.AutomorphicForm_HeckeEigensystem
import Def.AutomorphicForm_FormalBaseChange
import Structure.AutomorphicForm_FormalBaseChange

open IsDedekindDomain NumberField AutomorphicForm

noncomputable section

namespace AutomorphicForm

section FormalLift

variable (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K]
  [Algebra (𝓞 F) (𝓞 K)] [Algebra.IsIntegral (𝓞 F) (𝓞 K)]
  {R : Type*} [CommRing R]


@[simp] theorem formalBaseChange_a (π : HeckeEigensystem F R)
    (𝔓 : HeightOneSpectrum (𝓞 K)) :
    (formalBaseChange F K π).a 𝔓 =
      satakePow ((𝔓.under (𝓞 F)).asIdeal.inertiaDeg' 𝔓.asIdeal)
        (π.a (𝔓.under (𝓞 F))) (π.b (𝔓.under (𝓞 F))) := rfl

@[simp] theorem formalBaseChange_b (π : HeckeEigensystem F R)
    (𝔓 : HeightOneSpectrum (𝓞 K)) :
    (formalBaseChange F K π).b 𝔓 =
      (π.b (𝔓.under (𝓞 F))) ^ ((𝔓.under (𝓞 F)).asIdeal.inertiaDeg' 𝔓.asIdeal) := rfl

end FormalLift


section Package

variable (R : Type*) [CommRing R]
  (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K]
  [Algebra (𝓞 F) (𝓞 K)] [Algebra.IsIntegral (𝓞 F) (𝓞 K)]


end Package

end AutomorphicForm

end
