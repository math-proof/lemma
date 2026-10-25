import Def.AutomorphicForm_SmoothAutomorphicFnAt

open IsDedekindDomain NumberField MeasureTheory Matrix
open AutomorphicForm FLT.SmoothVectors

noncomputable section

namespace AutomorphicForm

variable (F : Type) [Field F] [NumberField F]

def fnTwist (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    AdelicGL2 (𝓞 F) F → ℂ :=
  fun g => chiDet (𝓞 F) F η g * φ g


def twistedCentralChar (Z : Subgroup (AdeleRing (𝓞 F) F)ˣ) (ξ : Z →* ℂˣ)
    (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) : Z →* ℂˣ :=
  ξ * (η.comp Z.subtype) ^ 2

end AutomorphicForm

end
