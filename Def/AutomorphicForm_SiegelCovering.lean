import Def.AutomorphicForm_CentreCutSiegelSet
import Lemma.Matrix.SiegelReduction

open Matrix NumberField UpperHalfPlane
open scoped MatrixGroups Modular

noncomputable section

namespace AutomorphicForm

namespace SiegelCovering

open WindowedSiegel SiegelCoordinates


section Adelic

open NumberField.AdelicLevel NumberField.AdelicVolume IsDedekindDomain Set SiegelReduction

variable (F : Type) [Field F] [NumberField F]

def FiniteIntegralCovering : Prop :=
  ∀ g : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F), ∃ γ : GL (Fin 2) F,
    glFin (𝓞 F) F (globalPoints (𝓞 F) F γ) * g ∈ finiteIntegralGL2 (𝓞 F) F

def CoversModCentre (D : Set (AdelicGL2 (𝓞 F) F)) : Prop :=
  ∀ g : AdelicGL2 (𝓞 F) F, ∃ γ : GL (Fin 2) F, ∃ z : (AdeleRing (𝓞 F) F)ˣ,
    globalPoints (𝓞 F) F γ * g * centralScalar (𝓞 F) F z ∈ D

end Adelic

end SiegelCovering

end AutomorphicForm

end
