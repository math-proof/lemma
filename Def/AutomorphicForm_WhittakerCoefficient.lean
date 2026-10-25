import Lemma.AutomorphicForm.CarrierPins
import Def.AutomorphicForm_ConstantTerm

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory
open AutomorphicForm

noncomputable section

namespace AutomorphicForm

variable (F : Type) [Field F] [NumberField F]

def IsPrincipalInvariantAddChar (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) : Prop :=
  ∀ α : F, ψ (algebraMap F (AdeleRing (𝓞 F) F) α) = 1


def whittakerCoefficient (pins : CarrierPins F) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (α : F) (g : AdelicGL2 (𝓞 F) F) : ℂ :=
  letI := pins.nS
  ∫ x, φ (unipotentGL2 x * g) * ψ (-(algebraMap F (AdeleRing (𝓞 F) F) α * x)) ∂pins.ν

def WhittakerCoefficientIntegrable (pins : CarrierPins F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ) (α : F)
    (g : AdelicGL2 (𝓞 F) F) : Prop :=
  letI := pins.nS
  Integrable
    (fun x => φ (unipotentGL2 x * g) * ψ (-(algebraMap F (AdeleRing (𝓞 F) F) α * x))) pins.ν

end AutomorphicForm

end
