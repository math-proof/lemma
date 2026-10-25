import Lemma.AutomorphicForm.WhittakerModelLocal
import Def.AutomorphicForm_WhittakerModelMultiplicityOne

set_option autoImplicit false

open NumberField IsDedekindDomain

namespace AutomorphicForm.WhittakerModel

variable (F : Type) [Field F] [NumberField F]


variable {F}

theorem hasMultiplicityOneAt_zero (pins : CarrierPins F) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (v : HeightOneSpectrum (𝓞 F)) (ψv : AddChar (v.adicCompletion F) ℂ) :
    HasMultiplicityOneAt F pins ψ (fun _ => (0 : ℂ)) v ψv := by
  intro ℓ _
  refine ⟨0, fun W hW => ?_⟩
  rw [localSpaceAt_zero, Submodule.mem_bot] at hW
  subst hW
  rw [map_zero, Pi.zero_apply, mul_zero]

theorem hasArchMultiplicityOneAt_zero (pins : CarrierPins F) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (w : InfinitePlace F) (ψw : AddChar w.Completion ℂ) :
    HasArchMultiplicityOneAt F pins ψ (fun _ => (0 : ℂ)) w ψw := by
  intro ℓ _ _
  refine ⟨0, fun W hW => ?_⟩
  rw [archSpaceAt_zero, Submodule.mem_bot] at hW
  subst hW
  rw [map_zero, Pi.zero_apply, mul_zero]

end AutomorphicForm.WhittakerModel
