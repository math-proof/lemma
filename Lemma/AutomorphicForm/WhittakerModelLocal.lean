import Lemma.AutomorphicForm.WhittakerCoefficient
import Lemma.AdelicDock.LocalEmbedding
import Lemma.NumberField.SiegelVolume
import Def.AutomorphicForm_WhittakerModelLocal

set_option autoImplicit false

open NumberField IsDedekindDomain

namespace AutomorphicForm.WhittakerModel

variable (F : Type) [Field F] [NumberField F]


variable {F}

@[simp] theorem localFnAt_zero (pins : CarrierPins F) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (v : HeightOneSpectrum (𝓞 F)) :
    localFnAt F pins ψ v (fun _ => (0 : ℂ)) = fun _ => 0 :=
  funext fun _ => by simp only [localFnAt, whittakerCoefficient_zero]

@[simp] theorem archFnAt_zero (pins : CarrierPins F) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (w : InfinitePlace F) :
    archFnAt F pins ψ w (fun _ => (0 : ℂ)) = fun _ => 0 :=
  funext fun _ => by simp only [archFnAt, whittakerCoefficient_zero]

theorem localSpaceAt_zero (pins : CarrierPins F) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (v : HeightOneSpectrum (𝓞 F)) :
    localSpaceAt F pins ψ v (fun _ => (0 : ℂ)) = ⊥ := by
  refine Submodule.span_eq_bot.2 ?_
  rintro W ⟨h, rfl⟩
  funext g
  simp only [localFnAt, whittakerCoefficient_zero, Pi.zero_apply]

theorem archSpaceAt_zero (pins : CarrierPins F) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (w : InfinitePlace F) :
    archSpaceAt F pins ψ w (fun _ => (0 : ℂ)) = ⊥ := by
  refine Submodule.span_eq_bot.2 ?_
  rintro W ⟨h, rfl⟩
  funext g
  simp only [archFnAt, whittakerCoefficient_zero, Pi.zero_apply]

end AutomorphicForm.WhittakerModel
