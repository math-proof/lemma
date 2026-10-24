import Lemma.Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Lemma.Definitions.Def_AdelicDock_LocalEmbedding
import Lemma.Definitions.Def_NumberField_SiegelVolume

set_option autoImplicit false

open NumberField IsDedekindDomain

namespace AutomorphicForm.WhittakerModel

variable (F : Type) [Field F] [NumberField F]

noncomputable def localFnAt (pins : CarrierPins F) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (v : HeightOneSpectrum (𝓞 F)) (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    GL (Fin 2) (v.adicCompletion F) → ℂ :=
  fun g => whittakerCoefficient F pins ψ φ 1
    (AdelicDock.finEmbed (𝓞 F) F (AdelicDock.localEmbed (𝓞 F) F v g))

noncomputable def localSpaceAt (pins : CarrierPins F) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (v : HeightOneSpectrum (𝓞 F)) (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    Submodule ℂ (GL (Fin 2) (v.adicCompletion F) → ℂ) :=
  Submodule.span ℂ
    {W | ∃ h : AdelicGL2 (𝓞 F) F, W = localFnAt F pins ψ v (fun x => φ (x * h))}

noncomputable def archFnAt (pins : CarrierPins F) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (w : InfinitePlace F) (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    GL (Fin 2) w.Completion → ℂ :=
  fun g => whittakerCoefficient F pins ψ φ 1 (NumberField.SiegelVolume.archEmbed F w g)

noncomputable def archSpaceAt (pins : CarrierPins F) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (w : InfinitePlace F) (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    Submodule ℂ (GL (Fin 2) w.Completion → ℂ) :=
  Submodule.span ℂ
    {W | ∃ h : AdelicGL2 (𝓞 F) F, W = archFnAt F pins ψ w (fun x => φ (x * h))}

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
