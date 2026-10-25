import Def.AutomorphicForm_WhittakerCoefficient
import Lemma.AdelicDock.LocalEmbedding
import Lemma.NumberField.SiegelVolume

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

end AutomorphicForm.WhittakerModel
