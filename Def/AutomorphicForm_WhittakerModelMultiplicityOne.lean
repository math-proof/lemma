import Def.AutomorphicForm_WhittakerModelLocal

set_option autoImplicit false

open NumberField IsDedekindDomain

namespace AutomorphicForm.WhittakerModel

variable (F : Type) [Field F] [NumberField F]

def HasMultiplicityOneAt (pins : CarrierPins F) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (v : HeightOneSpectrum (𝓞 F))
    (ψv : AddChar (v.adicCompletion F) ℂ) : Prop :=
  ∀ ℓ : (GL (Fin 2) (v.adicCompletion F) → ℂ) →ₗ[ℂ] ℂ,
    (∀ W ∈ localSpaceAt F pins ψ v φ, ∀ x : v.adicCompletion F,
        ℓ (fun g => W (g * unipotentGL2 x)) = ψv x * ℓ W) →
      ∃ c : ℂ, ∀ W ∈ localSpaceAt F pins ψ v φ, ℓ W = c * W 1

def HasArchMultiplicityOneAt (pins : CarrierPins F) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (w : InfinitePlace F) (ψw : AddChar w.Completion ℂ) : Prop :=
  ∀ ℓ : (GL (Fin 2) w.Completion → ℂ) →ₗ[ℂ] ℂ,
    (∀ W ∈ archSpaceAt F pins ψ w φ, ∀ x : w.Completion,
        ℓ (fun g => W (g * unipotentGL2 x)) = ψw x * ℓ W) →
      (∀ (Wn : ℕ → (GL (Fin 2) w.Completion → ℂ)) (W₀ : GL (Fin 2) w.Completion → ℂ),
          (∀ n : ℕ, Wn n ∈ archSpaceAt F pins ψ w φ) → W₀ ∈ archSpaceAt F pins ψ w φ →
            (∀ K : Set (GL (Fin 2) w.Completion), IsCompact K →
              TendstoUniformlyOn Wn W₀ Filter.atTop K) →
              Filter.Tendsto (fun n => ℓ (Wn n)) Filter.atTop (nhds (ℓ W₀))) →
        ∃ c : ℂ, ∀ W ∈ archSpaceAt F pins ψ w φ, ℓ W = c * W 1

end AutomorphicForm.WhittakerModel
