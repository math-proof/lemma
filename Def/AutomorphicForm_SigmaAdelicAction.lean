import Def.M4aHerbrand_IdeleClassVocab

set_option autoImplicit false

open IsDedekindDomain NumberField

noncomputable section

namespace AutomorphicForm

variable (F E : Type) [Field F] [Field E] [NumberField E] [Algebra F E]
variable (D : M4aHerbrand.IdeleGaloisDescent (𝓞 E) F E)

def sigmaAdelicAct (σ : E ≃ₐ[F] E) :
    Matrix.GeneralLinearGroup (Fin 2) (AdeleRing (𝓞 E) E) →*
      Matrix.GeneralLinearGroup (Fin 2) (AdeleRing (𝓞 E) E) :=
  Matrix.GeneralLinearGroup.map (D.act σ : RingAut (AdeleRing (𝓞 E) E)).toRingHom

def sigmaSectionActOn (σ : E ≃ₐ[F] E)
    (φ : Matrix.GeneralLinearGroup (Fin 2) (AdeleRing (𝓞 E) E) → ℂ) :
    Matrix.GeneralLinearGroup (Fin 2) (AdeleRing (𝓞 E) E) → ℂ :=
  φ ∘ (sigmaAdelicAct F E D σ)

def sigmaPairingOn
    [MeasurableSpace (Matrix.GeneralLinearGroup (Fin 2) (AdeleRing (𝓞 E) E))]
    (νK : MeasureTheory.Measure (Matrix.GeneralLinearGroup (Fin 2) (AdeleRing (𝓞 E) E)))
    (σ : E ≃ₐ[F] E)
    (φ : Matrix.GeneralLinearGroup (Fin 2) (AdeleRing (𝓞 E) E) → ℂ) : ℂ :=
  ∫ k, φ k * starRingEnd ℂ (sigmaSectionActOn F E D σ φ k) ∂νK

end AutomorphicForm

end
