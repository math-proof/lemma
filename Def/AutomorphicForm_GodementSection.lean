import Def.NumberField_AdelicFourier
import Def.NumberField_TateGlobalZeta
import Def.AutomorphicForm_EtaFamily

open NumberField IsDedekindDomain MeasureTheory
open scoped SchwartzMap

noncomputable section

namespace NumberField.AdelicFourier

variable (F : Type*) [Field F] [NumberField F]

open scoped Classical in

def pureTensorSet2 : Set ((Fin 2 → AdeleRing (𝓞 F) F) → ℂ) :=
  {Φ | ∃ (g : 𝓢((Fin 2 → mixedEmbedding.mixedSpace F), ℂ)) (h : (Fin 2 → FiniteAdeleRing (𝓞 F) F) → ℂ),
      IsLocallyConstant h ∧ HasCompactSupport h ∧
      Φ = fun x => g (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1) * h (fun i => (x i).2)}

def schwartzBruhat2 : Submodule ℂ ((Fin 2 → AdeleRing (𝓞 F) F) → ℂ) :=
  Submodule.span ℂ (pureTensorSet2 F)

variable {F}

def pairHaar [MeasurableSpace (AdeleRing (𝓞 F) F)] (μ₁ : Measure (AdeleRing (𝓞 F) F)) :
    Measure (Fin 2 → AdeleRing (𝓞 F) F) :=
  Measure.pi fun _ : Fin 2 => μ₁

def pairChar (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) : AddChar (Fin 2 → AdeleRing (𝓞 F) F) ℂ :=
  ψ.compAddMonoidHom
    (Pi.evalAddMonoidHom (fun _ : Fin 2 => AdeleRing (𝓞 F) F) 0
      + Pi.evalAddMonoidHom (fun _ : Fin 2 => AdeleRing (𝓞 F) F) 1)


def fourierTransform2 [MeasurableSpace (AdeleRing (𝓞 F) F)] (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (μ₁ : Measure (AdeleRing (𝓞 F) F)) (Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ) :
    (Fin 2 → AdeleRing (𝓞 F) F) → ℂ :=
  fourierIntegral (pairChar ψ) (pairHaar μ₁) Φ

def reflectPair [MeasurableSpace (AdeleRing (𝓞 F) F)] (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (μ₁ : Measure (AdeleRing (𝓞 F) F)) (Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ)
    (x : Fin 2 → AdeleRing (𝓞 F) F) : ℂ :=
  fourierTransform2 ψ μ₁ Φ ![x 1, -x 0]

end NumberField.AdelicFourier

namespace AutomorphicForm

variable (F : Type) [Field F] [NumberField F]

def bottomRowVec (g : AdelicGL2 (𝓞 F) F) (t : AdeleRing (𝓞 F) F) : Fin 2 → AdeleRing (𝓞 F) F :=
  fun j => t * (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 j

def godementSection {mI : MeasurableSpace (AdeleRing (𝓞 F) F)ˣ} (ν₀ : Measure (AdeleRing (𝓞 F) F)ˣ)
    (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ)
    (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) (Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ) (s : ℂ)
    (g : AdelicGL2 (𝓞 F) F) : ℂ :=
  ((μ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)
    * ((cpowChar α hα (s + 1 / 2) (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)
    * NumberField.TateGlobal.zetaIntegral ν₀ (fun t => Φ (bottomRowVec F g t)) (μ * ν⁻¹) (2 * s + 1)

end AutomorphicForm

end
