import Lemma.Definitions.Def_NumberField_AdelicFourier
import Lemma.Definitions.Def_NumberField_TateGlobalZeta
import Lemma.Definitions.Def_AutomorphicForm_EtaFamily

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

theorem pairChar_apply (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (v : Fin 2 → AdeleRing (𝓞 F) F) :
    pairChar ψ v = ψ (v 0 + v 1) := rfl

def fourierTransform2 [MeasurableSpace (AdeleRing (𝓞 F) F)] (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (μ₁ : Measure (AdeleRing (𝓞 F) F)) (Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ) :
    (Fin 2 → AdeleRing (𝓞 F) F) → ℂ :=
  fourierIntegral (pairChar ψ) (pairHaar μ₁) Φ

def reflectPair [MeasurableSpace (AdeleRing (𝓞 F) F)] (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (μ₁ : Measure (AdeleRing (𝓞 F) F)) (Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ)
    (x : Fin 2 → AdeleRing (𝓞 F) F) : ℂ :=
  fourierTransform2 ψ μ₁ Φ ![x 1, -x 0]

open scoped Classical in
theorem tensor_mem_pureTensorSet2 (g : 𝓢((Fin 2 → mixedEmbedding.mixedSpace F), ℂ))
    (h : (Fin 2 → FiniteAdeleRing (𝓞 F) F) → ℂ) (hlc : IsLocallyConstant h) (hcs : HasCompactSupport h) :
    (fun x : Fin 2 → AdeleRing (𝓞 F) F =>
        g (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1) * h (fun i => (x i).2))
      ∈ pureTensorSet2 F :=
  ⟨g, h, hlc, hcs, rfl⟩

theorem mem_schwartzBruhat2_of_mem_pureTensorSet2 {Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ}
    (hΦ : Φ ∈ pureTensorSet2 F) : Φ ∈ schwartzBruhat2 F :=
  Submodule.subset_span hΦ

theorem zero_mem_schwartzBruhat2 : (0 : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ) ∈ schwartzBruhat2 F :=
  Submodule.zero_mem _

theorem schwartzBruhat2_induction
    {p : (Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ) → Φ ∈ schwartzBruhat2 F → Prop}
    (tensor : ∀ (Φ) (hΦ : Φ ∈ pureTensorSet2 F), p Φ (mem_schwartzBruhat2_of_mem_pureTensorSet2 hΦ))
    (zero : p 0 zero_mem_schwartzBruhat2)
    (add : ∀ Φ Ψ (hΦ : Φ ∈ schwartzBruhat2 F) (hΨ : Ψ ∈ schwartzBruhat2 F),
      p Φ hΦ → p Ψ hΨ → p (Φ + Ψ) (Submodule.add_mem _ hΦ hΨ))
    (smul : ∀ (c : ℂ) Φ (hΦ : Φ ∈ schwartzBruhat2 F), p Φ hΦ → p (c • Φ) (Submodule.smul_mem _ c hΦ))
    {Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ} (hΦ : Φ ∈ schwartzBruhat2 F) : p Φ hΦ :=
  Submodule.span_induction tensor zero add smul hΦ

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
