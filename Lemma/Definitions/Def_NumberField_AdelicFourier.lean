import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Fourier.FourierTransform

open NumberField IsDedekindDomain MeasureTheory
open scoped SchwartzMap

noncomputable section

namespace NumberField.AdelicFourier

section Fourier

variable {A : Type*} [CommRing A] [MeasurableSpace A]

def fourierIntegral (ψ : AddChar A ℂ) (μ : Measure A) (f : A → ℂ) (w : A) : ℂ :=
  ∫ v, ψ (-(v * w)) * f v ∂μ

theorem fourierIntegral_def (ψ : AddChar A ℂ) (μ : Measure A) (f : A → ℂ) (w : A) :
    fourierIntegral ψ μ f w = ∫ v, ψ (-(v * w)) * f v ∂μ :=
  rfl

theorem fourierIntegral_compAddChar (e : AddChar A Circle) (μ : Measure A) (f : A → ℂ) :
    fourierIntegral (Circle.coeHom.compAddChar e) μ f = Fourier.fourierIntegral e μ f := by
  funext w
  simp only [fourierIntegral, Fourier.fourierIntegral_def, Circle.smul_def, smul_eq_mul]
  rfl

theorem fourierIntegral_zero (ψ : AddChar A ℂ) (μ : Measure A) :
    fourierIntegral ψ μ 0 = 0 := by
  funext w
  simp only [fourierIntegral, Pi.zero_apply, mul_zero, integral_zero]

theorem fourierIntegral_smul (ψ : AddChar A ℂ) (μ : Measure A) (c : ℂ) (f : A → ℂ) :
    fourierIntegral ψ μ (c • f) = c • fourierIntegral ψ μ f := by
  funext w
  simp only [fourierIntegral, Pi.smul_apply, smul_eq_mul, ← integral_const_mul]
  congr 1 with v
  ring

theorem fourierIntegral_add (ψ : AddChar A ℂ) (μ : Measure A) {f g : A → ℂ} (w : A)
    (hf : Integrable (fun v => ψ (-(v * w)) * f v) μ)
    (hg : Integrable (fun v => ψ (-(v * w)) * g v) μ) :
    fourierIntegral ψ μ (f + g) w = fourierIntegral ψ μ f w + fourierIntegral ψ μ g w := by
  simp only [fourierIntegral, Pi.add_apply, mul_add]
  exact integral_add hf hg

theorem norm_fourierIntegral_le_integral_norm (ψ : AddChar A ℂ) (μ : Measure A) (f : A → ℂ)
    (w : A) : ‖fourierIntegral ψ μ f w‖ ≤ ∫ v, ‖ψ (-(v * w)) * f v‖ ∂μ :=
  norm_integral_le_integral_norm _

theorem fourierIntegral_comp_add_right [MeasurableAdd A] (ψ : AddChar A ℂ) (μ : Measure A)
    [μ.IsAddRightInvariant] (f : A → ℂ) (v₀ : A) :
    fourierIntegral ψ μ (f ∘ fun v => v + v₀) = fun w => ψ (v₀ * w) * fourierIntegral ψ μ f w := by
  funext w
  simp only [fourierIntegral, Function.comp_apply]
  have h : (fun v => ψ (-(v * w)) * f (v + v₀))
      = fun v => (fun u => ψ (-((u - v₀) * w)) * f u) (v + v₀) := by
    funext v
    simp only [add_sub_cancel_right]
  rw [h, integral_add_right_eq_self (fun u => ψ (-((u - v₀) * w)) * f u) v₀, ← integral_const_mul]
  congr 1 with u
  rw [← mul_assoc, ← AddChar.map_add_eq_mul]
  congr 2
  ring

end Fourier

section SchwartzBruhat

variable (F : Type*) [Field F] [NumberField F]

open scoped Classical in

def pureTensorSet : Set (AdeleRing (𝓞 F) F → ℂ) :=
  {f | ∃ (g : 𝓢(mixedEmbedding.mixedSpace F, ℂ)) (h : FiniteAdeleRing (𝓞 F) F → ℂ),
      IsLocallyConstant h ∧ HasCompactSupport h ∧
      f = fun x => g (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1) * h x.2}

def schwartzBruhat : Submodule ℂ (AdeleRing (𝓞 F) F → ℂ) :=
  Submodule.span ℂ (pureTensorSet F)

variable {F}

open scoped Classical in
theorem tensor_mem_pureTensorSet (g : 𝓢(mixedEmbedding.mixedSpace F, ℂ))
    (h : FiniteAdeleRing (𝓞 F) F → ℂ) (hlc : IsLocallyConstant h) (hcs : HasCompactSupport h) :
    (fun x : AdeleRing (𝓞 F) F => g (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1) * h x.2)
      ∈ pureTensorSet F :=
  ⟨g, h, hlc, hcs, rfl⟩

theorem mem_schwartzBruhat_of_mem_pureTensorSet {f : AdeleRing (𝓞 F) F → ℂ}
    (hf : f ∈ pureTensorSet F) : f ∈ schwartzBruhat F :=
  Submodule.subset_span hf

theorem zero_mem_pureTensorSet : (0 : AdeleRing (𝓞 F) F → ℂ) ∈ pureTensorSet F :=
  ⟨0, 0, IsLocallyConstant.const 0, HasCompactSupport.zero, by funext x; simp⟩

theorem zero_mem_schwartzBruhat : (0 : AdeleRing (𝓞 F) F → ℂ) ∈ schwartzBruhat F :=
  Submodule.zero_mem _

theorem schwartzBruhat_induction {p : (f : AdeleRing (𝓞 F) F → ℂ) → f ∈ schwartzBruhat F → Prop}
    (tensor : ∀ (f) (hf : f ∈ pureTensorSet F), p f (mem_schwartzBruhat_of_mem_pureTensorSet hf))
    (zero : p 0 zero_mem_schwartzBruhat)
    (add : ∀ f g (hf : f ∈ schwartzBruhat F) (hg : g ∈ schwartzBruhat F),
      p f hf → p g hg → p (f + g) (Submodule.add_mem _ hf hg))
    (smul : ∀ (c : ℂ) f (hf : f ∈ schwartzBruhat F), p f hf → p (c • f) (Submodule.smul_mem _ c hf))
    {f : AdeleRing (𝓞 F) F → ℂ} (hf : f ∈ schwartzBruhat F) : p f hf :=
  Submodule.span_induction tensor zero add smul hf

end SchwartzBruhat

end NumberField.AdelicFourier

end
