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

end SchwartzBruhat

end NumberField.AdelicFourier

end
