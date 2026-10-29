import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Mathlib.Topology.LocallyConstant.Basic

noncomputable section

open MeasureTheory
open scoped NNReal ENNReal

namespace LanglandsTunnell.TateLocal

section Modulus

variable {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K] [LocallyCompactSpace K]

def modulus (a : K) : NNReal := by
  classical exact if h : a = 0 then 0 else distribHaarChar K (Units.mk0 a h)

end Modulus

section TestFunctions

variable {K : Type*} [TopologicalSpace K]

def IsSchwartzBruhat (f : K → ℂ) : Prop :=
  IsLocallyConstant f ∧ HasCompactSupport f

end TestFunctions

section Fourier

variable {K : Type*} [Field K] [MeasurableSpace K]

def tateFourier (ψ : AddChar K ℂ) (μ : Measure K) (f : K → ℂ) (y : K) : ℂ :=
  ∫ x, f x * ψ (x * y) ∂μ

end Fourier

section Characters

variable {K : Type*} [Field K]

def charExt (χ : Kˣ →* ℂˣ) (x : K) : ℂ := by
  classical exact if h : x = 0 then 0 else (χ (Units.mk0 x h) : ℂ)

end Characters

section Zeta

variable {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K] [LocallyCompactSpace K]
  [MeasurableSpace K]

def mulMeasure (μ : Measure K) : Measure K :=
  (μ.restrict {0}ᶜ).withDensity fun x => ((modulus x : ENNReal))⁻¹

def localZeta (μ : Measure K) (f : K → ℂ) (χ : Kˣ →* ℂˣ) (s : ℂ) : ℂ :=
  ∫ x, f x * charExt χ x * ((modulus x : ℝ) : ℂ) ^ s ∂(mulMeasure μ)


def localGammaAt (μ : Measure K) (ψ : AddChar K ℂ) (f₀ : K → ℂ) (χ : Kˣ →* ℂˣ) (s : ℂ) : ℂ :=
  localZeta μ (tateFourier ψ μ f₀) χ⁻¹ (1 - s) / localZeta μ f₀ χ s

end Zeta

end LanglandsTunnell.TateLocal

end
