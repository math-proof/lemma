import Def.NumberField_AdelicFourier
import Def.NumberField_AdelicVolume

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicFourier NumberField.AdelicLevel NumberField.AdelicVolume
open AutomorphicForm IsDedekindDomain
open scoped NNReal

noncomputable section

namespace NumberField.TateGlobal

variable (F : Type) [Field F] [NumberField F]

def normOneIdeles : Subgroup (AdeleRing (𝓞 F) F)ˣ :=
  (distribHaarChar (AdeleRing (𝓞 F) F)).ker

def ideleNorm (x : (AdeleRing (𝓞 F) F)ˣ) : ℝ :=
  ((distribHaarChar (AdeleRing (𝓞 F) F) x : ℝ≥0) : ℝ)

variable {F}


def zetaIntegral {mI : MeasurableSpace (AdeleRing (𝓞 F) F)ˣ} (ν : Measure (AdeleRing (𝓞 F) F)ˣ)
    (f : AdeleRing (𝓞 F) F → ℂ) (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (s : ℂ) : ℂ :=
  ∫ x, f x * ((χ x : ℂˣ) : ℂ) * ((ideleNorm F x : ℝ) : ℂ) ^ s ∂ν

def localChar (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 F)) :
    (v.adicCompletion F)ˣ →* ℂˣ :=
  χ.comp ((Units.map (finIncl (𝓞 F) F)).comp (localUnit (𝓞 F) F v))

def archUnitHom (w : InfinitePlace F) : (w.Completion)ˣ →* (AdeleRing (𝓞 F) F)ˣ where
  toFun := archCentralUnit F w
  map_one' := by
    sorry
  map_mul' a b := by
    sorry

def archLocalChar (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (w : InfinitePlace F) :
    (w.Completion)ˣ →* ℂˣ :=
  χ.comp (archUnitHom w)

def IsUnramifiedCharAt (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 F)) : Prop :=
  ∀ t : (v.adicCompletion F)ˣ, (t : v.adicCompletion F) ∈ v.adicCompletionIntegers F →
    ((t⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈ v.adicCompletionIntegers F →
      localChar χ v t = 1

def integralOutside (S : Finset (HeightOneSpectrum (𝓞 F))) : Set (AdeleRing (𝓞 F) F) :=
  {x | ∀ v ∉ S, (x.2 : FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F}

def IsFactorizableStandardOutside (f : AdeleRing (𝓞 F) F → ℂ) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (g : (w : InfinitePlace F) → w.Completion → ℂ)
    (h : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ) : Prop :=
  ∀ x, f x = (integralOutside S).indicator
      (fun x => (∏ w, g w (x.1 w)) * ∏ v ∈ S, h v ((x.2 : FiniteAdeleRing (𝓞 F) F) v)) x

end NumberField.TateGlobal

end
