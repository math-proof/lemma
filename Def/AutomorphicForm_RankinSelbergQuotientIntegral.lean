import Abbrev.AutomorphicForm_RationalCentreUnipotentQuotient
import Def.AutomorphicForm_WhittakerCoefficient
import Def.NumberField_TateGlobalZeta

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox IsDedekindDomain

noncomputable section

namespace AutomorphicForm

namespace RankinSelberg

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

variable (K : Type) [Field K] [NumberField K]

def quotientIntegrand (pins : CarrierPins K) (ψ : AddChar (AdeleRing (𝓞 K) K) ℂ)
    (x y φ : AdelicGL2 (𝓞 K) K → ℂ) (w d₁ d₂ : ℝ) (g : AdelicGL2 (𝓞 K) K) : ℂ :=
  ({g : AdelicGL2 (𝓞 K) K |
        NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂}.indicator
      (fun _ => (1 : ℂ)) g) *
    whittakerCoefficient K pins ψ x 1 g * (starRingEnd ℂ) (whittakerCoefficient K pins ψ y 1 g) * φ g *
    ((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ (-w) : ℝ) : ℂ)

def quotientIntegral (pins : CarrierPins K) (ψ : AddChar (AdeleRing (𝓞 K) K) ℂ)
    (x y φ : AdelicGL2 (𝓞 K) K → ℂ) (w d₁ d₂ : ℝ) : ℂ :=
  ∫ q : RationalCentreUnipotentQuotient K, quotientIntegrand K pins ψ x y φ w d₁ d₂ q.out
    ∂(rationalCentreUnipotentQuotientMeasure K)

def shellZeroOutside (S : Finset (HeightOneSpectrum (𝓞 K))) : Set (AdelicGL2 (𝓞 K) K) :=
  {g | ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
    Valued.v ((((Matrix.GeneralLinearGroup.det g : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).2 v) =
      (max (Valued.v (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0).2 v))
           (Valued.v (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v))) ^ 2}

def sPartIntegral (S : Finset (HeightOneSpectrum (𝓞 K))) (pins : CarrierPins K)
    (ψ : AddChar (AdeleRing (𝓞 K) K) ℂ) (x y φ : AdelicGL2 (𝓞 K) K → ℂ) (w d₁ d₂ : ℝ) : ℂ :=
  ∫ q in {q : RationalCentreUnipotentQuotient K | q.out ∈ shellZeroOutside K S},
    quotientIntegrand K pins ψ x y φ w d₁ d₂ q.out ∂(rationalCentreUnipotentQuotientMeasure K)

end RankinSelberg

end AutomorphicForm

end
