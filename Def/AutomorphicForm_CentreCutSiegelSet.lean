import Def.NumberField_AdelicVolume

open MeasureTheory Set IsDedekindDomain NumberField Metric

noncomputable section

namespace AutomorphicForm

namespace WindowedSiegel

open NumberField.AdelicLevel NumberField.AdelicVolume NumberField.AdelicCentre

variable (F : Type) [Field F] [NumberField F]

def centreCutSiegelSet (c u d₁ d₂ : ℝ) : Set (AdelicGL2 (𝓞 F) F) :=
  {g | glFin (𝓞 F) F g ∈ finiteIntegralGL2 (𝓞 F) F ∧
    (∀ w : InfinitePlace F,
      c ≤ localHeight (archComponent F w (glArch (𝓞 F) F g))) ∧
    (∀ w : InfinitePlace F,
      xWindowSq (archComponent F w (glArch (𝓞 F) F g)) ≤ u ^ 2) ∧
    (∀ w : InfinitePlace F, archDetNorm w g ∈ Icc d₁ d₂)}

variable {F}


variable (F)

def cappedSiegelBlock (c u d₁ d₂ : ℝ) : Set (AdelicGL2 (𝓞 F) F) :=
  centreCutSiegelSet F c u d₁ d₂ ∩
    {g | ∀ w : InfinitePlace F,
      localHeight (archComponent F w (glArch (𝓞 F) F g)) ≤ 4 * c}

end WindowedSiegel

end AutomorphicForm

end
