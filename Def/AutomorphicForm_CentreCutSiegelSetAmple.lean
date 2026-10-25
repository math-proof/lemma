import Def.AutomorphicForm_CentreCutSiegelSet
import Lemma.NumberField.SiegelVolume

set_option autoImplicit false

open MeasureTheory Set IsDedekindDomain NumberField Metric

noncomputable section

namespace AutomorphicForm

namespace WindowedSiegel

open NumberField.AdelicLevel NumberField.AdelicVolume NumberField.AdelicCentre NumberField.SiegelVolume

variable (F : Type) [Field F] [NumberField F]

def centreCutSiegelSetAmple (c u d₁ d₂ κ : ℝ) : Set (AdelicGL2 (𝓞 F) F) :=
  {g | g ∈ centreCutSiegelSet F c u d₁ d₂ ∧
    ∀ w w' : InfinitePlace F,
      localHeight (archComponent F w (glArch (𝓞 F) F g)) ≤
        κ * localHeight (archComponent F w' (glArch (𝓞 F) F g))}

end WindowedSiegel

end AutomorphicForm

end
