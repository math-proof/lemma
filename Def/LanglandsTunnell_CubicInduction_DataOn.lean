import Lemma.LanglandsTunnell.CubicInduction_Structure
import Structure.LanglandsTunnell_CubicInduction_DataOn

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField MeasureTheory AutomorphicForm

noncomputable section

namespace LanglandsTunnell.CubicInduction

def CubicInductionForm.toData {K : Type} [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)]
    [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)] {pins : CarrierPins ℚ} {ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ}
    {μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} (D : CubicInductionForm K pins ψ μ) : CubicInductionData where
  form := D.form
  whittaker := D.whittaker
  whittakerLoc := D.whittakerLoc
  whittakerArch := D.whittakerArch
  centralChar := D.centralChar
  dualWhittaker := D.dualWhittaker


end LanglandsTunnell.CubicInduction

end
