import Lemma.LanglandsTunnell.CubicInduction_Structure
import Def.UnramifiedWhittaker_HeckeRecursion
import Def.LanglandsTunnell_CubicInduction_CellBumps

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm

noncomputable section

namespace LanglandsTunnell.CubicInduction


section Existence

variable (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]


theorem hasCubicInductionForm_iff_exists_isNormalizedOffRamified (pins : CarrierPins ℚ)
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) :
    HasCubicInductionForm K pins ψ μ ↔ ∃ D : CubicInductionForm K pins ψ μ, IsNormalizedOffRamified K pins ψ μ D :=
  Iff.rfl

end Existence

end LanglandsTunnell.CubicInduction

end
