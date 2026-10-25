/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman/TwoPowerBadSets.lean -/

import Theorem.Analysis.Complex.Wiman.LogMajorantRegularity
import Lemma.Complex.Wiman.LogMajorantRegularity
import Lemma.Real.Calculus.PowerGrowthBadSet
import Def.Analysis.Calculus.PowerGrowthBadSet


namespace Complex

open Filter MeasureTheory Set

open scoped ENNReal

noncomputable section

/-- The union of the power-growth bad sets for the logarithmic majorant and its derivative. -/
def wimanExceptionalSet (f : ℂ → ℂ) (x₀ : ℝ) : Set ℝ :=
  Real.powerGrowthBadSet (wimanGrowth f) (9 / 8 : ℝ) x₀ ∪
    Real.powerGrowthBadSet (deriv (wimanGrowth f)) (9 / 8 : ℝ) x₀

end
end Complex
