/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman/CoefficientExponentialFamily.lean -/

import Def.Analysis.Complex.Wiman.RadialMajorant
import Lemma.Complex.Wiman.RadialMajorant
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Probability.Moments.Tilted


namespace Complex

open MeasureTheory ProbabilityTheory

open scoped ENNReal

noncomputable section

/-- The logarithm of the radial Taylor majorant at logarithmic radius `x`. -/
def wimanGrowth (f : ℂ → ℂ) (x : ℝ) : ℝ :=
  Real.log (wimanMajorant f (Real.exp x))

/-- The atomic measure whose mass at `n` is the norm of the `n`th Taylor coefficient. -/
def wimanCoefficientMeasure (f : ℂ → ℂ) : Measure ℕ :=
  Measure.sum fun n : ℕ =>
    ENNReal.ofReal ‖wimanTaylorCoefficient f n‖ • Measure.dirac n

/-- The coefficient measure tilted at logarithmic radius `x`. -/
def wimanTiltedMeasure (f : ℂ → ℂ) (x : ℝ) : Measure ℕ :=
  (wimanCoefficientMeasure f).tilted fun n : ℕ => x * (n : ℝ)

end
end Complex
