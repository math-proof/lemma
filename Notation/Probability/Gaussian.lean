import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.HasLaw
open MeasureTheory ProbabilityTheory
open scoped NNReal


/-- `𝒩(μ, σ)` — univariate normal / Gaussian law (`gaussianReal`); `σ` is variance. -/
notation "𝒩(" μ ", " σ ")" => gaussianReal μ σ


/-- `x ∼[π] μ` — `x` has law `μ` under sample measure `π` (`HasLaw`, no density/`ReferenceMeasure`). -/
notation:50 x:51 " ∼[" π:0 "] " μ:52 => HasLaw x μ π
