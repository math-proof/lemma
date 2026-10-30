import Mathlib.Probability.HasLaw
open MeasureTheory ProbabilityTheory

/-- `x ∼[π] μ` — `x` has law `μ` under sample measure `π` (`HasLaw`, no density/`ReferenceMeasure`). -/
notation:50 x:51 " ∼[" π:0 "] " μ:52 => HasLaw x μ π
