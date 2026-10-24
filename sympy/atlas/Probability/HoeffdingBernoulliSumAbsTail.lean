/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/HoeffdingBernoulliSumAbsTail.lean -/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Moments.SubGaussian

open scoped BigOperators MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
  [MeasureTheory.IsProbabilityMeasure μ]

namespace ProbabilityTheory
end ProbabilityTheory
