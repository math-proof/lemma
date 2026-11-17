/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/HoeffdingBernoulliSumAbsTail.lean -/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Moments.SubGaussian
open scoped BigOperators MeasureTheory

public section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
  [MeasureTheory.IsProbabilityMeasure μ]


namespace ProbabilityTheory
end ProbabilityTheory
