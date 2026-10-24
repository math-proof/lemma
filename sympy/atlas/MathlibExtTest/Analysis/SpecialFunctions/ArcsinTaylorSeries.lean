/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/SpecialFunctions/ArcsinTaylorSeries.lean -/


import sympy.atlas.Analysis.SpecialFunctions.ArcsinTaylorSeries
import Lemma.Real.ArcsinTaylorSeries

namespace MathlibExtTest.Analysis.SpecialFunctions.ArcsinTaylorSeries

open MathlibExt.Analysis.SpecialFunctions.ArcsinTaylorSeries

example : centralBinomialCoeff 0 = 1 := by
  norm_num [centralBinomialCoeff]

example {y : ℝ} (hy : y ∈ Set.Ioo (-1 : ℝ) 1) :
    arcsinSeries y = Real.arcsin y :=
  arcsinSeries_eq_arcsin hy

example : ContinuousOn arcsinIntegralSeries (Set.Icc (-1 : ℝ) 1) :=
  continuousOn_arcsinIntegralSeries

example {y : ℝ} (hy : ‖y‖ < 1) (hy0 : y ≠ 0) :
    HasDerivAt arcsinIntegralSeries (Real.arcsin y / y) y :=
  hasDerivAt_arcsinIntegralSeries hy hy0

end MathlibExtTest.Analysis.SpecialFunctions.ArcsinTaylorSeries
