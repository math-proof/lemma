import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexBetheTailSelectedDensity
open StatMech StatMech.FrontierD


/--
[sixVertexSelectedFiniteRootDensity_eq_halfFilled](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheTailSelectedDensity.lean)
-/
@[path]
private lemma sixVertexSelectedFiniteRootDensity_eq_halfFilled_eq
  {c : Real}
  {k : Nat}
  {x : Real}
-- given
  (hc : 2 < c) :
-- imply
  sixVertexSelectedFiniteRootDensity hc k x = sixVertexFiniteRootDensity c (sixVertexFourWidth 0 k) ((k + 1) + (k + 1)) (sixVertexHalfFilledBetheRoots hc k) x := by
-- proof
  apply StatMech.FrontierD.sixVertexSelectedFiniteRootDensity_eq_halfFilled hc k x

/--
[sixVertexTailConvolutionError_fourWidth_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheTailSelectedDensity.lean)
-/
@[path]
private lemma sixVertexTailConvolutionError_fourWidth_tendsto_zero_eq
  {c : Real}
-- given
  (hc : 2 < c)
  (htail : 2 < sixVertexAnisotropyMagnitude c) :
-- imply
  Tendsto (fun k : Nat => sixVertexTailConvolutionError c (sixVertexFourWidth 0 k)) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierD.sixVertexTailConvolutionError_fourWidth_tendsto_zero hc htail

/--
[sixVertexSelectedFiniteRootDensity_weighted_cauchy_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheTailSelectedDensity.lean)
-/
@[path]
private lemma sixVertexSelectedFiniteRootDensity_weighted_cauchy_tail_eq
  {c : Real}
  {k l : Nat}
-- given
  (hc : 2 < c)
  (htail : 2 < sixVertexAnisotropyMagnitude c) :
-- imply
  ∀ x ∈ Set.Icc (-Real.pi) Real.pi, |sixVertexRootDensityWeight c x * (sixVertexSelectedFiniteRootDensity hc k x - sixVertexSelectedFiniteRootDensity hc l x)| <= ((sixVertexTailConvolutionError c (sixVertexFourWidth 0 k) + sixVertexTailConvolutionError c (sixVertexFourWidth 0 l)) / (2 * Real.pi)) / (1 - sixVertexRootDensityContractionRate c) := by
-- proof
  apply StatMech.FrontierD.sixVertexSelectedFiniteRootDensity_weighted_cauchy_tail hc htail k l

/--
[sixVertexSelectedFiniteRootDensity_approximateEquation_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheTailSelectedDensity.lean)
-/
@[path]
private lemma sixVertexSelectedFiniteRootDensity_approximateEquation_tail_eq
  {c : Real}
  {k : Nat}
  {x : Real}
-- given
  (hc : 2 < c)
  (htail : 2 < sixVertexAnisotropyMagnitude c) :
-- imply
  |sixVertexRootDensityWeight c x * sixVertexSelectedFiniteRootDensity hc k x - (sixVertexRootDensityWeight c x / (2 * Real.pi) - (1 / (2 * Real.pi)) * ∫ y in -Real.pi..Real.pi, sixVertexRootDensityKernel c x y * sixVertexSelectedFiniteRootDensity hc k y)| <= sixVertexTailConvolutionError c (sixVertexFourWidth 0 k) / (2 * Real.pi) := by
-- proof
  apply StatMech.FrontierD.sixVertexSelectedFiniteRootDensity_approximateEquation_tail hc htail k x


-- created on 2026-10-23
