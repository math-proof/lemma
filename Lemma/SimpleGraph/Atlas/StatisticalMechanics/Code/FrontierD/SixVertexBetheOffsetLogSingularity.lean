import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexBetheOffsetLogSingularity
open StatMech StatMech.FrontierD


/--
[hasDerivAt_sixVertexBetheLogNormKernel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetLogSingularity.lean)
-/
@[path]
private lemma hasDerivAt_sixVertexBetheLogNormKernel_eq
  {c x : Real}
-- given
  (hc : 2 < c)
  (hx : x ≠ 0)
  (hxIcc : x ∈ Set.Icc (-Real.pi) Real.pi) :
-- imply
  HasDerivAt (sixVertexBetheLogNormKernel c) (sixVertexBetheLogNormDerivative c x) x := by
-- proof
  apply StatMech.FrontierD.hasDerivAt_sixVertexBetheLogNormKernel hc hx hxIcc

/--
[abs_mul_sixVertexBetheLogNormDenominatorDerivative_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetLogSingularity.lean)
-/
@[path]
private lemma abs_mul_sixVertexBetheLogNormDenominatorDerivative_le_eq
  {x : Real}
-- given
  (hx : x ≠ 0)
  (hxIcc : x ∈ Set.Icc (-Real.pi) Real.pi) :
-- imply
  |x * (Real.sin x / (2 - 2 * Real.cos x))| ≤ Real.pi / 2 := by
-- proof
  apply StatMech.FrontierD.abs_mul_sixVertexBetheLogNormDenominatorDerivative_le hx hxIcc

/--
[abs_mul_sixVertexBetheLogNormDerivative_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetLogSingularity.lean)
-/
@[path]
private lemma abs_mul_sixVertexBetheLogNormDerivative_le_eq
  {c x : Real}
-- given
  (hc : 2 < c)
  (hx : x ≠ 0)
  (hxIcc : x ∈ Set.Icc (-Real.pi) Real.pi) :
-- imply
  |x * sixVertexBetheLogNormDerivative c x| ≤ Real.pi * (c ^ 2 - 1) / (c ^ 2 - 2) ^ 2 + Real.pi / 2 := by
-- proof
  apply StatMech.FrontierD.abs_mul_sixVertexBetheLogNormDerivative_le hc hx hxIcc

/--
[abs_mul_sixVertexBetheLogNormDerivative_of_linearOffset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetLogSingularity.lean)
-/
@[path]
private lemma abs_mul_sixVertexBetheLogNormDerivative_of_linearOffset_eq
  {c C x f : Real}
-- given
  (hc : 2 < c)
  (hx : x ≠ 0)
  (hxIcc : x ∈ Set.Icc (-Real.pi) Real.pi)
  (hf : |f| ≤ C * |x|) :
-- imply
  |f * sixVertexBetheLogNormDerivative c x| ≤ C * (Real.pi * (c ^ 2 - 1) / (c ^ 2 - 2) ^ 2 + Real.pi / 2) := by
-- proof
  apply StatMech.FrontierD.abs_mul_sixVertexBetheLogNormDerivative_of_linearOffset hc hx hxIcc hf

/--
[hasDerivAt_sixVertexBetheLogNormDerivative](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetLogSingularity.lean)
-/
@[path]
private lemma hasDerivAt_sixVertexBetheLogNormDerivative_eq
  {c x : Real}
-- given
  (hc : 2 < c)
  (hx : x ≠ 0)
  (hxIcc : x ∈ Set.Icc (-Real.pi) Real.pi) :
-- imply
  HasDerivAt (sixVertexBetheLogNormDerivative c) ((-(c ^ 2 - 1) * Real.cos x * ((c ^ 2 - 1) ^ 2 + 1 + 2 * (c ^ 2 - 1) * Real.cos x) - 2 * (c ^ 2 - 1) ^ 2 * Real.sin x ^ 2) / (((c ^ 2 - 1) ^ 2 + 1 + 2 * (c ^ 2 - 1) * Real.cos x) ^ 2) + 1 / (2 - 2 * Real.cos x)) x := by
-- proof
  apply StatMech.FrontierD.hasDerivAt_sixVertexBetheLogNormDerivative hc hx hxIcc

/--
[abs_sq_mul_sixVertexBetheLogNormSecondDerivative_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetLogSingularity.lean)
-/
@[path]
private lemma abs_sq_mul_sixVertexBetheLogNormSecondDerivative_le_eq
  {c x : Real}
-- given
  (hc : 2 < c)
  (hx : x ≠ 0)
  (hxIcc : x ∈ Set.Icc (-Real.pi) Real.pi) :
-- imply
  |x ^ 2 * ((-(c ^ 2 - 1) * Real.cos x * ((c ^ 2 - 1) ^ 2 + 1 + 2 * (c ^ 2 - 1) * Real.cos x) - 2 * (c ^ 2 - 1) ^ 2 * Real.sin x ^ 2) / (((c ^ 2 - 1) ^ 2 + 1 + 2 * (c ^ 2 - 1) * Real.cos x) ^ 2) + 1 / (2 - 2 * Real.cos x))| <= sixVertexBetheLogNormSecondDerivativeBound c := by
-- proof
  apply StatMech.FrontierD.abs_sq_mul_sixVertexBetheLogNormSecondDerivative_le hc hx hxIcc


-- created on 2026-10-23
