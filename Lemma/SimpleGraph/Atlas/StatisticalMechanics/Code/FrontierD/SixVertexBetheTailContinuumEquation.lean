import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheTailContinuumEquation
open StatMech StatMech.FrontierD


/--
[abs_selectedDensityConvolution_sub_tailConvolution_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheTailContinuumEquation.lean)
-/
@[path]
private lemma abs_selectedDensityConvolution_sub_tailConvolution_le_eq
  {c : Real}
  {k : Nat}
  {x : Real}
-- given
  (hc : 2 < c)
  (htail : 2 < sixVertexAnisotropyMagnitude c) :
-- imply
  |(∫ y in -Real.pi..Real.pi, sixVertexRootDensityKernel c x y * sixVertexSelectedFiniteRootDensity hc k y) - ∫ y in -Real.pi..Real.pi, sixVertexRootDensityKernel c x y * sixVertexTailRootDensity hc htail y| <= 2 * Real.pi * (sixVertexAnisotropyMagnitude c / (sixVertexAnisotropyMagnitude c - 1)) * dist (sixVertexSelectedWeightedDensityMap hc k) (sixVertexTailWeightedDensityLimitMap hc htail) := by
-- proof
  apply StatMech.FrontierD.abs_selectedDensityConvolution_sub_tailConvolution_le hc htail k x

/--
[tendsto_sixVertexSelectedDensityConvolution_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheTailContinuumEquation.lean)
-/
@[path]
private lemma tendsto_sixVertexSelectedDensityConvolution_tail_eq
  {c : Real}
  {x : Real}
-- given
  (hc : 2 < c)
  (htail : 2 < sixVertexAnisotropyMagnitude c) :
-- imply
  Tendsto (fun k => ∫ y in -Real.pi..Real.pi, sixVertexRootDensityKernel c x y * sixVertexSelectedFiniteRootDensity hc k y) atTop (nhds (∫ y in -Real.pi..Real.pi, sixVertexRootDensityKernel c x y * sixVertexTailRootDensity hc htail y)) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexSelectedDensityConvolution_tail hc htail x

/--
[sixVertexTailRootDensity_continuumEquation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheTailContinuumEquation.lean)
-/
@[path]
private lemma sixVertexTailRootDensity_continuumEquation_eq
  {c : Real}
  {x : Real}
-- given
  (hc : 2 < c)
  (htail : 2 < sixVertexAnisotropyMagnitude c)
  (hx : x ∈ Set.Icc (-Real.pi) Real.pi) :
-- imply
  sixVertexRootDensityWeight c x * sixVertexTailRootDensity hc htail x = sixVertexRootDensityWeight c x / (2 * Real.pi) - (1 / (2 * Real.pi)) * ∫ y in -Real.pi..Real.pi, sixVertexRootDensityKernel c x y * sixVertexTailRootDensity hc htail y := by
-- proof
  apply StatMech.FrontierD.sixVertexTailRootDensity_continuumEquation hc htail hx


-- created on 2026-10-23
