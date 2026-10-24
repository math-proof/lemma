import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexBetheFourierPhysicalDensity
open StatMech StatMech.FrontierD


/--
[continuous_sixVertexMomentumRapidity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFourierPhysicalDensity.lean)
-/
@[path]
private lemma continuous_sixVertexMomentumRapidity_eq
  {lam : Real}
-- given
  (hlam : 0 < lam) :
-- imply
  Continuous (sixVertexMomentumRapidity lam hlam) := by
-- proof
  apply StatMech.FrontierD.continuous_sixVertexMomentumRapidity hlam

/--
[sixVertexMomentumRapidity_rapidityMomentum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFourierPhysicalDensity.lean)
-/
@[path]
private lemma sixVertexMomentumRapidity_rapidityMomentum_eq
  {lam : Real}
  {alpha : Real}
-- given
  (hlam : 0 < lam)
  (halpha : alpha ∈ Set.Icc (-Real.pi) Real.pi) :
-- imply
  sixVertexMomentumRapidity lam hlam (sixVertexRapidityMomentum lam alpha) = alpha := by
-- proof
  apply StatMech.FrontierD.sixVertexMomentumRapidity_rapidityMomentum hlam halpha

/--
[sixVertexRapidityMomentum_momentumRapidity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFourierPhysicalDensity.lean)
-/
@[path]
private lemma sixVertexRapidityMomentum_momentumRapidity_eq
  {lam : Real}
  {x : Real}
-- given
  (hlam : 0 < lam)
  (hx : x ∈ Set.Icc (-Real.pi) Real.pi) :
-- imply
  sixVertexRapidityMomentum lam (sixVertexMomentumRapidity lam hlam x) = x := by
-- proof
  apply StatMech.FrontierD.sixVertexRapidityMomentum_momentumRapidity hlam hx

/--
[continuous_sixVertexFourierPhysicalDensity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFourierPhysicalDensity.lean)
-/
@[path]
private lemma continuous_sixVertexFourierPhysicalDensity_eq
  {c : Real}
-- given
  (hc : 2 < c) :
-- imply
  Continuous (sixVertexFourierPhysicalDensity c hc) := by
-- proof
  apply StatMech.FrontierD.continuous_sixVertexFourierPhysicalDensity hc

/--
[sixVertexFourierPhysicalDensity_rapidityMomentum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFourierPhysicalDensity.lean)
-/
@[path]
private lemma sixVertexFourierPhysicalDensity_rapidityMomentum_eq
  {c : Real}
  {alpha : Real}
-- given
  (hc : 2 < c)
  (halpha : alpha ∈ Set.Icc (-Real.pi) Real.pi) :
-- imply
  sixVertexFourierPhysicalDensity c hc (sixVertexRapidityMomentum (sixVertexAntiferroelectricLambda c) alpha) = sixVertexFourierRootDensity (sixVertexAntiferroelectricLambda c) alpha / (2 * Real.pi * sixVertexXiFourier (sixVertexAntiferroelectricLambda c) alpha) := by
-- proof
  apply StatMech.FrontierD.sixVertexFourierPhysicalDensity_rapidityMomentum hc halpha

/--
[intervalIntegral_sixVertexFourierPhysicalDensity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFourierPhysicalDensity.lean)
-/
@[path]
private lemma intervalIntegral_sixVertexFourierPhysicalDensity_eq
  {c : Real}
-- given
  (hc : 2 < c) :
-- imply
  (∫ x in -Real.pi..Real.pi, sixVertexFourierPhysicalDensity c hc x) = 1 / 2 := by
-- proof
  apply StatMech.FrontierD.intervalIntegral_sixVertexFourierPhysicalDensity hc

/--
[sixVertexFourierPhysicalDensity_continuumEquation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFourierPhysicalDensity.lean)
-/
@[path]
private lemma sixVertexFourierPhysicalDensity_continuumEquation_eq
  {c : Real}
-- given
  (hc : 2 < c) :
-- imply
  SixVertexSatisfiesContinuousDensityEquation c (sixVertexFourierPhysicalDensity c hc) := by
-- proof
  apply StatMech.FrontierD.sixVertexFourierPhysicalDensity_continuumEquation hc

/--
[sixVertexTailRootDensity_eq_fourierPhysicalDensity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFourierPhysicalDensity.lean)
-/
@[path]
private lemma sixVertexTailRootDensity_eq_fourierPhysicalDensity_eq
  {c : Real}
-- given
  (hc : 2 < c)
  (htail : 2 < sixVertexAnisotropyMagnitude c) :
-- imply
  ∀ x ∈ Set.Icc (-Real.pi) Real.pi, sixVertexTailRootDensity hc htail x = sixVertexFourierPhysicalDensity c hc x := by
-- proof
  apply StatMech.FrontierD.sixVertexTailRootDensity_eq_fourierPhysicalDensity hc htail


-- created on 2026-10-23
