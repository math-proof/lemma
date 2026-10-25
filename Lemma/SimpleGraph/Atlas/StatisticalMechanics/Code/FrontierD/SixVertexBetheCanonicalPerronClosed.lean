import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalPerronClosed
open Filter Topology StatMech StatMech.FrontierD


/--
[tendsto_sixVertexCanonicalPerronRegularizedFourierValue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronClosed.lean)
-/
@[path]
private lemma tendsto_sixVertexCanonicalPerronRegularizedFourierValue_eq
  {c : Real}
-- given
  (hc : 2 < c) :
-- imply
  Tendsto (fun k => sixVertexRegularizedRapidityFourierValue (sixVertexAntiferroelectricLambda c) (sixVertexCanonicalPerronLogEpsilon hc k)) atTop (nhds (sixVertexAntiferroelectricFreeEnergyValue (sixVertexAntiferroelectricLambda c))) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexCanonicalPerronRegularizedFourierValue hc

/--
[tendsto_sixVertexCanonicalPerronRegularizedIntegral](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronClosed.lean)
-/
@[path]
private lemma tendsto_sixVertexCanonicalPerronRegularizedIntegral_eq
  {c : Real}
-- given
  (hc : 2 < c) :
-- imply
  Tendsto (sixVertexCanonicalPerronRegularizedIntegral hc) atTop (nhds (sixVertexAntiferroelectricFreeEnergyValue (sixVertexAntiferroelectricLambda c))) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexCanonicalPerronRegularizedIntegral hc

/--
[tendsto_sixVertexCanonicalPerronRootAverage_freeEnergy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronClosed.lean)
-/
@[path]
private lemma tendsto_sixVertexCanonicalPerronRootAverage_freeEnergy_eq
  {c : Real}
-- given
  (hc : 2 < c) :
-- imply
  Tendsto (sixVertexSymmetricBetheRootAverage c (sixVertexCanonicalDensityPerronPositiveHalfRootFamily hc)) atTop (nhds (sixVertexAntiferroelectricFreeEnergyValue (sixVertexAntiferroelectricLambda c))) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexCanonicalPerronRootAverage_freeEnergy hc

/--
[tendsto_sixVertexCanonicalDensityPerronEmpiricalLog_freeEnergy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronClosed.lean)
-/
@[path]
private lemma tendsto_sixVertexCanonicalDensityPerronEmpiricalLog_freeEnergy_eq
  {c : Real}
-- given
  (hc : 2 < c) :
-- imply
  Tendsto (sixVertexCanonicalDensityPerronEmpiricalObservable hc (sixVertexBetheLogObservable c)) atTop (nhds (sixVertexAntiferroelectricFreeEnergyValue (sixVertexAntiferroelectricLambda c))) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexCanonicalDensityPerronEmpiricalLog_freeEnergy hc

/--
[tendsto_sixVertexCentralWidthRate_canonicalPerron](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronClosed.lean)
-/
@[path]
private lemma tendsto_sixVertexCentralWidthRate_canonicalPerron_eq
  {c : Real}
-- given
  (hc : 2 < c) :
-- imply
  Tendsto (sixVertexCentralWidthRate c) atTop (nhds (sixVertexAntiferroelectricFreeEnergyValue (sixVertexAntiferroelectricLambda c))) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexCentralWidthRate_canonicalPerron hc

/--
[sixVertexBalanced_iteratedLimit_of_canonicalPerron](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronClosed.lean)
-/
@[path]
private lemma sixVertexBalanced_iteratedLimit_of_canonicalPerron_eq
  {c : Real}
-- given
  (hc : 2 < c) :
-- imply
  SixVertexHasIteratedLimit (sixVertexBalancedAreaDensity c) (sixVertexAntiferroelectricFreeEnergyValue (sixVertexAntiferroelectricLambda c)) := by
-- proof
  apply StatMech.FrontierD.sixVertexBalanced_iteratedLimit_of_canonicalPerron hc


-- created on 2026-10-23
