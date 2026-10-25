import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalPerronAbelLimit
open Filter Set Topology StatMech StatMech.FrontierD


/--
[tendsto_sixVertexRegularizedRapidityDelta_nhdsWithin_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronAbelLimit.lean)
-/
@[path]
private lemma tendsto_sixVertexRegularizedRapidityDelta_nhdsWithin_zero_eq
  {lam : Real} :
-- imply
  Tendsto (sixVertexRegularizedRapidityDelta lam) (nhdsWithin 0 (Ioi 0)) (nhds 1) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexRegularizedRapidityDelta_nhdsWithin_zero lam

/--
[tendsto_sixVertexRegularizedRapidityRadius_nhdsWithin_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronAbelLimit.lean)
-/
@[path]
private lemma tendsto_sixVertexRegularizedRapidityRadius_nhdsWithin_zero_eq
  {lam : Real}
-- given
  (hlam : 0 < lam) :
-- imply
  Tendsto (sixVertexRegularizedRapidityRadius lam) (nhdsWithin 0 (Ioi 0)) (nhds 1) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexRegularizedRapidityRadius_nhdsWithin_zero hlam

/--
[tendsto_sixVertexCanonicalPerronRapidityRadius](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronAbelLimit.lean)
-/
@[path]
private lemma tendsto_sixVertexCanonicalPerronRapidityRadius_eq
  {c : Real}
-- given
  (hc : 2 < c) :
-- imply
  Tendsto (fun k => sixVertexRegularizedRapidityRadius (sixVertexAntiferroelectricLambda c) (sixVertexCanonicalPerronLogEpsilon hc k)) atTop (nhds 1) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexCanonicalPerronRapidityRadius hc

/--
[tendsto_sixVertexRegularizedRapidityConstant_nhdsWithin_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronAbelLimit.lean)
-/
@[path]
private lemma tendsto_sixVertexRegularizedRapidityConstant_nhdsWithin_zero_eq
  {lam : Real}
-- given
  (hlam : 0 < lam) :
-- imply
  Tendsto (sixVertexRegularizedRapidityConstant lam) (nhdsWithin 0 (Ioi 0)) (nhds lam) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexRegularizedRapidityConstant_nhdsWithin_zero hlam

/--
[tendsto_sixVertexCanonicalPerronRapidityConstant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronAbelLimit.lean)
-/
@[path]
private lemma tendsto_sixVertexCanonicalPerronRapidityConstant_eq
  {c : Real}
-- given
  (hc : 2 < c) :
-- imply
  Tendsto (fun k => sixVertexRegularizedRapidityConstant (sixVertexAntiferroelectricLambda c) (sixVertexCanonicalPerronLogEpsilon hc k)) atTop (nhds (sixVertexAntiferroelectricLambda c)) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexCanonicalPerronRapidityConstant hc


-- created on 2026-10-23
