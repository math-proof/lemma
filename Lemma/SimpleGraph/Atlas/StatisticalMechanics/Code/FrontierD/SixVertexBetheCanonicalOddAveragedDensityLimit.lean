import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalOddAveragedDensityLimit
open StatMech StatMech.FrontierD


/--
[tendsto_sixVertexCanonicalOddAveragedDensityHalfCell](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddAveragedDensityLimit.lean)
-/
@[path]
private lemma tendsto_sixVertexCanonicalOddAveragedDensityHalfCell_eq
  {c : Real}
  {s : Nat}
-- given
  (hc : 2 < c) :
-- imply
  Tendsto (fun k => let N := sixVertexFourWidth (2 * s + 1) k let n := (2 * s + 1 + k + 1) + (2 * s + 1 + k + 1) let p := sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k) let F := sixVertexBetheCountingFunction c N n p 2 * ∑ j : Fin (s + k + 1), (Real.log (F (sixVertexCanonicalOddMidpointHalfRoot hc s k j) / sixVertexCanonicalOddMidpointHalfRoot hc s k j) - Real.log (F (sixVertexCanonicalOddLeftHalfRoot hc s k j) / sixVertexCanonicalOddLeftHalfRoot hc s k j))) atTop (nhds (Real.log (1 / (4 * Real.pi)) - Real.log (sixVertexFourierPhysicalDensity c hc 0))) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexCanonicalOddAveragedDensityHalfCell hc s


-- created on 2026-10-23
