import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoStrandCycleFamily.Part2
open StatMech StatMech.FrontierD


/--
[sixVertexDegreeTwoStrandCycleEnumeration_vertex_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoStrandCycleFamily.lean)
-/
@[path]
private lemma sixVertexDegreeTwoStrandCycleEnumeration_vertex_ne_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {first second : SixVertexOrientedDisagreementDart omega eta}
  {i : Fin (orderOf (sixVertexDegreeTwoStrandCyclePerm homega heta hdegree first))}
  {j : Fin (orderOf (sixVertexDegreeTwoStrandCyclePerm homega heta hdegree second))}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (hseparate : ¬ (sixVertexOrientedDegreeTwoStrandSuccessor homega heta hdegree).SameCycle first second) :
-- imply
  (sixVertexDegreeTwoStrandCycleEnumeration homega heta hdegree first i).1.1.1 ≠ (sixVertexDegreeTwoStrandCycleEnumeration homega heta hdegree second j).1.1.1 := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoStrandCycleEnumeration_vertex_ne homega heta hdegree first second hseparate i j

/--
[SixVertexDegreeTwoSynchronizedHighChargeSeed.separateCycles_or_sameCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoStrandCycleFamily.lean)
-/
@[path]
private lemma separateCycles_or_sameCycle_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {homega : omega.IceRule}
  {heta : eta.IceRule}
  {hdegree : SixVertexLocallyDegreeTwo omega eta}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree component} :
-- imply
  (¬ (sixVertexOrientedDegreeTwoStrandSuccessor homega heta hdegree).SameCycle seed.first seed.second) ∨ (sixVertexOrientedDegreeTwoStrandSuccessor homega heta hdegree).SameCycle seed.first seed.second := by
-- proof
  apply StatMech.FrontierD.SixVertexDegreeTwoSynchronizedHighChargeSeed.separateCycles_or_sameCycle seed


-- created on 2026-10-23
