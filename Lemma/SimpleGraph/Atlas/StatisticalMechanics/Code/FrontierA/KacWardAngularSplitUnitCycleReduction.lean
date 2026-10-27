import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAngularSplitUnitCycleReduction
open StatMech StatMech.FrontierA


/--
[kwAngularSplit_unitCycleLog_of_cyclePhaseSign](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngularSplitUnitCycleReduction.lean)
-/
@[path]
private lemma kwAngularSplit_unitCycleLog_of_cyclePhaseSign_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
-- given
  (hphase : KWAngularSplitCyclePhaseSign embedding) :
-- imply
  KWGraphUnitCycleLog (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding)) (kwAngularSplitPhase embedding) := by
-- proof
  apply StatMech.FrontierA.kwAngularSplit_unitCycleLog_of_cyclePhaseSign embedding hphase

/--
[kacWard_original_of_angularSplit_cyclePhaseSign](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngularSplitUnitCycleReduction.lean)
-/
@[path]
private lemma kacWard_original_of_angularSplit_cyclePhaseSign_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {weight : Sym2 V → Complex}
-- given
  (hphase : KWAngularSplitCyclePhaseSign embedding) :
-- imply
  (1 - kwGraphTransition G weight embedding.turnPhase).det = (kwEvenPolynomial G weight) ^ 2 := by
-- proof
  apply StatMech.FrontierA.kacWard_original_of_angularSplit_cyclePhaseSign embedding weight hphase


-- created on 2026-10-23
