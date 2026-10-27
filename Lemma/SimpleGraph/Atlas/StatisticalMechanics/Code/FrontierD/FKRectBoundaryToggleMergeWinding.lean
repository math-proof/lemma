import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryToggleMergeWinding
open Equiv Finset SimpleGraph StatMech StatMech.FrontierD


/--
[fkRectBlackBoundaryCycleClassWinding_insert_of_not_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryToggleMergeWinding.lean)
-/
@[path]
private lemma fkRectBlackBoundaryCycleClassWinding_insert_of_not_reachable_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {e : R.EdgeIndex}
-- given
  (heF : e ∉ F)
  (hdisc : ¬ (fkMedialLoopGraph R.medialTorus (fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F))).Reachable (fkMedialWestDart (fkRectMedialVertexOfEdge R e)) (fkMedialEastDart (fkRectMedialVertexOfEdge R e))) :
-- imply
  fkRectBlackBoundaryCycleClassWinding R (fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R (insert e F))) (fkMedialBlackDart0 (fkRectMedialVertexOfEdge R e)) = fkRectBlackBoundaryCycleClassWinding R (fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F)) (fkMedialBlackDart0 (fkRectMedialVertexOfEdge R e)) + fkRectBlackBoundaryCycleClassWinding R (fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F)) (fkMedialBlackDart1 (fkRectMedialVertexOfEdge R e)) := by
-- proof
  apply StatMech.FrontierD.fkRectBlackBoundaryCycleClassWinding_insert_of_not_reachable R F e heF hdisc

/--
[fkRectBlackBoundaryCycleClassWinding_eq_insert_of_not_reachable_away](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryToggleMergeWinding.lean)
-/
@[path]
private lemma fkRectBlackBoundaryCycleClassWinding_eq_insert_of_not_reachable_away_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {e : R.EdgeIndex}
  {d : FKMedialBlackDart R.medialTorus}
-- given
  (heF : e ∉ F)
  (hdisc : ¬ (fkMedialLoopGraph R.medialTorus (fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F))).Reachable (fkMedialWestDart (fkRectMedialVertexOfEdge R e)) (fkMedialEastDart (fkRectMedialVertexOfEdge R e)))
  (hd0 : ¬ (fkMedialBlackBoundaryPerm (fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F))).SameCycle (fkMedialBlackDart0 (fkRectMedialVertexOfEdge R e)) d)
  (hd1 : ¬ (fkMedialBlackBoundaryPerm (fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F))).SameCycle (fkMedialBlackDart1 (fkRectMedialVertexOfEdge R e)) d) :
-- imply
  fkRectBlackBoundaryCycleClassWinding R (fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F)) d = fkRectBlackBoundaryCycleClassWinding R (fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R (insert e F))) d := by
-- proof
  apply StatMech.FrontierD.fkRectBlackBoundaryCycleClassWinding_eq_insert_of_not_reachable_away R F e heF hdisc d hd0 hd1


-- created on 2026-10-23
