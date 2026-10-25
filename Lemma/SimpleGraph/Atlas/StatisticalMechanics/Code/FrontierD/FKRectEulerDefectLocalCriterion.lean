import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectEulerDefectLocalCriterion
open Finset StatMech StatMech.FrontierD


/--
[fkRectMedialLoopCount_insert_of_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectEulerDefectLocalCriterion.lean)
-/
@[path]
private lemma fkRectMedialLoopCount_insert_of_reachable_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {e : R.EdgeIndex}
-- given
  (heF : e ∉ F)
  (hconn : (fkMedialLoopGraph R.medialTorus (fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F))).Reachable (fkMedialWestDart (fkRectMedialVertexOfEdge R e)) (fkMedialEastDart (fkRectMedialVertexOfEdge R e))) :
-- imply
  fkRectMedialLoopCount R (fkRectConfigurationOfEdges R F) + 1 = fkRectMedialLoopCount R (fkRectConfigurationOfEdges R (insert e F)) := by
-- proof
  apply StatMech.FrontierD.fkRectMedialLoopCount_insert_of_reachable R F e heF hconn

/--
[fkRectMedialLoopCount_insert_of_medial_not_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectEulerDefectLocalCriterion.lean)
-/
@[path]
private lemma fkRectMedialLoopCount_insert_of_medial_not_reachable_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {e : R.EdgeIndex}
-- given
  (heF : e ∉ F)
  (hdisc : ¬(fkMedialLoopGraph R.medialTorus (fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F))).Reachable (fkMedialWestDart (fkRectMedialVertexOfEdge R e)) (fkMedialEastDart (fkRectMedialVertexOfEdge R e))) :
-- imply
  fkRectMedialLoopCount R (fkRectConfigurationOfEdges R (insert e F)) + 1 = fkRectMedialLoopCount R (fkRectConfigurationOfEdges R F) := by
-- proof
  apply StatMech.FrontierD.fkRectMedialLoopCount_insert_of_medial_not_reachable R F e heF hdisc

/--
[fkRectEulerHomologyDefect_insert_eq_add_two_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectEulerDefectLocalCriterion.lean)
-/
@[path]
private lemma fkRectEulerHomologyDefect_insert_eq_add_two_iff_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {e : R.EdgeIndex}
-- given
  (heF : e ∉ F) :
-- imply
  fkRectEulerHomologyDefect R (fkRectConfigurationOfEdges R (insert e F)) = fkRectEulerHomologyDefect R (fkRectConfigurationOfEdges R F) + 2 <-> (fkRectOpenGraph R (fkRectConfigurationOfEdges R F)).Reachable (fkRectMedialWestPrimal R e) (fkRectMedialEastPrimal R e) ∧ ¬(fkMedialLoopGraph R.medialTorus (fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F))).Reachable (fkMedialWestDart (fkRectMedialVertexOfEdge R e)) (fkMedialEastDart (fkRectMedialVertexOfEdge R e)) := by
-- proof
  apply StatMech.FrontierD.fkRectEulerHomologyDefect_insert_eq_add_two_iff R F e heF


-- created on 2026-10-23
