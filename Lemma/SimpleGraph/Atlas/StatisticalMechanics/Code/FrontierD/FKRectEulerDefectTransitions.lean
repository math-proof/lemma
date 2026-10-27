import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectEulerDefectTransitions
open Finset StatMech StatMech.FrontierD


/--
[fkRectMedialLoopCount_insert_dichotomy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectEulerDefectTransitions.lean)
-/
@[path]
private lemma fkRectMedialLoopCount_insert_dichotomy_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {e : R.EdgeIndex}
-- given
  (heF : e ∉ F) :
-- imply
  fkRectMedialLoopCount R (fkRectConfigurationOfEdges R (insert e F)) + 1 = fkRectMedialLoopCount R (fkRectConfigurationOfEdges R F) ∨ fkRectMedialLoopCount R (fkRectConfigurationOfEdges R F) + 1 = fkRectMedialLoopCount R (fkRectConfigurationOfEdges R (insert e F)) := by
-- proof
  apply StatMech.FrontierD.fkRectMedialLoopCount_insert_dichotomy R F e heF

/--
[fkRectEulerHomologyDefect_insert_dichotomy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectEulerDefectTransitions.lean)
-/
@[path]
private lemma fkRectEulerHomologyDefect_insert_dichotomy_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {e : R.EdgeIndex}
-- given
  (heF : e ∉ F) :
-- imply
  fkRectEulerHomologyDefect R (fkRectConfigurationOfEdges R (insert e F)) = fkRectEulerHomologyDefect R (fkRectConfigurationOfEdges R F) ∨ fkRectEulerHomologyDefect R (fkRectConfigurationOfEdges R (insert e F)) = fkRectEulerHomologyDefect R (fkRectConfigurationOfEdges R F) + 2 := by
-- proof
  apply StatMech.FrontierD.fkRectEulerHomologyDefect_insert_dichotomy R F e heF


-- created on 2026-10-23
