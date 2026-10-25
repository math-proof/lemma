import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectEulerDefectInsertion
open Finset StatMech StatMech.FrontierD


/--
[fkRectMedialLoopCount_insert_of_not_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectEulerDefectInsertion.lean)
-/
@[path]
private lemma fkRectMedialLoopCount_insert_of_not_reachable_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {e : R.EdgeIndex}
  {p q : R.Vertex}
-- given
  (heF : e ∉ F)
  (hedge : fkRectTorusIndexedEdge R e = s(p, q))
  (hpq : ¬ (fkRectOpenGraph R (fkRectConfigurationOfEdges R F)).Reachable p q) :
-- imply
  fkRectMedialLoopCount R (fkRectConfigurationOfEdges R (insert e F)) + 1 = fkRectMedialLoopCount R (fkRectConfigurationOfEdges R F) := by
-- proof
  apply StatMech.FrontierD.fkRectMedialLoopCount_insert_of_not_reachable R F e heF hedge hpq

/--
[fkRectMedialLoopCount_insert_le_add_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectEulerDefectInsertion.lean)
-/
@[path]
private lemma fkRectMedialLoopCount_insert_le_add_one_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {e : R.EdgeIndex}
-- given
  (heF : e ∉ F) :
-- imply
  fkRectMedialLoopCount R (fkRectConfigurationOfEdges R (insert e F)) ≤ fkRectMedialLoopCount R (fkRectConfigurationOfEdges R F) + 1 := by
-- proof
  apply StatMech.FrontierD.fkRectMedialLoopCount_insert_le_add_one R F e heF

/--
[fkRectEulerHomologyDefect_insert_of_not_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectEulerDefectInsertion.lean)
-/
@[path]
private lemma fkRectEulerHomologyDefect_insert_of_not_reachable_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {e : R.EdgeIndex}
  {p q : R.Vertex}
-- given
  (heF : e ∉ F)
  (hedge : fkRectTorusIndexedEdge R e = s(p, q))
  (hpq : ¬ (fkRectOpenGraph R (fkRectConfigurationOfEdges R F)).Reachable p q) :
-- imply
  fkRectEulerHomologyDefect R (fkRectConfigurationOfEdges R (insert e F)) = fkRectEulerHomologyDefect R (fkRectConfigurationOfEdges R F) := by
-- proof
  apply StatMech.FrontierD.fkRectEulerHomologyDefect_insert_of_not_reachable R F e heF hedge hpq

/--
[fkRectEulerHomologyDefect_insert_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectEulerDefectInsertion.lean)
-/
@[path]
private lemma fkRectEulerHomologyDefect_insert_mono_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {e : R.EdgeIndex}
-- given
  (heF : e ∉ F) :
-- imply
  fkRectEulerHomologyDefect R (fkRectConfigurationOfEdges R F) ≤ fkRectEulerHomologyDefect R (fkRectConfigurationOfEdges R (insert e F)) := by
-- proof
  apply StatMech.FrontierD.fkRectEulerHomologyDefect_insert_mono R F e heF


-- created on 2026-10-23
