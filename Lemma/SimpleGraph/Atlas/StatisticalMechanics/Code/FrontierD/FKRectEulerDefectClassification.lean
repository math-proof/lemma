import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectEulerDefectClassification
open Finset StatMech StatMech.FrontierD


/--
[fkRectEulerHomologyDefect_mono_configurationOfEdges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectEulerDefectClassification.lean)
-/
@[path]
private lemma fkRectEulerHomologyDefect_mono_configurationOfEdges_eq
  {R : FKRectTorus}
  {F A : Finset R.EdgeIndex}
-- given
  (hFA : F ⊆ A) :
-- imply
  fkRectEulerHomologyDefect R (fkRectConfigurationOfEdges R F) ≤ fkRectEulerHomologyDefect R (fkRectConfigurationOfEdges R A) := by
-- proof
  apply StatMech.FrontierD.fkRectEulerHomologyDefect_mono_configurationOfEdges R hFA

/--
[fkRectEulerHomologyDefect_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectEulerDefectClassification.lean)
-/
@[path]
private lemma fkRectEulerHomologyDefect_even_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex} :
-- imply
  Even (fkRectEulerHomologyDefect R (fkRectConfigurationOfEdges R F)) := by
-- proof
  apply StatMech.FrontierD.fkRectEulerHomologyDefect_even R F

/--
[fkRectEulerHomologyDefect_classified](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectEulerDefectClassification.lean)
-/
@[path]
private lemma fkRectEulerHomologyDefect_classified_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex} :
-- imply
  fkRectEulerHomologyDefect R (fkRectConfigurationOfEdges R F) = 0 ∨ fkRectEulerHomologyDefect R (fkRectConfigurationOfEdges R F) = 2 := by
-- proof
  apply StatMech.FrontierD.fkRectEulerHomologyDefect_classified R F


-- created on 2026-10-23
