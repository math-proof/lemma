import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusSurfaceReduction
open Finset SimpleGraph StatMech StatMech.FrontierD


/--
[fkRectConnectedInsertionSurfaceBridge_iff_defectJump_iff_hasNet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusSurfaceReduction.lean)
-/
@[path]
private lemma fkRectConnectedInsertionSurfaceBridge_iff_defectJump_iff_hasNet_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {e : R.EdgeIndex}
  {r : (fkRectOpenGraph R (fkRectConfigurationOfEdges R F)).Walk (fkRectMedialWestPrimal R e) (fkRectMedialEastPrimal R e)}
-- given
  (heF : e ∉ F)
  (hold : ¬ FKRectHasNet R (fkRectConfigurationOfEdges R F)) :
-- imply
  FKRectConnectedInsertionSurfaceBridge R F e r heF hold ↔ (fkRectEulerHomologyDefect R (fkRectConfigurationOfEdges R (insert e F)) = fkRectEulerHomologyDefect R (fkRectConfigurationOfEdges R F) + 2 ↔ FKRectHasNet R (fkRectConfigurationOfEdges R (insert e F))) := by
-- proof
  apply StatMech.FrontierD.fkRectConnectedInsertionSurfaceBridge_iff_defectJump_iff_hasNet R F e heF r hold

/--
[fkRectEulerHomologyDefect_insert_eq_add_two_iff_hasNet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusSurfaceReduction.lean)
-/
@[path]
private lemma fkRectEulerHomologyDefect_insert_eq_add_two_iff_hasNet_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {e : R.EdgeIndex}
  {r : (fkRectOpenGraph R (fkRectConfigurationOfEdges R F)).Walk (fkRectMedialWestPrimal R e) (fkRectMedialEastPrimal R e)}
-- given
  (heF : e ∉ F)
  (hold : ¬ FKRectHasNet R (fkRectConfigurationOfEdges R F))
  (hsurface : FKRectConnectedInsertionSurfaceBridge R F e r heF hold) :
-- imply
  fkRectEulerHomologyDefect R (fkRectConfigurationOfEdges R (insert e F)) = fkRectEulerHomologyDefect R (fkRectConfigurationOfEdges R F) + 2 ↔ FKRectHasNet R (fkRectConfigurationOfEdges R (insert e F)) := by
-- proof
  apply StatMech.FrontierD.fkRectEulerHomologyDefect_insert_eq_add_two_iff_hasNet R F e heF r hold hsurface

/--
[fkRectEulerHomologyDefect_insert_eq_two_iff_hasNet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusSurfaceReduction.lean)
-/
@[path]
private lemma fkRectEulerHomologyDefect_insert_eq_two_iff_hasNet_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {e : R.EdgeIndex}
  {r : (fkRectOpenGraph R (fkRectConfigurationOfEdges R F)).Walk (fkRectMedialWestPrimal R e) (fkRectMedialEastPrimal R e)}
-- given
  (heF : e ∉ F)
  (hzero : fkRectEulerHomologyDefect R (fkRectConfigurationOfEdges R F) = 0)
  (hold : ¬ FKRectHasNet R (fkRectConfigurationOfEdges R F))
  (hsurface : FKRectConnectedInsertionSurfaceBridge R F e r heF hold) :
-- imply
  fkRectEulerHomologyDefect R (fkRectConfigurationOfEdges R (insert e F)) = 2 ↔ FKRectHasNet R (fkRectConfigurationOfEdges R (insert e F)) := by
-- proof
  apply StatMech.FrontierD.fkRectEulerHomologyDefect_insert_eq_two_iff_hasNet R F e heF r hzero hold hsurface


-- created on 2026-10-23
