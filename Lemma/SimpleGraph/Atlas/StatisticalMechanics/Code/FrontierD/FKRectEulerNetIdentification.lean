import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectEulerNetIdentification
open Finset SimpleGraph StatMech StatMech.FrontierD


/--
[fkRectEulerHomologyDefect_eq_two_mul_netIndicator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectEulerNetIdentification.lean)
-/
@[path]
private lemma fkRectEulerHomologyDefect_eq_two_mul_netIndicator_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex} :
-- imply
  fkRectEulerHomologyDefect R (fkRectConfigurationOfEdges R F) = 2 * (fkRectNetIndicator R (fkRectConfigurationOfEdges R F) : Int) := by
-- proof
  apply StatMech.FrontierD.fkRectEulerHomologyDefect_eq_two_mul_netIndicator R F

/--
[fkRectEulerHomologyDefect_eq_two_iff_hasNet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectEulerNetIdentification.lean)
-/
@[path]
private lemma fkRectEulerHomologyDefect_eq_two_iff_hasNet_eq
  {R : FKRectTorus}
  {omega : R.Configuration} :
-- imply
  fkRectEulerHomologyDefect R omega = 2 ↔ FKRectHasNet R omega := by
-- proof
  apply StatMech.FrontierD.fkRectEulerHomologyDefect_eq_two_iff_hasNet R omega

/--
[fkRectEulerHomologyDefect_eq_two_mul_netIndicator_configuration](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectEulerNetIdentification.lean)
-/
@[path]
private lemma fkRectEulerHomologyDefect_eq_two_mul_netIndicator_configuration_eq
  {R : FKRectTorus}
  {omega : R.Configuration} :
-- imply
  fkRectEulerHomologyDefect R omega = 2 * (fkRectNetIndicator R omega : Int) := by
-- proof
  apply StatMech.FrontierD.fkRectEulerHomologyDefect_eq_two_mul_netIndicator_configuration R omega


-- created on 2026-10-23
