import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCutPushforward.Part2
open Finset StatMech StatMech.FrontierD


/--
[fkRectHorizontalCutClosedConfiguration_force](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCutPushforward.lean)
-/
@[path]
private lemma fkRectHorizontalCutClosedConfiguration_force_eq
  {R : FKRectTorus}
  {omega : R.Configuration} :
-- imply
  FKRectHorizontalCutClosedConfiguration R (fkRectForceHorizontalCutClosed R omega) := by
-- proof
  apply StatMech.FrontierD.fkRectHorizontalCutClosedConfiguration_force R omega

/--
[fkRectCriticalEventMass_horizontalCutClosed_eq_closedMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCutPushforward.lean)
-/
@[path]
private lemma fkRectCriticalEventMass_horizontalCutClosed_eq_closedMass_eq
  {R : FKRectTorus}
  {q : Real} :
-- imply
  fkRectCriticalEventMass R q {eta | FKRectHorizontalCutClosedConfiguration R eta} = fkRectCriticalClosedMass R q (fkRectHorizontalCutEdges R) := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalEventMass_horizontalCutClosed_eq_closedMass R q

/--
[fkRectCriticalClosedMass_horizontalCut_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCutPushforward.lean)
-/
@[path]
private lemma fkRectCriticalClosedMass_horizontalCut_pos_eq
  {R : FKRectTorus}
  {q : Real}
-- given
  (hq : 1 <= q) :
-- imply
  0 < fkRectCriticalClosedMass R q (fkRectHorizontalCutEdges R) := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalClosedMass_horizontalCut_pos R hq

/--
[fkRectCriticalClosedMass_horizontalCut_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCutPushforward.lean)
-/
@[path]
private lemma fkRectCriticalClosedMass_horizontalCut_le_one_eq
  {R : FKRectTorus}
  {q : Real}
-- given
  (hq : 1 <= q) :
-- imply
  fkRectCriticalClosedMass R q (fkRectHorizontalCutEdges R) <= 1 := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalClosedMass_horizontalCut_le_one R hq

/--
[fkRectCriticalHorizontalCutEventMass_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCutPushforward.lean)
-/
@[path]
private lemma fkRectCriticalHorizontalCutEventMass_nonneg_eq
  {R : FKRectTorus}
  {q : Real}
  {A : Set R.Configuration}
-- given
  (hq : 1 <= q) :
-- imply
  0 <= fkRectCriticalHorizontalCutEventMass R q A := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalHorizontalCutEventMass_nonneg R hq A

/--
[closedMass_mul_fkRectCriticalHorizontalCutEventMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCutPushforward.lean)
-/
@[path]
private lemma closedMass_mul_fkRectCriticalHorizontalCutEventMass_eq
  {R : FKRectTorus}
  {q : Real}
  {A : Set R.Configuration}
-- given
  (hq : 1 <= q) :
-- imply
  fkRectCriticalClosedMass R q (fkRectHorizontalCutEdges R) * fkRectCriticalHorizontalCutEventMass R q A = fkRectCriticalEventMass R q {eta | FKRectHorizontalCutClosedConfiguration R eta ∧ eta ∈ A} := by
-- proof
  apply StatMech.FrontierD.closedMass_mul_fkRectCriticalHorizontalCutEventMass R hq A

/--
[fkRectCritical_horizontalCutPushforward_event](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCutPushforward.lean)
-/
@[path]
private lemma fkRectCritical_horizontalCutPushforward_event_eq
  {R : FKRectTorus}
  {q : Real}
  {A : Set R.Configuration}
-- given
  (hq : 1 <= q) :
-- imply
  FK.cFE (fkRectCriticalP q) q ^ (2 * R.width) * fkRectCriticalEventMass R q (fkRectForceHorizontalCutClosed R ⁻¹' A) <= fkRectCriticalEventMass R q A := by
-- proof
  apply StatMech.FrontierD.fkRectCritical_horizontalCutPushforward_event R hq A

/--
[fkRectCritical_eventMass_le_horizontalCutEventMass_of_force](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCutPushforward.lean)
-/
@[path]
private lemma fkRectCritical_eventMass_le_horizontalCutEventMass_of_force_eq
  {R : FKRectTorus}
  {q : Real}
  {Source Target : Set R.Configuration}
-- given
  (hq : 1 <= q)
  (hforce : ∀ omega, omega ∈ Source -> fkRectForceHorizontalCutClosed R omega ∈ Target) :
-- imply
  FK.cFE (fkRectCriticalP q) q ^ (2 * R.width) * fkRectCriticalEventMass R q Source <= fkRectCriticalHorizontalCutEventMass R q Target := by
-- proof
  apply StatMech.FrontierD.fkRectCritical_eventMass_le_horizontalCutEventMass_of_force R hq Source Target hforce


-- created on 2026-10-23
