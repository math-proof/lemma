import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.FKRectBlackOrbitRibbonSubdivisionCodeDirectionThree
open StatMech StatMech.FrontierD


/--
[fkRectBlackOrbitRibbonSubdivisionCode_eq_of_direction_three](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitRibbonSubdivisionCodeDirectionThree.lean)
-/
@[path]
private lemma fkRectBlackOrbitRibbonSubdivisionCode_eq_of_direction_three_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {d : FKMedialBlackDart R.medialTorus}
  {z w : FKRectBlackOrbitRibbonSubdivisionIndex R omega d}
-- given
  (hz : fkRectBlackOrbitMedialRibbonFlatDirection R omega d z.1 = 3)
  (h : fkRectBlackOrbitRibbonSubdivisionCode R omega d z = fkRectBlackOrbitRibbonSubdivisionCode R omega d w) :
-- imply
  z = w := by
-- proof
  apply StatMech.FrontierD.fkRectBlackOrbitRibbonSubdivisionCode_eq_of_direction_three R omega d z w hz h


-- created on 2026-10-23
