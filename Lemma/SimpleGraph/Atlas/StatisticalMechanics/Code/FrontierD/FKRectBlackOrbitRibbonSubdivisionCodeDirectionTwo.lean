import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.FKRectBlackOrbitRibbonSubdivisionCodeDirectionTwo
open StatMech StatMech.FrontierD


/--
[fkRectBlackOrbitRibbonSubdivisionCode_eq_of_direction_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitRibbonSubdivisionCodeDirectionTwo.lean)
-/
@[path]
private lemma fkRectBlackOrbitRibbonSubdivisionCode_eq_of_direction_two_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {d : FKMedialBlackDart R.medialTorus}
  {z w : FKRectBlackOrbitRibbonSubdivisionIndex R omega d}
-- given
  (hz : fkRectBlackOrbitMedialRibbonFlatDirection R omega d z.1 = 2)
  (h : fkRectBlackOrbitRibbonSubdivisionCode R omega d z = fkRectBlackOrbitRibbonSubdivisionCode R omega d w) :
-- imply
  z = w := by
-- proof
  apply StatMech.FrontierD.fkRectBlackOrbitRibbonSubdivisionCode_eq_of_direction_two R omega d z w hz h


-- created on 2026-10-23
