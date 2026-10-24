import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.FKRectBlackOrbitRibbonSubdivisionCodeDirectionZero
open StatMech StatMech.FrontierD


/--
[fkRectBlackOrbitRibbonSubdivisionCode_eq_of_directions_zero_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitRibbonSubdivisionCodeDirectionZero.lean)
-/
@[path]
private lemma fkRectBlackOrbitRibbonSubdivisionCode_eq_of_directions_zero_zero_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {d : FKMedialBlackDart R.medialTorus}
  {z w : FKRectBlackOrbitRibbonSubdivisionIndex R omega d}
-- given
  (hz : fkRectBlackOrbitMedialRibbonFlatDirection R omega d z.1 = 0)
  (hw : fkRectBlackOrbitMedialRibbonFlatDirection R omega d w.1 = 0)
  (h : fkRectBlackOrbitRibbonSubdivisionCode R omega d z = fkRectBlackOrbitRibbonSubdivisionCode R omega d w) :
-- imply
  z = w := by
-- proof
  apply StatMech.FrontierD.fkRectBlackOrbitRibbonSubdivisionCode_eq_of_directions_zero_zero R omega d z w hz hw h

/--
[fkRectBlackOrbitRibbonSubdivisionCode_eq_of_direction_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitRibbonSubdivisionCodeDirectionZero.lean)
-/
@[path]
private lemma fkRectBlackOrbitRibbonSubdivisionCode_eq_of_direction_zero_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {d : FKMedialBlackDart R.medialTorus}
  {z w : FKRectBlackOrbitRibbonSubdivisionIndex R omega d}
-- given
  (hz : fkRectBlackOrbitMedialRibbonFlatDirection R omega d z.1 = 0)
  (h : fkRectBlackOrbitRibbonSubdivisionCode R omega d z = fkRectBlackOrbitRibbonSubdivisionCode R omega d w) :
-- imply
  z = w := by
-- proof
  apply StatMech.FrontierD.fkRectBlackOrbitRibbonSubdivisionCode_eq_of_direction_zero R omega d z w hz h


-- created on 2026-10-23
