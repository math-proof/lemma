import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.FKRectBlackOrbitRibbonSubdivisionGeometry
open StatMech StatMech.FrontierD


/--
[fkRectBlackOrbitRibbonSubdivisionWord_get](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitRibbonSubdivisionGeometry.lean)
-/
@[path]
private lemma fkRectBlackOrbitRibbonSubdivisionWord_get_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {d : FKMedialBlackDart R.medialTorus}
  {k : Fin (fkRectBlackOrbitRibbonSubdivisionWord R omega d).length} :
-- imply
  (fkRectBlackOrbitRibbonSubdivisionWord R omega d).get k = fkRectBlackOrbitMedialRibbonFlatDirection R omega d (fkRectBlackOrbitRibbonSubdivisionIndexEquiv R omega d k).1 := by
-- proof
  apply StatMech.FrontierD.fkRectBlackOrbitRibbonSubdivisionWord_get R omega d k


-- created on 2026-10-23
