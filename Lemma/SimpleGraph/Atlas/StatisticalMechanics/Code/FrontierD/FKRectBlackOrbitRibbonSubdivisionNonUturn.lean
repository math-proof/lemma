import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.FKRectBlackOrbitRibbonSubdivisionNonUturn
open StatMech StatMech.FrontierD


/--
[fkRectBlackOrbitRibbonSubdivisionDirection_nonUturn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitRibbonSubdivisionNonUturn.lean)
-/
@[path]
private lemma fkRectBlackOrbitRibbonSubdivisionDirection_nonUturn_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {d : FKMedialBlackDart R.medialTorus}
  {k : Fin (fkRectBlackOrbitRibbonSubdivisionWord R omega d).length} :
-- imply
  fkRectBlackOrbitMedialRibbonFlatDirection R omega d (fkRectBlackOrbitRibbonSubdivisionIndexEquiv R omega d (k + 1)).1 ≠ fkRectBlackOrbitMedialRibbonFlatDirection R omega d (fkRectBlackOrbitRibbonSubdivisionIndexEquiv R omega d k).1 + 2 := by
-- proof
  apply StatMech.FrontierD.fkRectBlackOrbitRibbonSubdivisionDirection_nonUturn R omega d k


-- created on 2026-10-23
