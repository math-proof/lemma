import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBlackOrbitRibbonSubdivisionWordLookup
open StatMech StatMech.FrontierD


/--
[fkRectBlackOrbitRibbonSubdivisionWord_get_index](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitRibbonSubdivisionWordLookup.lean)
-/
@[path]
private lemma fkRectBlackOrbitRibbonSubdivisionWord_get_index_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {d : FKMedialBlackDart R.medialTorus}
  {i : Fin (fkRectBlackOrbitMedialRibbonWord R omega d).length}
  {r : Fin (onsAnisotropicStepScale (8 * R.medialTorus.width) (8 * R.medialTorus.height) (fkRectBlackOrbitMedialRibbonFlatDirection R omega d i))} :
-- imply
  (fkRectBlackOrbitRibbonSubdivisionWord R omega d).get ((fkRectBlackOrbitRibbonSubdivisionIndexEquiv R omega d).symm ⟨i, r⟩) = (fkRectBlackOrbitMedialRibbonWord R omega d).get i := by
-- proof
  apply StatMech.FrontierD.fkRectBlackOrbitRibbonSubdivisionWord_get_index R omega d i r


-- created on 2026-10-23
