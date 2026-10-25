import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBlackOrbitRibbonSubdivisionCodeInjective
open StatMech StatMech.FrontierD


/--
[fkRectBlackOrbitRibbonSubdivisionCode_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitRibbonSubdivisionCodeInjective.lean)
-/
@[path]
private lemma fkRectBlackOrbitRibbonSubdivisionCode_injective_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {d : FKMedialBlackDart R.medialTorus} :
-- imply
  Function.Injective (fkRectBlackOrbitRibbonSubdivisionCode R omega d) := by
-- proof
  apply StatMech.FrontierD.fkRectBlackOrbitRibbonSubdivisionCode_injective R omega d


-- created on 2026-10-23
