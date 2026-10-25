import Mathlib
import sympy.Basic
import Def.StatisticalMechanics.Code.FrontierD.FKRectMedialBoundaryWalk.Part2
open SimpleGraph StatMech StatMech.FrontierD


/--
[fkRectMedialDartPrimalLabel_localMate_eq_or_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialBoundaryWalk.lean)
-/
@[path]
private lemma fkRectMedialDartPrimalLabel_localMate_eq_or_adj_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {d : FKMedialDart R.medialTorus} :
-- imply
  fkRectMedialDartPrimalLabel R d = fkRectMedialDartPrimalLabel R (fkMedialLocalMate (fkRectConfigurationToMedialPairing R omega) d) ∨ (fkRectOpenGraph R omega).Adj (fkRectMedialDartPrimalLabel R d) (fkRectMedialDartPrimalLabel R (fkMedialLocalMate (fkRectConfigurationToMedialPairing R omega) d)) := by
-- proof
  apply StatMech.FrontierD.fkRectMedialDartPrimalLabel_localMate_eq_or_adj R omega d

/--
[fkRectMedialDartPrimalLabel_boundaryStep_eq_or_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialBoundaryWalk.lean)
-/
@[path]
private lemma fkRectMedialDartPrimalLabel_boundaryStep_eq_or_adj_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {d : FKMedialDart R.medialTorus} :
-- imply
  fkRectMedialDartPrimalLabel R d = fkRectMedialDartPrimalLabel R (fkMedialBoundaryStep (fkRectConfigurationToMedialPairing R omega) d) ∨ (fkRectOpenGraph R omega).Adj (fkRectMedialDartPrimalLabel R d) (fkRectMedialDartPrimalLabel R (fkMedialBoundaryStep (fkRectConfigurationToMedialPairing R omega) d)) := by
-- proof
  apply StatMech.FrontierD.fkRectMedialDartPrimalLabel_boundaryStep_eq_or_adj R omega d

/--
[fkRectMedialBoundaryPrimalStepWalk_length_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialBoundaryWalk.lean)
-/
@[path]
private lemma fkRectMedialBoundaryPrimalStepWalk_length_le_one_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {d : FKMedialDart R.medialTorus} :
-- imply
  (fkRectMedialBoundaryPrimalStepWalk R omega d).length ≤ 1 := by
-- proof
  apply StatMech.FrontierD.fkRectMedialBoundaryPrimalStepWalk_length_le_one R omega d


-- created on 2026-10-23
