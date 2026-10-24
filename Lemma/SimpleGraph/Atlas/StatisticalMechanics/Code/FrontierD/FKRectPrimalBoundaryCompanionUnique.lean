import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.FKRectPrimalBoundaryCompanionUnique
open StatMech StatMech.FrontierD


/--
[fkRectPrimalBoundaryCompanionUnique_of_card_nonzero_le_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalBoundaryCompanionUnique.lean)
-/
@[path]
private lemma fkRectPrimalBoundaryCompanionUnique_of_card_nonzero_le_two_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
-- given
  (hcard : forall x : R.Vertex, (fkRectPrimalClusterNonzeroBoundaryCycles R omega x).card <= 2) :
-- imply
  FKRectPrimalBoundaryCompanionUnique R omega := by
-- proof
  apply StatMech.FrontierD.fkRectPrimalBoundaryCompanionUnique_of_card_nonzero_le_two R omega hcard

/--
[card_fkRectPrimalClusterNonzeroBoundaryCycles_le_two_of_companionUnique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalBoundaryCompanionUnique.lean)
-/
@[path]
private lemma card_fkRectPrimalClusterNonzeroBoundaryCycles_le_two_of_companionUnique_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {x : R.Vertex}
-- given
  (hunique : FKRectPrimalBoundaryCompanionUnique R omega) :
-- imply
  (fkRectPrimalClusterNonzeroBoundaryCycles R omega x).card <= 2 := by
-- proof
  apply StatMech.FrontierD.card_fkRectPrimalClusterNonzeroBoundaryCycles_le_two_of_companionUnique R omega hunique x

/--
[card_nonzero_le_two_iff_primalBoundaryCompanionUnique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalBoundaryCompanionUnique.lean)
-/
@[path]
private lemma card_nonzero_le_two_iff_primalBoundaryCompanionUnique_eq
  {R : FKRectTorus}
  {omega : R.Configuration} :
-- imply
  (forall x : R.Vertex, (fkRectPrimalClusterNonzeroBoundaryCycles R omega x).card <= 2) ↔ FKRectPrimalBoundaryCompanionUnique R omega := by
-- proof
  apply StatMech.FrontierD.card_nonzero_le_two_iff_primalBoundaryCompanionUnique R omega


-- created on 2026-10-23
