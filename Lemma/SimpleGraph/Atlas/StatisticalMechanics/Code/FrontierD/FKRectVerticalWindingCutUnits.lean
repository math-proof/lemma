import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.FKRectVerticalWindingCutUnits
open Finset SimpleGraph StatMech StatMech.FrontierD


/--
[card_fkRectPositiveBoundaryUnit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectVerticalWindingCutUnits.lean)
-/
@[path]
private lemma card_fkRectPositiveBoundaryUnit_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {K : (fkRectOpenGraph R omega).ConnectedComponent} :
-- imply
  Fintype.card (FKRectPositiveBoundaryUnit R omega K) = fkRectPrimalComponentPositiveBoundaryVerticalMass R omega K := by
-- proof
  apply StatMech.FrontierD.card_fkRectPositiveBoundaryUnit R omega K

/--
[FKRectPositiveBoundaryUnit.component](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectVerticalWindingCutUnits.lean)
-/
@[path]
private lemma component_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {K : (fkRectOpenGraph R omega).ConnectedComponent}
  {u : FKRectPositiveBoundaryUnit R omega K} :
-- imply
  fkRectBlackBoundaryCyclePrimalComponent R omega u.1 = K := by
-- proof
  apply StatMech.FrontierD.FKRectPositiveBoundaryUnit.component R omega K u

/--
[FKRectPositiveBoundaryUnit.winding_snd_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectVerticalWindingCutUnits.lean)
-/
@[path]
private lemma winding_snd_pos_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {K : (fkRectOpenGraph R omega).ConnectedComponent}
  {u : FKRectPositiveBoundaryUnit R omega K} :
-- imply
  0 < (fkRectBlackBoundaryCycleWinding R omega u.1).2 := by
-- proof
  apply StatMech.FrontierD.FKRectPositiveBoundaryUnit.winding_snd_pos R omega K u

/--
[card_fkRectHorizontalCutCrossingInFiber](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectVerticalWindingCutUnits.lean)
-/
@[path]
private lemma card_fkRectHorizontalCutCrossingInFiber_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {K : (fkRectOpenGraph R omega).ConnectedComponent} :
-- imply
  Fintype.card (FKRectHorizontalCutCrossingInFiber R omega K) = fkRectPrimalComponentHorizontalCutCrossingCount R omega K := by
-- proof
  apply StatMech.FrontierD.card_fkRectHorizontalCutCrossingInFiber R omega K

/--
[positiveBoundaryMass_le_crossingCount_iff_nonempty_embedding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectVerticalWindingCutUnits.lean)
-/
@[path]
private lemma positiveBoundaryMass_le_crossingCount_iff_nonempty_embedding_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {K : (fkRectOpenGraph R omega).ConnectedComponent} :
-- imply
  fkRectPrimalComponentPositiveBoundaryVerticalMass R omega K ≤ fkRectPrimalComponentHorizontalCutCrossingCount R omega K ↔ Nonempty (FKRectPositiveBoundaryUnit R omega K ↪ FKRectHorizontalCutCrossingInFiber R omega K) := by
-- proof
  apply StatMech.FrontierD.positiveBoundaryMass_le_crossingCount_iff_nonempty_embedding R omega K

/--
[rankOnePositiveBoundaryCutFiberBound_iff_unitEmbedding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectVerticalWindingCutUnits.lean)
-/
@[path]
private lemma rankOnePositiveBoundaryCutFiberBound_iff_unitEmbedding_eq
  {R : FKRectTorus}
  {omega : R.Configuration} :
-- imply
  FKRectRankOnePositiveVerticalBoundaryCutFiberBound R omega ↔ ∀ K : (fkRectOpenGraph R omega).ConnectedComponent, ¬ FKRectPrimalComponentHasNet R omega K → Nonempty (FKRectPositiveBoundaryUnit R omega K ↪ FKRectHorizontalCutCrossingInFiber R omega K) := by
-- proof
  apply StatMech.FrontierD.rankOnePositiveBoundaryCutFiberBound_iff_unitEmbedding R omega


-- created on 2026-10-23
