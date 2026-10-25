import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBlackOrbitRibbonParityCapstone
open StatMech StatMech.FrontierD


/--
[fkRectBlackOrbitFaithfulRibbonSubdivisionDart_valid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitRibbonParityCapstone.lean)
-/
@[path]
private lemma fkRectBlackOrbitFaithfulRibbonSubdivisionDart_valid_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {d : FKMedialBlackDart R.medialTorus} :
-- imply
  ∀ k, (fkRectBlackOrbitFaithfulRibbonSubdivisionDart R omega d k).1 = ons_dirStep (fkRectBlackOrbitRibbonSubdivisionSide R) (fkRectBlackOrbitFaithfulRibbonSubdivisionDart R omega d (k + 1)).2 (fkRectBlackOrbitFaithfulRibbonSubdivisionDart R omega d (k + 1)).1 := by
-- proof
  apply StatMech.FrontierD.fkRectBlackOrbitFaithfulRibbonSubdivisionDart_valid R omega d

/--
[fkRectBlackOrbitFaithfulRibbonSubdivisionDart_site_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitRibbonParityCapstone.lean)
-/
@[path]
private lemma fkRectBlackOrbitFaithfulRibbonSubdivisionDart_site_injective_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {d : FKMedialBlackDart R.medialTorus} :
-- imply
  Function.Injective (fun k => (fkRectBlackOrbitFaithfulRibbonSubdivisionDart R omega d k).1) := by
-- proof
  apply StatMech.FrontierD.fkRectBlackOrbitFaithfulRibbonSubdivisionDart_site_injective R omega d

/--
[fkRectBlackOrbitFaithfulRibbonSubdivisionDart_direction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitRibbonParityCapstone.lean)
-/
@[path]
private lemma fkRectBlackOrbitFaithfulRibbonSubdivisionDart_direction_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {d : FKMedialBlackDart R.medialTorus}
  {k : Fin (fkRectBlackOrbitRibbonSubdivisionWord R omega d).length} :
-- imply
  (fkRectBlackOrbitFaithfulRibbonSubdivisionDart R omega d k).2 = (fkRectBlackOrbitRibbonSubdivisionWord R omega d).get (-k) := by
-- proof
  apply StatMech.FrontierD.fkRectBlackOrbitFaithfulRibbonSubdivisionDart_direction R omega d k

/--
[fkRectBlackOrbitFaithfulRibbonSubdivisionDart_nonUturn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitRibbonParityCapstone.lean)
-/
@[path]
private lemma fkRectBlackOrbitFaithfulRibbonSubdivisionDart_nonUturn_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {d : FKMedialBlackDart R.medialTorus} :
-- imply
  ∀ k, (fkRectBlackOrbitFaithfulRibbonSubdivisionDart R omega d k).2 ≠ (fkRectBlackOrbitFaithfulRibbonSubdivisionDart R omega d (k + 1)).2 + 2 := by
-- proof
  apply StatMech.FrontierD.fkRectBlackOrbitFaithfulRibbonSubdivisionDart_nonUturn R omega d

/--
[fkRectBlackOrbitFaithfulRibbonSubdivisionDart_exponentX_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitRibbonParityCapstone.lean)
-/
@[path]
private lemma fkRectBlackOrbitFaithfulRibbonSubdivisionDart_exponentX_sum_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {d : FKMedialBlackDart R.medialTorus} :
-- imply
  let w := fkRectWalkWinding R (fkRectBlackBoundaryPrimalCycleWalk R omega d) (∑ k, ons_dirExponentX (fkRectBlackOrbitFaithfulRibbonSubdivisionDart R omega d k).2) = (fkRectBlackOrbitRibbonSubdivisionSide R : ℤ) * w.1 := by
-- proof
  apply StatMech.FrontierD.fkRectBlackOrbitFaithfulRibbonSubdivisionDart_exponentX_sum R omega d

/--
[fkRectBlackOrbitFaithfulRibbonSubdivisionDart_exponentY_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitRibbonParityCapstone.lean)
-/
@[path]
private lemma fkRectBlackOrbitFaithfulRibbonSubdivisionDart_exponentY_sum_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {d : FKMedialBlackDart R.medialTorus} :
-- imply
  let w := fkRectWalkWinding R (fkRectBlackBoundaryPrimalCycleWalk R omega d) (∑ k, ons_dirExponentY (fkRectBlackOrbitFaithfulRibbonSubdivisionDart R omega d k).2) = (fkRectBlackOrbitRibbonSubdivisionSide R : ℤ) * w.2 := by
-- proof
  apply StatMech.FrontierD.fkRectBlackOrbitFaithfulRibbonSubdivisionDart_exponentY_sum R omega d

/--
[fkRectBlackBoundaryPrimalCycleWinding_fst_odd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitRibbonParityCapstone.lean)
-/
@[path]
private lemma fkRectBlackBoundaryPrimalCycleWinding_fst_odd_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {d : FKMedialBlackDart R.medialTorus}
-- given
  (hy : (fkRectWalkWinding R (fkRectBlackBoundaryPrimalCycleWalk R omega d)).2 = 0)
  (hx : (fkRectWalkWinding R (fkRectBlackBoundaryPrimalCycleWalk R omega d)).1 ≠ 0) :
-- imply
  Odd (fkRectWalkWinding R (fkRectBlackBoundaryPrimalCycleWalk R omega d)).1 := by
-- proof
  apply StatMech.FrontierD.fkRectBlackBoundaryPrimalCycleWinding_fst_odd R omega d hy hx


-- created on 2026-10-23
