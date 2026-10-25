import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBlackOrbitRibbonPrimitive
open StatMech StatMech.FrontierD


/--
[fkRectBlackBoundaryPrimalCycleWinding_primitive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitRibbonPrimitive.lean)
-/
@[path]
private lemma fkRectBlackBoundaryPrimalCycleWinding_primitive_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {d : FKMedialBlackDart R.medialTorus}
-- given
  (hnonzero : fkRectWalkWinding R (fkRectBlackBoundaryPrimalCycleWalk R omega d) ≠ (0, 0)) :
-- imply
  FKRectPrimitiveWinding (fkRectWalkWinding R (fkRectBlackBoundaryPrimalCycleWalk R omega d)) := by
-- proof
  apply StatMech.FrontierD.fkRectBlackBoundaryPrimalCycleWinding_primitive R omega d hnonzero

/--
[fkRectBlackBoundaryPrimalCycleWinding_primitive_of_snd_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitRibbonPrimitive.lean)
-/
@[path]
private lemma fkRectBlackBoundaryPrimalCycleWinding_primitive_of_snd_pos_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {d : FKMedialBlackDart R.medialTorus}
-- given
  (hpos : 0 < (fkRectWalkWinding R (fkRectBlackBoundaryPrimalCycleWalk R omega d)).2) :
-- imply
  FKRectPrimitiveWinding (fkRectWalkWinding R (fkRectBlackBoundaryPrimalCycleWalk R omega d)) := by
-- proof
  apply StatMech.FrontierD.fkRectBlackBoundaryPrimalCycleWinding_primitive_of_snd_pos R omega d hpos


-- created on 2026-10-23
