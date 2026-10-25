import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryCycleDuality.Part5
open Equiv SimpleGraph StatMech StatMech.FrontierD


/--
[fkMedialCheckerColor_dualShift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryCycleDuality.lean)
-/
@[path]
private lemma fkMedialCheckerColor_dualShift_eq
  {R : FKRectTorus}
  {d : FKMedialDart R.medialTorus} :
-- imply
  fkMedialCheckerColor (fkRectMedialDualShiftDart R d) = !fkMedialCheckerColor d := by
-- proof
  apply StatMech.FrontierD.fkMedialCheckerColor_dualShift R d

/--
[fkMedialCheckerColor_dualUnshift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryCycleDuality.lean)
-/
@[path]
private lemma fkMedialCheckerColor_dualUnshift_eq
  {R : FKRectTorus}
  {d : FKMedialDart R.medialTorus} :
-- imply
  fkMedialCheckerColor (fkRectMedialDualUnshiftDart R d) = !fkMedialCheckerColor d := by
-- proof
  apply StatMech.FrontierD.fkMedialCheckerColor_dualUnshift R d

/--
[fkRectDualBlackDartEquiv_reachable_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryCycleDuality.lean)
-/
@[path]
private lemma fkRectDualBlackDartEquiv_reachable_iff_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {d e : FKMedialBlackDart R.medialTorus} :
-- imply
  (fkMedialLoopGraph R.medialTorus (fkRectConfigurationToMedialPairing R (fkRectDualConfigurationEquiv R omega))).Reachable ((fkRectDualBlackDartEquiv R omega d).1) ((fkRectDualBlackDartEquiv R omega e).1) ↔ (fkMedialLoopGraph R.medialTorus (fkRectConfigurationToMedialPairing R omega)).Reachable d.1 e.1 := by
-- proof
  apply StatMech.FrontierD.fkRectDualBlackDartEquiv_reachable_iff R omega d e

/--
[fkRectBlackBoundaryCycleDualEquiv_mk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryCycleDuality.lean)
-/
@[path]
private lemma fkRectBlackBoundaryCycleDualEquiv_mk_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {d : FKMedialBlackDart R.medialTorus} :
-- imply
  fkRectBlackBoundaryCycleDualEquiv R omega (Quot.mk _ d) = Quot.mk _ (fkRectDualBlackDartEquiv R omega d) := by
-- proof
  apply StatMech.FrontierD.fkRectBlackBoundaryCycleDualEquiv_mk R omega d

/--
[fkMedialBoundaryStep_sameCycle_dualShift_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryCycleDuality.lean)
-/
@[path]
private lemma fkMedialBoundaryStep_sameCycle_dualShift_iff_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {d e : FKMedialDart R.medialTorus} :
-- imply
  (fkMedialBoundaryStep (fkRectConfigurationToMedialPairing R (fkRectDualConfigurationEquiv R omega))).SameCycle (fkRectMedialDualShiftDart R d) (fkRectMedialDualShiftDart R e) ↔ (fkMedialBoundaryStep (fkRectConfigurationToMedialPairing R omega)).SameCycle d e := by
-- proof
  apply StatMech.FrontierD.fkMedialBoundaryStep_sameCycle_dualShift_iff R omega d e

/--
[fkMedialBoundaryStep_mem_support_dualShift_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryCycleDuality.lean)
-/
@[path]
private lemma fkMedialBoundaryStep_mem_support_dualShift_iff_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {d : FKMedialDart R.medialTorus} :
-- imply
  fkRectMedialDualShiftDart R d ∈ (fkMedialBoundaryStep (fkRectConfigurationToMedialPairing R (fkRectDualConfigurationEquiv R omega))).support ↔ d ∈ (fkMedialBoundaryStep (fkRectConfigurationToMedialPairing R omega)).support := by
-- proof
  apply StatMech.FrontierD.fkMedialBoundaryStep_mem_support_dualShift_iff R omega d

/--
[fkRectMedialBoundaryPrimalSeamTrace_toList_eq_cycleClass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryCycleDuality.lean)
-/
@[path]
private lemma fkRectMedialBoundaryPrimalSeamTrace_toList_eq_cycleClass_eq
  {R : FKRectTorus}
  {pairing : FKMedialLoopPairing R.medialTorus}
  {d : FKMedialDart R.medialTorus}
-- given
  (hd : d ∈ (fkMedialBoundaryStep pairing).support) :
-- imply
  fkRectMedialBoundaryPrimalSeamTrace R pairing d ((fkMedialBoundaryStep pairing).toList d).length = fkRectBoundaryCycleClassWinding R pairing d := by
-- proof
  apply StatMech.FrontierD.fkRectMedialBoundaryPrimalSeamTrace_toList_eq_cycleClass R pairing d hd

/--
[fkMedialBoundaryStep_toList_length_dualShift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryCycleDuality.lean)
-/
@[path]
private lemma fkMedialBoundaryStep_toList_length_dualShift_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {d : FKMedialDart R.medialTorus} :
-- imply
  ((fkMedialBoundaryStep (fkRectConfigurationToMedialPairing R (fkRectDualConfigurationEquiv R omega))).toList (fkRectMedialDualShiftDart R d)).length = ((fkMedialBoundaryStep (fkRectConfigurationToMedialPairing R omega)).toList d).length := by
-- proof
  apply StatMech.FrontierD.fkMedialBoundaryStep_toList_length_dualShift R omega d

/--
[fkRectBoundaryCycleClassWinding_dualShift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryCycleDuality.lean)
-/
@[path]
private lemma fkRectBoundaryCycleClassWinding_dualShift_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {d : FKMedialBlackDart R.medialTorus} :
-- imply
  fkRectBoundaryCycleClassWinding R (fkRectConfigurationToMedialPairing R (fkRectDualConfigurationEquiv R omega)) (fkRectMedialDualShiftDart R d.1) = fkRectBoundaryCycleClassWinding R (fkRectConfigurationToMedialPairing R omega) d.1 := by
-- proof
  apply StatMech.FrontierD.fkRectBoundaryCycleClassWinding_dualShift R omega d

/--
[fkRectBlackBoundaryCycleWinding_dualEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryCycleDuality.lean)
-/
@[path]
private lemma fkRectBlackBoundaryCycleWinding_dualEquiv_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {C : FKRectConfigurationBlackBoundaryCycle R omega} :
-- imply
  fkRectBlackBoundaryCycleWinding R (fkRectDualConfigurationEquiv R omega) (fkRectBlackBoundaryCycleDualEquiv R omega C) = -fkRectBlackBoundaryCycleWinding R omega C := by
-- proof
  apply StatMech.FrontierD.fkRectBlackBoundaryCycleWinding_dualEquiv R omega C

/--
[fkRectBlackBoundaryCycleInPrimalCluster_iff_primalComponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryCycleDuality.lean)
-/
@[path]
private lemma fkRectBlackBoundaryCycleInPrimalCluster_iff_primalComponent_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {x : R.Vertex}
  {C : FKRectConfigurationBlackBoundaryCycle R omega} :
-- imply
  fkRectBlackBoundaryCycleInPrimalCluster R omega x C ↔ fkRectBlackBoundaryCyclePrimalComponent R omega C = (fkRectOpenGraph R omega).connectedComponentMk x := by
-- proof
  apply StatMech.FrontierD.fkRectBlackBoundaryCycleInPrimalCluster_iff_primalComponent R omega x C

/--
[fkRectDualClusterBoundaryCycleWindingSum_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryCycleDuality.lean)
-/
@[path]
private lemma fkRectDualClusterBoundaryCycleWindingSum_eq_zero_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {L : (fkRectOpenGraph R (fkRectDualConfigurationEquiv R omega)).ConnectedComponent} :
-- imply
  fkRectDualClusterBoundaryCycleWindingSum R omega L = 0 := by
-- proof
  apply StatMech.FrontierD.fkRectDualClusterBoundaryCycleWindingSum_eq_zero R omega L


-- created on 2026-10-23
