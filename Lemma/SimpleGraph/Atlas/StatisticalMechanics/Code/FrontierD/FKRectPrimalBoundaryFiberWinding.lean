import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.FKRectPrimalBoundaryFiberWinding
open Equiv Finset SimpleGraph StatMech StatMech.FrontierD


/--
[fkRectBlackDart01_primalLabels](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalBoundaryFiberWinding.lean)
-/
@[path]
private lemma fkRectBlackDart01_primalLabels_eq
  {R : FKRectTorus}
  {v : R.medialTorus.Vertex} :
-- imply
  s(fkRectMedialDartPrimalLabel R (fkMedialBlackDart0 v).1, fkRectMedialDartPrimalLabel R (fkMedialBlackDart1 v).1) = fkRectTorusIndexedEdge R (fkRectTorusMedialEdgeEquiv R v) := by
-- proof
  apply StatMech.FrontierD.fkRectBlackDart01_primalLabels R v

/--
[fkRectBlackDart01_primalLabels_reachable_of_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalBoundaryFiberWinding.lean)
-/
@[path]
private lemma fkRectBlackDart01_primalLabels_reachable_of_open_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {v : R.medialTorus.Vertex}
-- given
  (hopen : omega (fkRectTorusMedialEdgeEquiv R v) = true) :
-- imply
  (fkRectOpenGraph R omega).Reachable (fkRectMedialDartPrimalLabel R (fkMedialBlackDart0 v).1) (fkRectMedialDartPrimalLabel R (fkMedialBlackDart1 v).1) := by
-- proof
  apply StatMech.FrontierD.fkRectBlackDart01_primalLabels_reachable_of_open R omega v hopen

/--
[fkRectBlackBoundaryWeight_dart0_add_dart1_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalBoundaryFiberWinding.lean)
-/
@[path]
private lemma fkRectBlackBoundaryWeight_dart0_add_dart1_eq_zero_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {v : R.medialTorus.Vertex} :
-- imply
  fkRectBlackBoundaryWeight R (fkRectConfigurationToMedialPairing R omega) (fkMedialBlackDart0 v) + fkRectBlackBoundaryWeight R (fkRectConfigurationToMedialPairing R omega) (fkMedialBlackDart1 v) = 0 := by
-- proof
  apply StatMech.FrontierD.fkRectBlackBoundaryWeight_dart0_add_dart1_eq_zero R omega v

/--
[fkRectBlackBoundaryWeight_dart0_eq_zero_of_closed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalBoundaryFiberWinding.lean)
-/
@[path]
private lemma fkRectBlackBoundaryWeight_dart0_eq_zero_of_closed_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {v : R.medialTorus.Vertex}
-- given
  (hclosed : omega (fkRectTorusMedialEdgeEquiv R v) = false) :
-- imply
  fkRectBlackBoundaryWeight R (fkRectConfigurationToMedialPairing R omega) (fkMedialBlackDart0 v) = 0 := by
-- proof
  apply StatMech.FrontierD.fkRectBlackBoundaryWeight_dart0_eq_zero_of_closed R omega v hclosed

/--
[fkRectBlackBoundaryWeight_dart1_eq_zero_of_closed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalBoundaryFiberWinding.lean)
-/
@[path]
private lemma fkRectBlackBoundaryWeight_dart1_eq_zero_of_closed_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {v : R.medialTorus.Vertex}
-- given
  (hclosed : omega (fkRectTorusMedialEdgeEquiv R v) = false) :
-- imply
  fkRectBlackBoundaryWeight R (fkRectConfigurationToMedialPairing R omega) (fkMedialBlackDart1 v) = 0 := by
-- proof
  apply StatMech.FrontierD.fkRectBlackBoundaryWeight_dart1_eq_zero_of_closed R omega v hclosed

/--
[fkRectBlackBoundaryCycleInPrimalCluster_mk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalBoundaryFiberWinding.lean)
-/
@[path]
private lemma fkRectBlackBoundaryCycleInPrimalCluster_mk_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {x : R.Vertex}
  {d : FKMedialBlackDart R.medialTorus} :
-- imply
  fkRectBlackBoundaryCycleInPrimalCluster R omega x (Quot.mk _ d) ↔ (fkRectOpenGraph R omega).Reachable x (fkRectMedialDartPrimalLabel R d.1) := by
-- proof
  apply StatMech.FrontierD.fkRectBlackBoundaryCycleInPrimalCluster_mk R omega x d

/--
[fkRectBlackBoundaryCycleWinding_mk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalBoundaryFiberWinding.lean)
-/
@[path]
private lemma fkRectBlackBoundaryCycleWinding_mk_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {d : FKMedialBlackDart R.medialTorus} :
-- imply
  fkRectBlackBoundaryCycleWinding R omega (Quot.mk _ d) = fkRectBlackBoundaryCycleClassWinding R (fkRectConfigurationToMedialPairing R omega) d := by
-- proof
  apply StatMech.FrontierD.fkRectBlackBoundaryCycleWinding_mk R omega d

/--
[fkRectPrimalClusterBoundaryCycleWindingSum_eq_weightSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalBoundaryFiberWinding.lean)
-/
@[path]
private lemma fkRectPrimalClusterBoundaryCycleWindingSum_eq_weightSum_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {x : R.Vertex} :
-- imply
  fkRectPrimalClusterBoundaryCycleWindingSum R omega x = fkRectPrimalClusterBoundaryWeightSum R omega x := by
-- proof
  apply StatMech.FrontierD.fkRectPrimalClusterBoundaryCycleWindingSum_eq_weightSum R omega x

/--
[fkRectPrimalClusterBoundaryWeightSum_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalBoundaryFiberWinding.lean)
-/
@[path]
private lemma fkRectPrimalClusterBoundaryWeightSum_eq_zero_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {x : R.Vertex} :
-- imply
  fkRectPrimalClusterBoundaryWeightSum R omega x = 0 := by
-- proof
  apply StatMech.FrontierD.fkRectPrimalClusterBoundaryWeightSum_eq_zero R omega x

/--
[fkRectPrimalClusterBoundaryCycleWindingSum_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalBoundaryFiberWinding.lean)
-/
@[path]
private lemma fkRectPrimalClusterBoundaryCycleWindingSum_eq_zero_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {x : R.Vertex} :
-- imply
  fkRectPrimalClusterBoundaryCycleWindingSum R omega x = 0 := by
-- proof
  apply StatMech.FrontierD.fkRectPrimalClusterBoundaryCycleWindingSum_eq_zero R omega x

/--
[fkRectBlackBoundaryCycle_eq_of_card_nonzero_le_two_of_fst_mul_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalBoundaryFiberWinding.lean)
-/
@[path]
private lemma fkRectBlackBoundaryCycle_eq_of_card_nonzero_le_two_of_fst_mul_pos_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {x : R.Vertex}
  {C D : FKRectConfigurationBlackBoundaryCycle R omega}
-- given
  (hcard : (fkRectPrimalClusterNonzeroBoundaryCycles R omega x).card ≤ 2)
  (hC : fkRectBlackBoundaryCycleInPrimalCluster R omega x C)
  (hD : fkRectBlackBoundaryCycleInPrimalCluster R omega x D)
  (hsign : 0 < (fkRectBlackBoundaryCycleWinding R omega C).1 * (fkRectBlackBoundaryCycleWinding R omega D).1) :
-- imply
  C = D := by
-- proof
  apply StatMech.FrontierD.fkRectBlackBoundaryCycle_eq_of_card_nonzero_le_two_of_fst_mul_pos R omega x hcard hC hD hsign


-- created on 2026-10-23
