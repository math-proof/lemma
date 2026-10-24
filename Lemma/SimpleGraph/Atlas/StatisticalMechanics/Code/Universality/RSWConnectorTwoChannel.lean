import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannel
open Finset SimpleGraph Set StatMech StatMech.Universality


/--
[rlc_connectorCentralFaceFiniteGraph_le_twoChannel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannel.lean)
-/
@[path]
private lemma rlc_connectorCentralFaceFiniteGraph_le_twoChannel_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n} :
-- imply
  rlc_connectorCentralFaceFiniteGraph gamma gamma' ≤ rlc_connectorTwoChannelGraph gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_connectorCentralFaceFiniteGraph_le_twoChannel gamma gamma'

/--
[rlc_finiteCentralFaceRandomConnectorEvent_subset_twoChannel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannel.lean)
-/
@[path]
private lemma rlc_finiteCentralFaceRandomConnectorEvent_subset_twoChannel_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n} :
-- imply
  rlc_finiteCentralFaceRandomConnectorEvent gamma gamma' ⊆ rlc_finiteTwoChannelConnectorEvent gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_finiteCentralFaceRandomConnectorEvent_subset_twoChannel gamma gamma'

/--
[rlc_connectorCentralFaceClosureGraph_eq_twoChannel_sup_trace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannel.lean)
-/
@[path]
private lemma rlc_connectorCentralFaceClosureGraph_eq_twoChannel_sup_trace_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n} :
-- imply
  rlc_connectorCentralFaceClosureGraph gamma gamma' = rlc_connectorTwoChannelGraph gamma gamma' ⊔ rlc_connectorTraceWiring gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_connectorCentralFaceClosureGraph_eq_twoChannel_sup_trace gamma gamma'

/--
[rlc_connectorTwoChannelAugmentedGraph_eq_closure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannel.lean)
-/
@[path]
private lemma rlc_connectorTwoChannelAugmentedGraph_eq_closure_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n} :
-- imply
  (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma').G = rlc_connectorCentralFaceClosureGraph gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_connectorTwoChannelAugmentedGraph_eq_closure gamma gamma'

/--
[rlc_twoChannel_numClustersBC_traceWiring_eq_separateWiring](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannel.lean)
-/
@[path]
private lemma rlc_twoChannel_numClustersBC_traceWiring_eq_separateWiring_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))} :
-- imply
  FK.numClustersBC (rlc_connectorTwoChannelGraph gamma gamma') (rlc_connectorTraceWiring gamma gamma') rho = FK.numClustersBC (rlc_connectorTwoChannelGraph gamma gamma') (rlc_connectorSeparateWiring gamma gamma') rho := by
-- proof
  apply StatMech.Universality.rlc_twoChannel_numClustersBC_traceWiring_eq_separateWiring gamma gamma' rho

/--
[rlc_twoChannel_bcWeight_traceWiring_eq_separateWiring](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannel.lean)
-/
@[path]
private lemma rlc_twoChannel_bcWeight_traceWiring_eq_separateWiring_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {p q : Real}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))} :
-- imply
  FK.bcWeight (rlc_connectorTwoChannelGraph gamma gamma') (rlc_connectorTraceWiring gamma gamma') p q rho = FK.bcWeight (rlc_connectorTwoChannelGraph gamma gamma') (rlc_connectorSeparateWiring gamma gamma') p q rho := by
-- proof
  apply StatMech.Universality.rlc_twoChannel_bcWeight_traceWiring_eq_separateWiring gamma gamma' p q rho

/--
[rlc_twoChannel_bcZ_traceWiring_eq_separateWiring](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannel.lean)
-/
@[path]
private lemma rlc_twoChannel_bcZ_traceWiring_eq_separateWiring_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {p q : Real} :
-- imply
  FK.bcZ (rlc_connectorTwoChannelGraph gamma gamma') (rlc_connectorTraceWiring gamma gamma') p q = FK.bcZ (rlc_connectorTwoChannelGraph gamma gamma') (rlc_connectorSeparateWiring gamma gamma') p q := by
-- proof
  apply StatMech.Universality.rlc_twoChannel_bcZ_traceWiring_eq_separateWiring gamma gamma' p q

/--
[rlc_twoChannel_bcProb_traceWiring_eq_separateWiring](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannel.lean)
-/
@[path]
private lemma rlc_twoChannel_bcProb_traceWiring_eq_separateWiring_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {p q : Real}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))} :
-- imply
  FK.bcProb (rlc_connectorTwoChannelGraph gamma gamma') (rlc_connectorTraceWiring gamma gamma') p q rho = FK.bcProb (rlc_connectorTwoChannelGraph gamma gamma') (rlc_connectorSeparateWiring gamma gamma') p q rho := by
-- proof
  apply StatMech.Universality.rlc_twoChannel_bcProb_traceWiring_eq_separateWiring gamma gamma' p q rho

/--
[rlc_twoChannel_bcEventMass_traceWiring_eq_separateWiring](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannel.lean)
-/
@[path]
private lemma rlc_twoChannel_bcEventMass_traceWiring_eq_separateWiring_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {p q : Real}
  {A : Set (ConfigSpace (Sym2 (RlcConnectorVertex n)))} :
-- imply
  FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma') (rlc_connectorTraceWiring gamma gamma') p q A = FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma') (rlc_connectorSeparateWiring gamma gamma') p q A := by
-- proof
  apply StatMech.Universality.rlc_twoChannel_bcEventMass_traceWiring_eq_separateWiring gamma gamma' p q A

/--
[rlc_openSub_twoChannelAugmented_forceTrace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannel.lean)
-/
@[path]
private lemma rlc_openSub_twoChannelAugmented_forceTrace_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))} :
-- imply
  FK.openSub (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma').G (rlc_connectorForceTraceConfig gamma gamma' rho) = FK.openSub (rlc_connectorTwoChannelGraph gamma gamma') rho ⊔ rlc_connectorTraceWiring gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_openSub_twoChannelAugmented_forceTrace gamma gamma' rho

/--
[rlc_connectorTwoChannelGraph_adj_not_traceWiring](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannel.lean)
-/
@[path]
private lemma rlc_connectorTwoChannelGraph_adj_not_traceWiring_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {x y : RlcConnectorVertex n}
-- given
  (hxy : (rlc_connectorTwoChannelGraph gamma gamma').Adj x y) :
-- imply
  ¬ (rlc_connectorTraceWiring gamma gamma').Adj x y := by
-- proof
  apply StatMech.Universality.rlc_connectorTwoChannelGraph_adj_not_traceWiring gamma gamma' hxy

/--
[rlc_twoChannel_numClusters_augmented_forceTrace_eq_traceBC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannel.lean)
-/
@[path]
private lemma rlc_twoChannel_numClusters_augmented_forceTrace_eq_traceBC_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))} :
-- imply
  FK.numClusters (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma').G (rlc_connectorForceTraceConfig gamma gamma' rho) = FK.numClustersBC (rlc_connectorTwoChannelGraph gamma gamma') (rlc_connectorTraceWiring gamma gamma') rho := by
-- proof
  apply StatMech.Universality.rlc_twoChannel_numClusters_augmented_forceTrace_eq_traceBC gamma gamma' rho

/--
[rlc_twoChannel_edgeProduct_augmented_forceTrace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannel.lean)
-/
@[path]
private lemma rlc_twoChannel_edgeProduct_augmented_forceTrace_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {p : Real}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))} :
-- imply
  FK.edgeProduct (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma').G p (rlc_connectorForceTraceConfig gamma gamma' rho) = p ^ (rlc_connectorTraceWiring gamma gamma').edgeFinset.card * FK.edgeProduct (rlc_connectorTwoChannelGraph gamma gamma') p rho := by
-- proof
  apply StatMech.Universality.rlc_twoChannel_edgeProduct_augmented_forceTrace gamma gamma' p rho

/--
[rlc_twoChannel_fkWeight_augmented_forceTrace_eq_separateBC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannel.lean)
-/
@[path]
private lemma rlc_twoChannel_fkWeight_augmented_forceTrace_eq_separateBC_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {p q : Real}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))} :
-- imply
  FK.fkWeight (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma').G p q (rlc_connectorForceTraceConfig gamma gamma' rho) = p ^ (rlc_connectorTraceWiring gamma gamma').edgeFinset.card * FK.bcWeight (rlc_connectorTwoChannelGraph gamma gamma') (rlc_connectorSeparateWiring gamma gamma') p q rho := by
-- proof
  apply StatMech.Universality.rlc_twoChannel_fkWeight_augmented_forceTrace_eq_separateBC gamma gamma' p q rho

/--
[rlc_twoChannelForced_weight_duality](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannel.lean)
-/
@[path]
private lemma rlc_twoChannelForced_weight_duality_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {p q : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  let P := rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma' p ^ (rlc_connectorTraceWiring gamma gamma').edgeFinset.card * FK.bcWeight (rlc_connectorTwoChannelGraph gamma gamma') (rlc_connectorSeparateWiring gamma gamma') p q rho * q ^ (P.G.edgeFinset.card + 1) = (p / (1 - BeffaraDC.dualParam p q)) ^ P.G.edgeFinset.card * q ^ Nat.card P.V * BeffaraDC.pfdDualWeight P (BeffaraDC.dualParam p q) q (FK.openSub P.G (rlc_connectorForceTraceConfig gamma gamma' rho)) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelForced_weight_duality gamma gamma' rho hp hp1 hq

/--
[rlc_twoChannelForcedDualZ_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannel.lean)
-/
@[path]
private lemma rlc_twoChannelForcedDualZ_pos_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {p q : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  0 < rlc_twoChannelForcedDualZ gamma gamma' p q := by
-- proof
  apply StatMech.Universality.rlc_twoChannelForcedDualZ_pos gamma gamma' hp hp1 hq

/--
[rlc_twoChannelForced_partition_duality](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannel.lean)
-/
@[path]
private lemma rlc_twoChannelForced_partition_duality_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {p q : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  let P := rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma' p ^ (rlc_connectorTraceWiring gamma gamma').edgeFinset.card * FK.bcZ (rlc_connectorTwoChannelGraph gamma gamma') (rlc_connectorSeparateWiring gamma gamma') p q * q ^ (P.G.edgeFinset.card + 1) = (p / (1 - BeffaraDC.dualParam p q)) ^ P.G.edgeFinset.card * q ^ Nat.card P.V * rlc_twoChannelForcedDualZ gamma gamma' (BeffaraDC.dualParam p q) q := by
-- proof
  apply StatMech.Universality.rlc_twoChannelForced_partition_duality gamma gamma' hp hp1 hq

/--
[rlc_twoChannel_bcProb_separate_eq_forcedDualProb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannel.lean)
-/
@[path]
private lemma rlc_twoChannel_bcProb_separate_eq_forcedDualProb_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {p q : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  FK.bcProb (rlc_connectorTwoChannelGraph gamma gamma') (rlc_connectorSeparateWiring gamma gamma') p q rho = rlc_twoChannelForcedDualProb gamma gamma' (BeffaraDC.dualParam p q) q rho := by
-- proof
  apply StatMech.Universality.rlc_twoChannel_bcProb_separate_eq_forcedDualProb gamma gamma' rho hp hp1 hq

/--
[rlc_twoChannelForcedDualProb_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannel.lean)
-/
@[path]
private lemma rlc_twoChannelForcedDualProb_nonneg_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {p q : Real}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  0 ≤ rlc_twoChannelForcedDualProb gamma gamma' p q rho := by
-- proof
  apply StatMech.Universality.rlc_twoChannelForcedDualProb_nonneg gamma gamma' hp hp1 hq rho

/--
[rlc_bcProb_half_q_one_uniform](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannel.lean)
-/
@[path]
private lemma rlc_bcProb_half_q_one_uniform_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C D : SimpleGraph V}
  [DecidableRel C.Adj]
  [DecidableRel D.Adj]
  {rho eta : ConfigSpace (Sym2 V)} :
-- imply
  FK.bcProb G C (1 / 2 : Real) 1 rho = FK.bcProb G D (1 / 2 : Real) 1 eta := by
-- proof
  apply StatMech.Universality.rlc_bcProb_half_q_one_uniform G C D rho eta

/--
[rlc_twoChannelForcedDualProb_half_q_one_eq_merged](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannel.lean)
-/
@[path]
private lemma rlc_twoChannelForcedDualProb_half_q_one_eq_merged_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho eta : ConfigSpace (Sym2 (RlcConnectorVertex n))} :
-- imply
  rlc_twoChannelForcedDualProb gamma gamma' (1 / 2) 1 rho = FK.bcProb (rlc_connectorTwoChannelGraph gamma gamma') (rlc_connectorMergedWiring gamma gamma') (1 / 2) 1 eta := by
-- proof
  apply StatMech.Universality.rlc_twoChannelForcedDualProb_half_q_one_eq_merged gamma gamma' rho eta

/--
[rlc_twoChannelForcedDualSingletonMass_le_merged_of_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannel.lean)
-/
@[path]
private lemma rlc_twoChannelForcedDualSingletonMass_le_merged_of_mem_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho eta : ConfigSpace (Sym2 (RlcConnectorVertex n))}
-- given
  (heta : eta ∈ rlc_finiteTwoChannelConnectorEvent gamma gamma') :
-- imply
  rlc_twoChannelForcedDualEventMass gamma gamma' (1 / 2) 1 {rho} ≤ FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma') (rlc_connectorMergedWiring gamma gamma') (1 / 2) 1 (rlc_finiteTwoChannelConnectorEvent gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_twoChannelForcedDualSingletonMass_le_merged_of_mem gamma gamma' rho eta heta

/--
[rlc_twoChannel_bcEventMass_separate_eq_forcedDualEventMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannel.lean)
-/
@[path]
private lemma rlc_twoChannel_bcEventMass_separate_eq_forcedDualEventMass_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {A : Set (ConfigSpace (Sym2 (RlcConnectorVertex n)))}
  {p q : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma') (rlc_connectorSeparateWiring gamma gamma') p q A = rlc_twoChannelForcedDualEventMass gamma gamma' (BeffaraDC.dualParam p q) q A := by
-- proof
  apply StatMech.Universality.rlc_twoChannel_bcEventMass_separate_eq_forcedDualEventMass gamma gamma' A hp hp1 hq

/--
[rlc_twoChannel_bcEventMass_separate_selfDual_eq_forcedDualEventMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannel.lean)
-/
@[path]
private lemma rlc_twoChannel_bcEventMass_separate_selfDual_eq_forcedDualEventMass_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {A : Set (ConfigSpace (Sym2 (RlcConnectorVertex n)))}
  {q : Real}
-- given
  (hq : 0 < q) :
-- imply
  FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma') (rlc_connectorSeparateWiring gamma gamma') (BeffaraDC.selfDualPoint q) q A = rlc_twoChannelForcedDualEventMass gamma gamma' (BeffaraDC.selfDualPoint q) q A := by
-- proof
  apply StatMech.Universality.rlc_twoChannel_bcEventMass_separate_selfDual_eq_forcedDualEventMass gamma gamma' A hq

/--
[rlc_twoChannel_bcProb_separate_selfDual_eq_forcedDualProb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannel.lean)
-/
@[path]
private lemma rlc_twoChannel_bcProb_separate_selfDual_eq_forcedDualProb_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {q : Real}
-- given
  (hq : 0 < q) :
-- imply
  FK.bcProb (rlc_connectorTwoChannelGraph gamma gamma') (rlc_connectorSeparateWiring gamma gamma') (BeffaraDC.selfDualPoint q) q rho = rlc_twoChannelForcedDualProb gamma gamma' (BeffaraDC.selfDualPoint q) q rho := by
-- proof
  apply StatMech.Universality.rlc_twoChannel_bcProb_separate_selfDual_eq_forcedDualProb gamma gamma' rho hq

/--
[rlc_finiteCentralFaceClosureConnectorEvent_subset_twoChannel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannel.lean)
-/
@[path]
private lemma rlc_finiteCentralFaceClosureConnectorEvent_subset_twoChannel_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n} :
-- imply
  rlc_finiteCentralFaceClosureConnectorEvent gamma gamma' ⊆ rlc_finiteTwoChannelConnectorEvent gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_finiteCentralFaceClosureConnectorEvent_subset_twoChannel gamma gamma'

/--
[rlc_centralFacePIMS_twoChannel_success_of_closure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannel.lean)
-/
@[path]
private lemma rlc_centralFacePIMS_twoChannel_success_of_closure_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
-- given
  (hclosure : rlc_connectorCentralFacePIMSConfig gamma gamma' rho ∈ rlc_finiteCentralFaceClosureConnectorEvent gamma gamma') :
-- imply
  rlc_connectorCentralFacePIMSConfig gamma gamma' rho ∈ rlc_finiteTwoChannelConnectorEvent gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_centralFacePIMS_twoChannel_success_of_closure gamma gamma' rho hclosure

/--
[rlc_twoChannelClosureFailureCertificate_of_centralFace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannel.lean)
-/
@[path]
private lemma rlc_twoChannelClosureFailureCertificate_of_centralFace_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
-- given
  (hcentral : RlcCentralFaceClosureFailureCertificate gamma gamma') :
-- imply
  RlcTwoChannelClosureFailureCertificate gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_twoChannelClosureFailureCertificate_of_centralFace gamma gamma' hcentral

/--
[rlc_twoChannelPIMS_success_of_closureFailureCertificate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannel.lean)
-/
@[path]
private lemma rlc_twoChannelPIMS_success_of_closureFailureCertificate_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
-- given
  (hfailure : RlcTwoChannelClosureFailureCertificate gamma gamma')
  (hno : rho ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma') :
-- imply
  rlc_connectorCentralFacePIMSConfig gamma gamma' rho ∈ rlc_finiteTwoChannelConnectorEvent gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_twoChannelPIMS_success_of_closureFailureCertificate gamma gamma' hfailure rho hno

/--
[rlc_finiteTwoChannelConnectorEvent_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannel.lean)
-/
@[path]
private lemma rlc_finiteTwoChannelConnectorEvent_isIncreasing_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n} :
-- imply
  IsIncreasing (rlc_finiteTwoChannelConnectorEvent gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_finiteTwoChannelConnectorEvent_isIncreasing gamma gamma'

/--
[rlc_twoChannelPIMSFailureImageMass_eq_forcedDual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannel.lean)
-/
@[path]
private lemma rlc_twoChannelPIMSFailureImageMass_eq_forcedDual_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {q : Real}
-- given
  (hq : 0 < q) :
-- imply
  rlc_twoChannelPIMSFailureImageMass gamma gamma' (BeffaraDC.selfDualPoint q) q = rlc_twoChannelForcedDualFailureImageMass gamma gamma' (BeffaraDC.selfDualPoint q) q := by
-- proof
  apply StatMech.Universality.rlc_twoChannelPIMSFailureImageMass_eq_forcedDual gamma gamma' hq

/--
[rlc_twoChannel_failureMass_eq_PIMSFailureImageMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannel.lean)
-/
@[path]
private lemma rlc_twoChannel_failureMass_eq_PIMSFailureImageMass_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {p q : Real}
-- given
  (hfailure : RlcTwoChannelClosureFailureCertificate gamma gamma') :
-- imply
  FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma') (rlc_connectorSeparateWiring gamma gamma') p q (rlc_finiteTwoChannelConnectorEvent gamma gamma')ᶜ = rlc_twoChannelPIMSFailureImageMass gamma gamma' p q := by
-- proof
  apply StatMech.Universality.rlc_twoChannel_failureMass_eq_PIMSFailureImageMass gamma gamma' p q hfailure

/--
[rlc_twoChannelForcedDualFailureImageMass_eq_compl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannel.lean)
-/
@[path]
private lemma rlc_twoChannelForcedDualFailureImageMass_eq_compl_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {p q : Real}
-- given
  (hfailure : RlcTwoChannelClosureFailureCertificate gamma gamma') :
-- imply
  rlc_twoChannelForcedDualFailureImageMass gamma gamma' p q = rlc_twoChannelForcedDualEventMass gamma gamma' p q (rlc_finiteTwoChannelConnectorEvent gamma gamma')ᶜ := by
-- proof
  apply StatMech.Universality.rlc_twoChannelForcedDualFailureImageMass_eq_compl gamma gamma' p q hfailure

/--
[rlc_twoChannelForcedDualEventMass_compl_le_merged_of_equiv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannel.lean)
-/
@[path]
private lemma rlc_twoChannelForcedDualEventMass_compl_le_merged_of_equiv_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {q : Real}
  {D : ConfigSpace (Sym2 (RlcConnectorVertex n)) ≃ ConfigSpace (Sym2 (RlcConnectorVertex n))}
-- given
  (hq : 1 ≤ q)
  (hfailure : ∀ rho, rho ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma' → D rho ∈ rlc_finiteTwoChannelConnectorEvent gamma gamma')
  (hprob : ∀ rho, rlc_twoChannelForcedDualProb gamma gamma' (BeffaraDC.selfDualPoint q) q rho ≤ FK.bcProb (rlc_connectorTwoChannelGraph gamma gamma') (rlc_connectorMergedWiring gamma gamma') (BeffaraDC.selfDualPoint q) q (D rho)) :
-- imply
  rlc_twoChannelForcedDualEventMass gamma gamma' (BeffaraDC.selfDualPoint q) q (rlc_finiteTwoChannelConnectorEvent gamma gamma')ᶜ ≤ FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma') (rlc_connectorMergedWiring gamma gamma') (BeffaraDC.selfDualPoint q) q (rlc_finiteTwoChannelConnectorEvent gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_twoChannelForcedDualEventMass_compl_le_merged_of_equiv gamma gamma' hq D hfailure hprob

/--
[rlc_twoChannelForcedDualEventMass_compl_le_merged_of_injection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannel.lean)
-/
@[path]
private lemma rlc_twoChannelForcedDualEventMass_compl_le_merged_of_injection_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {q : Real}
-- given
  (hq : 1 ≤ q)
  (D : {rho : ConfigSpace (Sym2 (RlcConnectorVertex n)) // rho ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma'} → ConfigSpace (Sym2 (RlcConnectorVertex n)))
  (hinj : Function.Injective D)
  (hsuccess : ∀ rho, D rho ∈ rlc_finiteTwoChannelConnectorEvent gamma gamma')
  (hprob : ∀ rho, rlc_twoChannelForcedDualProb gamma gamma' (BeffaraDC.selfDualPoint q) q rho.1 ≤ FK.bcProb (rlc_connectorTwoChannelGraph gamma gamma') (rlc_connectorMergedWiring gamma gamma') (BeffaraDC.selfDualPoint q) q (D rho)) :
-- imply
  rlc_twoChannelForcedDualEventMass gamma gamma' (BeffaraDC.selfDualPoint q) q (rlc_finiteTwoChannelConnectorEvent gamma gamma')ᶜ ≤ FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma') (rlc_connectorMergedWiring gamma gamma') (BeffaraDC.selfDualPoint q) q (rlc_finiteTwoChannelConnectorEvent gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_twoChannelForcedDualEventMass_compl_le_merged_of_injection gamma gamma' hq D hinj hsuccess hprob

/--
[rlc_twoChannelForcedDualEventMass_compl_le_mul_merged_of_injection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannel.lean)
-/
@[path]
private lemma rlc_twoChannelForcedDualEventMass_compl_le_mul_merged_of_injection_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {q distortion : Real}
-- given
  (hq : 1 ≤ q)
  (hdistortion : 0 ≤ distortion)
  (D : {rho : ConfigSpace (Sym2 (RlcConnectorVertex n)) // rho ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma'} → ConfigSpace (Sym2 (RlcConnectorVertex n)))
  (hinj : Function.Injective D)
  (hsuccess : ∀ rho, D rho ∈ rlc_finiteTwoChannelConnectorEvent gamma gamma')
  (hprob : ∀ rho, rlc_twoChannelForcedDualProb gamma gamma' (BeffaraDC.selfDualPoint q) q rho.1 ≤ distortion * FK.bcProb (rlc_connectorTwoChannelGraph gamma gamma') (rlc_connectorMergedWiring gamma gamma') (BeffaraDC.selfDualPoint q) q (D rho)) :
-- imply
  rlc_twoChannelForcedDualEventMass gamma gamma' (BeffaraDC.selfDualPoint q) q (rlc_finiteTwoChannelConnectorEvent gamma gamma')ᶜ ≤ distortion * FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma') (rlc_connectorMergedWiring gamma gamma') (BeffaraDC.selfDualPoint q) q (rlc_finiteTwoChannelConnectorEvent gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_twoChannelForcedDualEventMass_compl_le_mul_merged_of_injection gamma gamma' hq hdistortion D hinj hsuccess hprob

/--
[rlc_twoChannelForcedDualFailurePushforwardComparison_of_equiv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannel.lean)
-/
@[path]
private lemma rlc_twoChannelForcedDualFailurePushforwardComparison_of_equiv_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {q : Real}
  {D : ConfigSpace (Sym2 (RlcConnectorVertex n)) ≃ ConfigSpace (Sym2 (RlcConnectorVertex n))}
-- given
  (hq : 1 ≤ q)
  (hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma')
  (hfailure : ∀ rho, rho ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma' → D rho ∈ rlc_finiteTwoChannelConnectorEvent gamma gamma')
  (hprob : ∀ rho, rlc_twoChannelForcedDualProb gamma gamma' (BeffaraDC.selfDualPoint q) q rho ≤ FK.bcProb (rlc_connectorTwoChannelGraph gamma gamma') (rlc_connectorMergedWiring gamma gamma') (BeffaraDC.selfDualPoint q) q (D rho)) :
-- imply
  RlcTwoChannelForcedDualFailurePushforwardComparison gamma gamma' q := by
-- proof
  apply StatMech.Universality.rlc_twoChannelForcedDualFailurePushforwardComparison_of_equiv gamma gamma' hq hclosure D hfailure hprob

/--
[rlc_twoChannelForcedDualFailurePushforwardComparison_of_injection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannel.lean)
-/
@[path]
private lemma rlc_twoChannelForcedDualFailurePushforwardComparison_of_injection_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {q : Real}
-- given
  (hq : 1 ≤ q)
  (hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma')
  (D : {rho : ConfigSpace (Sym2 (RlcConnectorVertex n)) // rho ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma'} → ConfigSpace (Sym2 (RlcConnectorVertex n)))
  (hinj : Function.Injective D)
  (hsuccess : ∀ rho, D rho ∈ rlc_finiteTwoChannelConnectorEvent gamma gamma')
  (hprob : ∀ rho, rlc_twoChannelForcedDualProb gamma gamma' (BeffaraDC.selfDualPoint q) q rho.1 ≤ FK.bcProb (rlc_connectorTwoChannelGraph gamma gamma') (rlc_connectorMergedWiring gamma gamma') (BeffaraDC.selfDualPoint q) q (D rho)) :
-- imply
  RlcTwoChannelForcedDualFailurePushforwardComparison gamma gamma' q := by
-- proof
  apply StatMech.Universality.rlc_twoChannelForcedDualFailurePushforwardComparison_of_injection gamma gamma' hq hclosure D hinj hsuccess hprob

/--
[rlc_twoChannelForcedDualFailurePushforwardComparison_q_one_of_injection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannel.lean)
-/
@[path]
private lemma rlc_twoChannelForcedDualFailurePushforwardComparison_q_one_of_injection_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
-- given
  (hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma')
  (D : {rho : ConfigSpace (Sym2 (RlcConnectorVertex n)) // rho ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma'} → ConfigSpace (Sym2 (RlcConnectorVertex n)))
  (hinj : Function.Injective D)
  (hsuccess : ∀ rho, D rho ∈ rlc_finiteTwoChannelConnectorEvent gamma gamma') :
-- imply
  RlcTwoChannelForcedDualFailurePushforwardComparison gamma gamma' 1 := by
-- proof
  apply StatMech.Universality.rlc_twoChannelForcedDualFailurePushforwardComparison_q_one_of_injection gamma gamma' hclosure D hinj hsuccess

/--
[rlc_twoChannelForcedDualEventMass_compl_le_merged_of_partitioned_injections](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannel.lean)
-/
@[path]
private lemma rlc_twoChannelForcedDualEventMass_compl_le_merged_of_partitioned_injections_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {q : Real}
-- given
  (hq : 1 <= q)
  (R : {rho : ConfigSpace (Sym2 (RlcConnectorVertex n)) // rho ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma'} -> Prop)
  (Dgood : {rho : {rho : ConfigSpace (Sym2 (RlcConnectorVertex n)) // rho ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma'} // R rho} -> ConfigSpace (Sym2 (RlcConnectorVertex n)))
  (Dbad : {rho : {rho : ConfigSpace (Sym2 (RlcConnectorVertex n)) // rho ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma'} // ¬ R rho} -> ConfigSpace (Sym2 (RlcConnectorVertex n)))
  (hgoodInj : Function.Injective Dgood)
  (hbadInj : Function.Injective Dbad)
  (hrange : Disjoint (Set.range Dgood) (Set.range Dbad))
  (hgoodSuccess : forall rho, Dgood rho ∈ rlc_finiteTwoChannelConnectorEvent gamma gamma')
  (hbadSuccess : forall rho, Dbad rho ∈ rlc_finiteTwoChannelConnectorEvent gamma gamma')
  (hgoodProb : forall rho, rlc_twoChannelForcedDualProb gamma gamma' (BeffaraDC.selfDualPoint q) q rho.1.1 <= FK.bcProb (rlc_connectorTwoChannelGraph gamma gamma') (rlc_connectorMergedWiring gamma gamma') (BeffaraDC.selfDualPoint q) q (Dgood rho))
  (hbadProb : forall rho, rlc_twoChannelForcedDualProb gamma gamma' (BeffaraDC.selfDualPoint q) q rho.1.1 <= FK.bcProb (rlc_connectorTwoChannelGraph gamma gamma') (rlc_connectorMergedWiring gamma gamma') (BeffaraDC.selfDualPoint q) q (Dbad rho)) :
-- imply
  rlc_twoChannelForcedDualEventMass gamma gamma' (BeffaraDC.selfDualPoint q) q (rlc_finiteTwoChannelConnectorEvent gamma gamma')ᶜ <= FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma') (rlc_connectorMergedWiring gamma gamma') (BeffaraDC.selfDualPoint q) q (rlc_finiteTwoChannelConnectorEvent gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_twoChannelForcedDualEventMass_compl_le_merged_of_partitioned_injections gamma gamma' hq R Dgood Dbad hgoodInj hbadInj hrange hgoodSuccess hbadSuccess hgoodProb hbadProb

/--
[rlc_twoChannelForcedDualFailurePushforwardComparison_of_anchoredIncidenceInjections](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannel.lean)
-/
@[path]
private lemma rlc_twoChannelForcedDualFailurePushforwardComparison_of_anchoredIncidenceInjections_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {q : Real}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hq : 1 <= q)
  (Dincidence : {rho : {rho : ConfigSpace (Sym2 (RlcConnectorVertex n)) // rho ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma'} // RlcTwoChannelFailureRetainedAnchorTraceIncidence gamma gamma' hfaith rho} -> ConfigSpace (Sym2 (RlcConnectorVertex n)))
  (Dmissing : {rho : {rho : ConfigSpace (Sym2 (RlcConnectorVertex n)) // rho ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma'} // ¬ RlcTwoChannelFailureRetainedAnchorTraceIncidence gamma gamma' hfaith rho} -> ConfigSpace (Sym2 (RlcConnectorVertex n)))
  (hincidenceInj : Function.Injective Dincidence)
  (hmissingInj : Function.Injective Dmissing)
  (hrange : Disjoint (Set.range Dincidence) (Set.range Dmissing))
  (hincidenceSuccess : forall rho, Dincidence rho ∈ rlc_finiteTwoChannelConnectorEvent gamma gamma')
  (hmissingSuccess : forall rho, Dmissing rho ∈ rlc_finiteTwoChannelConnectorEvent gamma gamma')
  (hincidenceProb : forall rho, rlc_twoChannelForcedDualProb gamma gamma' (BeffaraDC.selfDualPoint q) q rho.1.1 <= FK.bcProb (rlc_connectorTwoChannelGraph gamma gamma') (rlc_connectorMergedWiring gamma gamma') (BeffaraDC.selfDualPoint q) q (Dincidence rho))
  (hmissingProb : forall rho, rlc_twoChannelForcedDualProb gamma gamma' (BeffaraDC.selfDualPoint q) q rho.1.1 <= FK.bcProb (rlc_connectorTwoChannelGraph gamma gamma') (rlc_connectorMergedWiring gamma gamma') (BeffaraDC.selfDualPoint q) q (Dmissing rho)) :
-- imply
  RlcTwoChannelForcedDualFailurePushforwardComparison gamma gamma' q := by
-- proof
  apply StatMech.Universality.rlc_twoChannelForcedDualFailurePushforwardComparison_of_anchoredIncidenceInjections gamma gamma' hfaith hq Dincidence Dmissing hincidenceInj hmissingInj hrange hincidenceSuccess hmissingSuccess hincidenceProb hmissingProb

/--
[rlc_twoChannelForcedDualFailurePushforwardComparison_q_one_of_anchoredIncidenceInjections](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannel.lean)
-/
@[path]
private lemma rlc_twoChannelForcedDualFailurePushforwardComparison_q_one_of_anchoredIncidenceInjections_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (Dincidence : {rho : {rho : ConfigSpace (Sym2 (RlcConnectorVertex n)) // rho ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma'} // RlcTwoChannelFailureRetainedAnchorTraceIncidence gamma gamma' hfaith rho} -> ConfigSpace (Sym2 (RlcConnectorVertex n)))
  (Dmissing : {rho : {rho : ConfigSpace (Sym2 (RlcConnectorVertex n)) // rho ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma'} // ¬ RlcTwoChannelFailureRetainedAnchorTraceIncidence gamma gamma' hfaith rho} -> ConfigSpace (Sym2 (RlcConnectorVertex n)))
  (hincidenceInj : Function.Injective Dincidence)
  (hmissingInj : Function.Injective Dmissing)
  (hrange : Disjoint (Set.range Dincidence) (Set.range Dmissing))
  (hincidenceSuccess : forall rho, Dincidence rho ∈ rlc_finiteTwoChannelConnectorEvent gamma gamma')
  (hmissingSuccess : forall rho, Dmissing rho ∈ rlc_finiteTwoChannelConnectorEvent gamma gamma') :
-- imply
  RlcTwoChannelForcedDualFailurePushforwardComparison gamma gamma' 1 := by
-- proof
  apply StatMech.Universality.rlc_twoChannelForcedDualFailurePushforwardComparison_q_one_of_anchoredIncidenceInjections gamma gamma' hfaith Dincidence Dmissing hincidenceInj hmissingInj hrange hincidenceSuccess hmissingSuccess

/--
[rlc_twoChannelConnector_glues_horizontal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannel.lean)
-/
@[path]
private lemma rlc_twoChannelConnector_glues_horizontal_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
-- given
  (_hn : 0 < n) :
-- imply
  rlc_pathOpen gamma.1 ∩ rlc_pathOpen gamma'.1 ∩ (rlc_connectorRestrictConfig ⁻¹' rlc_finiteTwoChannelConnectorEvent gamma gamma') ⊆ horizontalCrossingEvent (-2 * n) (2 * n) (-n) n := by
-- proof
  apply StatMech.Universality.rlc_twoChannelConnector_glues_horizontal n _hn gamma gamma'

/--
[rlc_twoChannelFailureMassComparison_of_PIMS](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannel.lean)
-/
@[path]
private lemma rlc_twoChannelFailureMassComparison_of_PIMS_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {p q : Real}
-- given
  (hfailure : RlcTwoChannelClosureFailureCertificate gamma gamma')
  (hpush : RlcTwoChannelPIMSFailurePushforwardComparison gamma gamma' p q) :
-- imply
  RlcTwoChannelFailureMassComparison gamma gamma' p q := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFailureMassComparison_of_PIMS gamma gamma' p q hfailure hpush

/--
[rlc_finiteTwoChannelConnectorMass_ge_one_div_one_add_q](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannel.lean)
-/
@[path]
private lemma rlc_finiteTwoChannelConnectorMass_ge_one_div_one_add_q_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {p q : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hdual : RlcTwoChannelFailureMassComparison gamma gamma' p q) :
-- imply
  1 / (1 + q) ≤ FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma') (rlc_connectorSeparateWiring gamma gamma') p q (rlc_finiteTwoChannelConnectorEvent gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_finiteTwoChannelConnectorMass_ge_one_div_one_add_q gamma gamma' hp hp1 hq hdual

/--
[rlc_finiteTwoChannelConnectorMass_ge_one_div_one_add_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannel.lean)
-/
@[path]
private lemma rlc_finiteTwoChannelConnectorMass_ge_one_div_one_add_mul_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {p q distortion : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 <= q)
  (hdistortion : 0 <= distortion)
  (hdual : FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma') (rlc_connectorSeparateWiring gamma gamma') p q (rlc_finiteTwoChannelConnectorEvent gamma gamma')ᶜ <= distortion * FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma') (rlc_connectorMergedWiring gamma gamma') p q (rlc_finiteTwoChannelConnectorEvent gamma gamma')) :
-- imply
  1 / (1 + distortion * q) <= FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma') (rlc_connectorSeparateWiring gamma gamma') p q (rlc_finiteTwoChannelConnectorEvent gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_finiteTwoChannelConnectorMass_ge_one_div_one_add_mul gamma gamma' hp hp1 hq hdistortion hdual

/--
[rlc_finiteTwoChannelConnectorMass_selfDual_ge_of_distorted_forcedDual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannel.lean)
-/
@[path]
private lemma rlc_finiteTwoChannelConnectorMass_selfDual_ge_of_distorted_forcedDual_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {q distortion : Real}
-- given
  (hq : 1 <= q)
  (hdistortion : 0 <= distortion)
  (hfailure : RlcTwoChannelClosureFailureCertificate gamma gamma')
  (hpush : rlc_twoChannelForcedDualEventMass gamma gamma' (BeffaraDC.selfDualPoint q) q (rlc_finiteTwoChannelConnectorEvent gamma gamma')ᶜ <= distortion * FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma') (rlc_connectorMergedWiring gamma gamma') (BeffaraDC.selfDualPoint q) q (rlc_finiteTwoChannelConnectorEvent gamma gamma')) :
-- imply
  1 / (1 + distortion * q) <= FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma') (rlc_connectorSeparateWiring gamma gamma') (BeffaraDC.selfDualPoint q) q (rlc_finiteTwoChannelConnectorEvent gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_finiteTwoChannelConnectorMass_selfDual_ge_of_distorted_forcedDual gamma gamma' hq hdistortion hfailure hpush

/--
[rlc_finiteTwoChannelConnectorMass_selfDual_ge_of_PIMS](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannel.lean)
-/
@[path]
private lemma rlc_finiteTwoChannelConnectorMass_selfDual_ge_of_PIMS_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {q : Real}
-- given
  (hq : 1 ≤ q)
  (hfailure : RlcTwoChannelClosureFailureCertificate gamma gamma')
  (hpush : RlcTwoChannelForcedDualFailurePushforwardComparison gamma gamma' q) :
-- imply
  1 / (1 + q) ≤ FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma') (rlc_connectorSeparateWiring gamma gamma') (BeffaraDC.selfDualPoint q) q (rlc_finiteTwoChannelConnectorEvent gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_finiteTwoChannelConnectorMass_selfDual_ge_of_PIMS gamma gamma' hq hfailure hpush


-- created on 2026-10-23
