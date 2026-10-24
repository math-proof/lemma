import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelEdgeEncoding
open Finset SimpleGraph Set StatMech StatMech.Universality


/--
[rlc_twoChannelEdgeConfigCombine_edge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelEdgeEncoding.lean)
-/
@[path]
private lemma rlc_twoChannelEdgeConfigCombine_edge_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {outside : RlcTwoChannelOffGraphConfig gamma gamma'}
  {e : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet} :
-- imply
  rlc_twoChannelEdgeConfigCombine gamma gamma' omega outside e.1 = omega e := by
-- proof
  apply StatMech.Universality.rlc_twoChannelEdgeConfigCombine_edge gamma gamma' omega outside e

/--
[rlc_openSub_twoChannel_edgeConfigCombine](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelEdgeEncoding.lean)
-/
@[path]
private lemma rlc_openSub_twoChannel_edgeConfigCombine_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {outside : RlcTwoChannelOffGraphConfig gamma gamma'} :
-- imply
  FK.openSub (rlc_connectorTwoChannelGraph gamma gamma') (rlc_twoChannelEdgeConfigCombine gamma gamma' omega outside) = FK.openSub (rlc_connectorTwoChannelGraph gamma gamma') (rlc_twoChannelEdgeConfigExtend gamma gamma' omega) := by
-- proof
  apply StatMech.Universality.rlc_openSub_twoChannel_edgeConfigCombine gamma gamma' omega outside

/--
[rlc_twoChannel_edgeConfigCombine_mem_event_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelEdgeEncoding.lean)
-/
@[path]
private lemma rlc_twoChannel_edgeConfigCombine_mem_event_iff_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {outside : RlcTwoChannelOffGraphConfig gamma gamma'} :
-- imply
  rlc_twoChannelEdgeConfigCombine gamma gamma' omega outside ∈ rlc_finiteTwoChannelConnectorEvent gamma gamma' ↔ rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∈ rlc_finiteTwoChannelConnectorEvent gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_twoChannel_edgeConfigCombine_mem_event_iff gamma gamma' omega outside

/--
[rlc_twoChannel_split_fst_mem_event_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelEdgeEncoding.lean)
-/
@[path]
private lemma rlc_twoChannel_split_fst_mem_event_iff_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))} :
-- imply
  rlc_twoChannelEdgeConfigExtend gamma gamma' ((rlc_twoChannelConfigSplitEquiv gamma gamma' rho).1) ∈ rlc_finiteTwoChannelConnectorEvent gamma gamma' ↔ rho ∈ rlc_finiteTwoChannelConnectorEvent gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_twoChannel_split_fst_mem_event_iff gamma gamma' rho

/--
[rlc_twoChannelLiftEdgeFailureEmbedding_success](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelEdgeEncoding.lean)
-/
@[path]
private lemma rlc_twoChannelLiftEdgeFailureEmbedding_success_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
-- given
  (J : {omega : RlcTwoChannelEdgeConfig gamma gamma' // rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma'} ↪ {eta : RlcTwoChannelEdgeConfig gamma gamma' // rlc_twoChannelEdgeConfigExtend gamma gamma' eta ∈ rlc_finiteTwoChannelConnectorEvent gamma gamma'})
  (rho : {rho : ConfigSpace (Sym2 (RlcConnectorVertex n)) // rho ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma'}) :
-- imply
  rlc_twoChannelLiftEdgeFailureEmbedding gamma gamma' J rho ∈ rlc_finiteTwoChannelConnectorEvent gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_twoChannelLiftEdgeFailureEmbedding_success gamma gamma' J rho

/--
[rlc_twoChannelForcedDualProb_edgeConfigCombine](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelEdgeEncoding.lean)
-/
@[path]
private lemma rlc_twoChannelForcedDualProb_edgeConfigCombine_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {p q : Real}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {outside : RlcTwoChannelOffGraphConfig gamma gamma'} :
-- imply
  rlc_twoChannelForcedDualProb gamma gamma' p q (rlc_twoChannelEdgeConfigCombine gamma gamma' omega outside) = rlc_twoChannelForcedDualProb gamma gamma' p q (rlc_twoChannelEdgeConfigExtend gamma gamma' omega) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelForcedDualProb_edgeConfigCombine gamma gamma' p q omega outside

/--
[rlc_twoChannel_bcWeight_edgeConfigCombine](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelEdgeEncoding.lean)
-/
@[path]
private lemma rlc_twoChannel_bcWeight_edgeConfigCombine_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {C : SimpleGraph (RlcConnectorVertex n)}
  [DecidableRel C.Adj]
  {p q : Real}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {outside : RlcTwoChannelOffGraphConfig gamma gamma'} :
-- imply
  FK.bcWeight (rlc_connectorTwoChannelGraph gamma gamma') C p q (rlc_twoChannelEdgeConfigCombine gamma gamma' omega outside) = FK.bcWeight (rlc_connectorTwoChannelGraph gamma gamma') C p q (rlc_twoChannelEdgeConfigExtend gamma gamma' omega) := by
-- proof
  apply StatMech.Universality.rlc_twoChannel_bcWeight_edgeConfigCombine gamma gamma' C p q omega outside

/--
[rlc_twoChannel_bcProb_edgeConfigCombine](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelEdgeEncoding.lean)
-/
@[path]
private lemma rlc_twoChannel_bcProb_edgeConfigCombine_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {C : SimpleGraph (RlcConnectorVertex n)}
  [DecidableRel C.Adj]
  {p q : Real}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {outside : RlcTwoChannelOffGraphConfig gamma gamma'} :
-- imply
  FK.bcProb (rlc_connectorTwoChannelGraph gamma gamma') C p q (rlc_twoChannelEdgeConfigCombine gamma gamma' omega outside) = FK.bcProb (rlc_connectorTwoChannelGraph gamma gamma') C p q (rlc_twoChannelEdgeConfigExtend gamma gamma' omega) := by
-- proof
  apply StatMech.Universality.rlc_twoChannel_bcProb_edgeConfigCombine gamma gamma' C p q omega outside

/--
[rlc_twoChannelForcedDualEventMass_compl_le_merged_of_edgeEmbedding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelEdgeEncoding.lean)
-/
@[path]
private lemma rlc_twoChannelForcedDualEventMass_compl_le_merged_of_edgeEmbedding_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {q : Real}
-- given
  (hq : 1 <= q)
  (J : {omega : RlcTwoChannelEdgeConfig gamma gamma' // rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma'} ↪ {eta : RlcTwoChannelEdgeConfig gamma gamma' // rlc_twoChannelEdgeConfigExtend gamma gamma' eta ∈ rlc_finiteTwoChannelConnectorEvent gamma gamma'})
  (hprob : forall omega, rlc_twoChannelForcedDualProb gamma gamma' (BeffaraDC.selfDualPoint q) q (rlc_twoChannelEdgeConfigExtend gamma gamma' omega.1) <= FK.bcProb (rlc_connectorTwoChannelGraph gamma gamma') (rlc_connectorMergedWiring gamma gamma') (BeffaraDC.selfDualPoint q) q (rlc_twoChannelEdgeConfigExtend gamma gamma' (J omega).1)) :
-- imply
  rlc_twoChannelForcedDualEventMass gamma gamma' (BeffaraDC.selfDualPoint q) q (rlc_finiteTwoChannelConnectorEvent gamma gamma')ᶜ <= FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma') (rlc_connectorMergedWiring gamma gamma') (BeffaraDC.selfDualPoint q) q (rlc_finiteTwoChannelConnectorEvent gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_twoChannelForcedDualEventMass_compl_le_merged_of_edgeEmbedding gamma gamma' hq J hprob

/--
[rlc_twoChannelForcedDualEventMass_compl_le_mul_merged_of_edgeEmbedding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelEdgeEncoding.lean)
-/
@[path]
private lemma rlc_twoChannelForcedDualEventMass_compl_le_mul_merged_of_edgeEmbedding_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {q distortion : Real}
-- given
  (hq : 1 <= q)
  (hdistortion : 0 <= distortion)
  (J : {omega : RlcTwoChannelEdgeConfig gamma gamma' // rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma'} ↪ {eta : RlcTwoChannelEdgeConfig gamma gamma' // rlc_twoChannelEdgeConfigExtend gamma gamma' eta ∈ rlc_finiteTwoChannelConnectorEvent gamma gamma'})
  (hprob : forall omega, rlc_twoChannelForcedDualProb gamma gamma' (BeffaraDC.selfDualPoint q) q (rlc_twoChannelEdgeConfigExtend gamma gamma' omega.1) <= distortion * FK.bcProb (rlc_connectorTwoChannelGraph gamma gamma') (rlc_connectorMergedWiring gamma gamma') (BeffaraDC.selfDualPoint q) q (rlc_twoChannelEdgeConfigExtend gamma gamma' (J omega).1)) :
-- imply
  rlc_twoChannelForcedDualEventMass gamma gamma' (BeffaraDC.selfDualPoint q) q (rlc_finiteTwoChannelConnectorEvent gamma gamma')ᶜ <= distortion * FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma') (rlc_connectorMergedWiring gamma gamma') (BeffaraDC.selfDualPoint q) q (rlc_finiteTwoChannelConnectorEvent gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_twoChannelForcedDualEventMass_compl_le_mul_merged_of_edgeEmbedding gamma gamma' hq hdistortion J hprob

/--
[rlc_twoChannelForcedDualEventMass_compl_le_merged_q_one_of_edgeEmbedding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelEdgeEncoding.lean)
-/
@[path]
private lemma rlc_twoChannelForcedDualEventMass_compl_le_merged_q_one_of_edgeEmbedding_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
-- given
  (J : {omega : RlcTwoChannelEdgeConfig gamma gamma' // rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma'} ↪ {eta : RlcTwoChannelEdgeConfig gamma gamma' // rlc_twoChannelEdgeConfigExtend gamma gamma' eta ∈ rlc_finiteTwoChannelConnectorEvent gamma gamma'}) :
-- imply
  rlc_twoChannelForcedDualEventMass gamma gamma' (1 / 2) 1 (rlc_finiteTwoChannelConnectorEvent gamma gamma')ᶜ <= FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma') (rlc_connectorMergedWiring gamma gamma') (1 / 2) 1 (rlc_finiteTwoChannelConnectorEvent gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_twoChannelForcedDualEventMass_compl_le_merged_q_one_of_edgeEmbedding gamma gamma' J

/--
[rlc_twoChannelForcedDualEventMass_compl_le_merged_q_one_of_edgeCapacity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelEdgeEncoding.lean)
-/
@[path]
private lemma rlc_twoChannelForcedDualEventMass_compl_le_merged_q_one_of_edgeCapacity_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
-- given
  (hcard : Fintype.card {omega : RlcTwoChannelEdgeConfig gamma gamma' // rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma'} <= Fintype.card {eta : RlcTwoChannelEdgeConfig gamma gamma' // rlc_twoChannelEdgeConfigExtend gamma gamma' eta ∈ rlc_finiteTwoChannelConnectorEvent gamma gamma'}) :
-- imply
  rlc_twoChannelForcedDualEventMass gamma gamma' (1 / 2) 1 (rlc_finiteTwoChannelConnectorEvent gamma gamma')ᶜ <= FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma') (rlc_connectorMergedWiring gamma gamma') (1 / 2) 1 (rlc_finiteTwoChannelConnectorEvent gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_twoChannelForcedDualEventMass_compl_le_merged_q_one_of_edgeCapacity gamma gamma' hcard


-- created on 2026-10-23
