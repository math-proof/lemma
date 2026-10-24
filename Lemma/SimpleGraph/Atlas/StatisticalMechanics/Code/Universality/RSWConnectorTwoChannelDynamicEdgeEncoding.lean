import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelDynamicEdgeEncoding
open Finset SimpleGraph Set StatMech StatMech.Universality


/--
[RlcTwoChannelDynamicRoutePlan.code_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelDynamicEdgeEncoding.lean)
-/
@[path]
private lemma code_card_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {P : RlcTwoChannelDynamicRoutePlan gamma gamma'}
  {route : P.Route} :
-- imply
  Fintype.card (P.Code route) = 2 ^ (P.payloadSlots route).card := by
-- proof
  apply StatMech.Universality.RlcTwoChannelDynamicRoutePlan.code_card P route

/--
[rlc_twoChannelEdgeCodeHall_iff_exists_compatibleEmbedding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelDynamicEdgeEncoding.lean)
-/
@[path]
private lemma rlc_twoChannelEdgeCodeHall_iff_exists_compatibleEmbedding_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
-- given
  (Compatible : RlcTwoChannelEdgeFailure gamma gamma' → RlcTwoChannelEdgeSuccess gamma gamma' → Prop) :
-- imply
  RlcTwoChannelEdgeCodeHall gamma gamma' Compatible ↔ ∃ J : RlcTwoChannelEdgeFailure gamma gamma' ↪ RlcTwoChannelEdgeSuccess gamma gamma', ∀ rho, Compatible rho (J rho) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelEdgeCodeHall_iff_exists_compatibleEmbedding gamma gamma' Compatible

/--
[rlc_twoChannelForcedDualEventMass_compl_le_merged_q_one_of_edgeCodeHall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelDynamicEdgeEncoding.lean)
-/
@[path]
private lemma rlc_twoChannelForcedDualEventMass_compl_le_merged_q_one_of_edgeCodeHall_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
-- given
  (Compatible : RlcTwoChannelEdgeFailure gamma gamma' → RlcTwoChannelEdgeSuccess gamma gamma' → Prop)
  (hHall : RlcTwoChannelEdgeCodeHall gamma gamma' Compatible) :
-- imply
  rlc_twoChannelForcedDualEventMass gamma gamma' (1 / 2) 1 (rlc_finiteTwoChannelConnectorEvent gamma gamma')ᶜ <= FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma') (rlc_connectorMergedWiring gamma gamma') (1 / 2) 1 (rlc_finiteTwoChannelConnectorEvent gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_twoChannelForcedDualEventMass_compl_le_merged_q_one_of_edgeCodeHall gamma gamma' Compatible hHall

/--
[rlc_twoChannelForcedDualEventMass_compl_le_merged_of_edgeCodeHall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelDynamicEdgeEncoding.lean)
-/
@[path]
private lemma rlc_twoChannelForcedDualEventMass_compl_le_merged_of_edgeCodeHall_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {q : Real}
-- given
  (hq : 1 <= q)
  (Compatible : RlcTwoChannelEdgeFailure gamma gamma' → RlcTwoChannelEdgeSuccess gamma gamma' → Prop)
  (hHall : RlcTwoChannelEdgeCodeHall gamma gamma' Compatible)
  (hdom : ∀ rho eta, Compatible rho eta → rlc_twoChannelForcedDualProb gamma gamma' (BeffaraDC.selfDualPoint q) q (rlc_twoChannelEdgeConfigExtend gamma gamma' rho.1) <= FK.bcProb (rlc_connectorTwoChannelGraph gamma gamma') (rlc_connectorMergedWiring gamma gamma') (BeffaraDC.selfDualPoint q) q (rlc_twoChannelEdgeConfigExtend gamma gamma' eta.1)) :
-- imply
  rlc_twoChannelForcedDualEventMass gamma gamma' (BeffaraDC.selfDualPoint q) q (rlc_finiteTwoChannelConnectorEvent gamma gamma')ᶜ <= FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma') (rlc_connectorMergedWiring gamma gamma') (BeffaraDC.selfDualPoint q) q (rlc_finiteTwoChannelConnectorEvent gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_twoChannelForcedDualEventMass_compl_le_merged_of_edgeCodeHall gamma gamma' hq Compatible hHall hdom

/--
[rlc_twoChannelForcedDualEventMass_compl_le_mul_merged_of_edgeCodeHall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelDynamicEdgeEncoding.lean)
-/
@[path]
private lemma rlc_twoChannelForcedDualEventMass_compl_le_mul_merged_of_edgeCodeHall_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {q distortion : Real}
-- given
  (hq : 1 <= q)
  (hdistortion : 0 <= distortion)
  (Compatible : RlcTwoChannelEdgeFailure gamma gamma' -> RlcTwoChannelEdgeSuccess gamma gamma' -> Prop)
  (hHall : RlcTwoChannelEdgeCodeHall gamma gamma' Compatible)
  (hdom : forall rho eta, Compatible rho eta -> rlc_twoChannelForcedDualProb gamma gamma' (BeffaraDC.selfDualPoint q) q (rlc_twoChannelEdgeConfigExtend gamma gamma' rho.1) <= distortion * FK.bcProb (rlc_connectorTwoChannelGraph gamma gamma') (rlc_connectorMergedWiring gamma gamma') (BeffaraDC.selfDualPoint q) q (rlc_twoChannelEdgeConfigExtend gamma gamma' eta.1)) :
-- imply
  rlc_twoChannelForcedDualEventMass gamma gamma' (BeffaraDC.selfDualPoint q) q (rlc_finiteTwoChannelConnectorEvent gamma gamma')ᶜ <= distortion * FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma') (rlc_connectorMergedWiring gamma gamma') (BeffaraDC.selfDualPoint q) q (rlc_finiteTwoChannelConnectorEvent gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_twoChannelForcedDualEventMass_compl_le_mul_merged_of_edgeCodeHall gamma gamma' hq hdistortion Compatible hHall hdom

/--
[rlc_twoChannelForcedDualEventMass_compl_le_sqrt_pow_merged_of_edgeCodeHall_score](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelDynamicEdgeEncoding.lean)
-/
@[path]
private lemma rlc_twoChannelForcedDualEventMass_compl_le_sqrt_pow_merged_of_edgeCodeHall_score_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {q : Real}
  {N : Nat}
-- given
  (hq : 1 <= q)
  (Compatible : RlcTwoChannelEdgeFailure gamma gamma' -> RlcTwoChannelEdgeSuccess gamma gamma' -> Prop)
  (hHall : RlcTwoChannelEdgeCodeHall gamma gamma' Compatible)
  (hscore : forall rho eta, Compatible rho eta -> FK.openCount (rlc_connectorTwoChannelGraph gamma gamma') (rlc_twoChannelEdgeConfigExtend gamma gamma' rho.1) + 2 * FK.numClustersBC (rlc_connectorTwoChannelGraph gamma gamma') (rlc_connectorSeparateWiring gamma gamma') (rlc_twoChannelEdgeConfigExtend gamma gamma' rho.1) <= FK.openCount (rlc_connectorTwoChannelGraph gamma gamma') (rlc_twoChannelEdgeConfigExtend gamma gamma' eta.1) + 2 * FK.numClustersBC (rlc_connectorTwoChannelGraph gamma gamma') (rlc_connectorMergedWiring gamma gamma') (rlc_twoChannelEdgeConfigExtend gamma gamma' eta.1) + N) :
-- imply
  rlc_twoChannelForcedDualEventMass gamma gamma' (BeffaraDC.selfDualPoint q) q (rlc_finiteTwoChannelConnectorEvent gamma gamma')ᶜ <= (Real.sqrt q) ^ N * FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma') (rlc_connectorMergedWiring gamma gamma') (BeffaraDC.selfDualPoint q) q (rlc_finiteTwoChannelConnectorEvent gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_twoChannelForcedDualEventMass_compl_le_sqrt_pow_merged_of_edgeCodeHall_score gamma gamma' hq N Compatible hHall hscore

/--
[rlc_twoChannel_score_le_hamming_add_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelDynamicEdgeEncoding.lean)
-/
@[path]
private lemma rlc_twoChannel_score_le_hamming_add_two_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega eta : ConfigSpace (Sym2 (RlcConnectorVertex n))} :
-- imply
  FK.openCount (rlc_connectorTwoChannelGraph gamma gamma') omega + 2 * FK.numClustersBC (rlc_connectorTwoChannelGraph gamma gamma') (rlc_connectorSeparateWiring gamma gamma') omega <= FK.openCount (rlc_connectorTwoChannelGraph gamma gamma') eta + 2 * FK.numClustersBC (rlc_connectorTwoChannelGraph gamma gamma') (rlc_connectorMergedWiring gamma gamma') eta + FK.configHammingCount (rlc_connectorTwoChannelGraph gamma gamma') omega eta + 2 := by
-- proof
  apply StatMech.Universality.rlc_twoChannel_score_le_hamming_add_two gamma gamma' omega eta

/--
[rlc_twoChannelForcedDualEventMass_compl_le_sqrt_pow_merged_of_edgeCodeHall_hamming](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelDynamicEdgeEncoding.lean)
-/
@[path]
private lemma rlc_twoChannelForcedDualEventMass_compl_le_sqrt_pow_merged_of_edgeCodeHall_hamming_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {q : Real}
  {K : Nat}
-- given
  (hq : 1 <= q)
  (Compatible : RlcTwoChannelEdgeFailure gamma gamma' -> RlcTwoChannelEdgeSuccess gamma gamma' -> Prop)
  (hHall : RlcTwoChannelEdgeCodeHall gamma gamma' Compatible)
  (hHamming : forall rho eta, Compatible rho eta -> FK.configHammingCount (rlc_connectorTwoChannelGraph gamma gamma') (rlc_twoChannelEdgeConfigExtend gamma gamma' rho.1) (rlc_twoChannelEdgeConfigExtend gamma gamma' eta.1) <= K) :
-- imply
  rlc_twoChannelForcedDualEventMass gamma gamma' (BeffaraDC.selfDualPoint q) q (rlc_finiteTwoChannelConnectorEvent gamma gamma')ᶜ <= (Real.sqrt q) ^ (K + 2) * FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma') (rlc_connectorMergedWiring gamma gamma') (BeffaraDC.selfDualPoint q) q (rlc_finiteTwoChannelConnectorEvent gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_twoChannelForcedDualEventMass_compl_le_sqrt_pow_merged_of_edgeCodeHall_hamming gamma gamma' hq K Compatible hHall hHamming

/--
[rlc_twoChannelForcedDualEventMass_compl_le_qpow_merged_of_edgeCodeHall_score](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelDynamicEdgeEncoding.lean)
-/
@[path]
private lemma rlc_twoChannelForcedDualEventMass_compl_le_qpow_merged_of_edgeCodeHall_score_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {q : Real}
  {N : Nat}
-- given
  (hq : 1 <= q)
  (Compatible : RlcTwoChannelEdgeFailure gamma gamma' -> RlcTwoChannelEdgeSuccess gamma gamma' -> Prop)
  (hHall : RlcTwoChannelEdgeCodeHall gamma gamma' Compatible)
  (hscore : forall rho eta, Compatible rho eta -> FK.openCount (rlc_connectorTwoChannelGraph gamma gamma') (rlc_twoChannelEdgeConfigExtend gamma gamma' rho.1) + 2 * FK.numClustersBC (rlc_connectorTwoChannelGraph gamma gamma') (rlc_connectorSeparateWiring gamma gamma') (rlc_twoChannelEdgeConfigExtend gamma gamma' rho.1) <= FK.openCount (rlc_connectorTwoChannelGraph gamma gamma') (rlc_twoChannelEdgeConfigExtend gamma gamma' eta.1) + 2 * FK.numClustersBC (rlc_connectorTwoChannelGraph gamma gamma') (rlc_connectorMergedWiring gamma gamma') (rlc_twoChannelEdgeConfigExtend gamma gamma' eta.1) + N) :
-- imply
  rlc_twoChannelForcedDualEventMass gamma gamma' (BeffaraDC.selfDualPoint q) q (rlc_finiteTwoChannelConnectorEvent gamma gamma')ᶜ <= q ^ N * FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma') (rlc_connectorMergedWiring gamma gamma') (BeffaraDC.selfDualPoint q) q (rlc_finiteTwoChannelConnectorEvent gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_twoChannelForcedDualEventMass_compl_le_qpow_merged_of_edgeCodeHall_score gamma gamma' hq N Compatible hHall hscore

/--
[rlc_twoChannelForcedDualEventMass_compl_le_merged_q_one_of_dynamicRouteHall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelDynamicEdgeEncoding.lean)
-/
@[path]
private lemma rlc_twoChannelForcedDualEventMass_compl_le_merged_q_one_of_dynamicRouteHall_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {P : RlcTwoChannelDynamicRoutePlan gamma gamma'}
-- given
  (routeAvailable : RlcTwoChannelEdgeFailure gamma gamma' → P.Route → Prop)
  (hHall : P.HasCodeHall routeAvailable) :
-- imply
  rlc_twoChannelForcedDualEventMass gamma gamma' (1 / 2) 1 (rlc_finiteTwoChannelConnectorEvent gamma gamma')ᶜ <= FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma') (rlc_connectorMergedWiring gamma gamma') (1 / 2) 1 (rlc_finiteTwoChannelConnectorEvent gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_twoChannelForcedDualEventMass_compl_le_merged_q_one_of_dynamicRouteHall gamma gamma' P routeAvailable hHall

/--
[rlc_twoChannelForcedDualEventMass_compl_le_merged_of_dynamicRouteHall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelDynamicEdgeEncoding.lean)
-/
@[path]
private lemma rlc_twoChannelForcedDualEventMass_compl_le_merged_of_dynamicRouteHall_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {q : Real}
  {P : RlcTwoChannelDynamicRoutePlan gamma gamma'}
-- given
  (hq : 1 <= q)
  (routeAvailable : RlcTwoChannelEdgeFailure gamma gamma' → P.Route → Prop)
  (hHall : P.HasCodeHall routeAvailable)
  (hdom : ∀ rho eta, P.Compatible routeAvailable rho eta → rlc_twoChannelForcedDualProb gamma gamma' (BeffaraDC.selfDualPoint q) q (rlc_twoChannelEdgeConfigExtend gamma gamma' rho.1) <= FK.bcProb (rlc_connectorTwoChannelGraph gamma gamma') (rlc_connectorMergedWiring gamma gamma') (BeffaraDC.selfDualPoint q) q (rlc_twoChannelEdgeConfigExtend gamma gamma' eta.1)) :
-- imply
  rlc_twoChannelForcedDualEventMass gamma gamma' (BeffaraDC.selfDualPoint q) q (rlc_finiteTwoChannelConnectorEvent gamma gamma')ᶜ <= FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma') (rlc_connectorMergedWiring gamma gamma') (BeffaraDC.selfDualPoint q) q (rlc_finiteTwoChannelConnectorEvent gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_twoChannelForcedDualEventMass_compl_le_merged_of_dynamicRouteHall gamma gamma' hq P routeAvailable hHall hdom

/--
[rlc_twoChannelForcedDualEventMass_compl_le_mul_merged_of_dynamicRouteHall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelDynamicEdgeEncoding.lean)
-/
@[path]
private lemma rlc_twoChannelForcedDualEventMass_compl_le_mul_merged_of_dynamicRouteHall_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {q distortion : Real}
  {P : RlcTwoChannelDynamicRoutePlan gamma gamma'}
-- given
  (hq : 1 <= q)
  (hdistortion : 0 <= distortion)
  (routeAvailable : RlcTwoChannelEdgeFailure gamma gamma' -> P.Route -> Prop)
  (hHall : P.HasCodeHall routeAvailable)
  (hdom : forall rho eta, P.Compatible routeAvailable rho eta -> rlc_twoChannelForcedDualProb gamma gamma' (BeffaraDC.selfDualPoint q) q (rlc_twoChannelEdgeConfigExtend gamma gamma' rho.1) <= distortion * FK.bcProb (rlc_connectorTwoChannelGraph gamma gamma') (rlc_connectorMergedWiring gamma gamma') (BeffaraDC.selfDualPoint q) q (rlc_twoChannelEdgeConfigExtend gamma gamma' eta.1)) :
-- imply
  rlc_twoChannelForcedDualEventMass gamma gamma' (BeffaraDC.selfDualPoint q) q (rlc_finiteTwoChannelConnectorEvent gamma gamma')ᶜ <= distortion * FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma') (rlc_connectorMergedWiring gamma gamma') (BeffaraDC.selfDualPoint q) q (rlc_finiteTwoChannelConnectorEvent gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_twoChannelForcedDualEventMass_compl_le_mul_merged_of_dynamicRouteHall gamma gamma' hq hdistortion P routeAvailable hHall hdom

/--
[rlc_twoChannelForcedDualEventMass_compl_le_qpow_merged_of_dynamicRouteHall_score](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelDynamicEdgeEncoding.lean)
-/
@[path]
private lemma rlc_twoChannelForcedDualEventMass_compl_le_qpow_merged_of_dynamicRouteHall_score_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {q : Real}
  {N : Nat}
  {P : RlcTwoChannelDynamicRoutePlan gamma gamma'}
-- given
  (hq : 1 <= q)
  (routeAvailable : RlcTwoChannelEdgeFailure gamma gamma' -> P.Route -> Prop)
  (hHall : P.HasCodeHall routeAvailable)
  (hscore : forall rho eta, P.Compatible routeAvailable rho eta -> FK.openCount (rlc_connectorTwoChannelGraph gamma gamma') (rlc_twoChannelEdgeConfigExtend gamma gamma' rho.1) + 2 * FK.numClustersBC (rlc_connectorTwoChannelGraph gamma gamma') (rlc_connectorSeparateWiring gamma gamma') (rlc_twoChannelEdgeConfigExtend gamma gamma' rho.1) <= FK.openCount (rlc_connectorTwoChannelGraph gamma gamma') (rlc_twoChannelEdgeConfigExtend gamma gamma' eta.1) + 2 * FK.numClustersBC (rlc_connectorTwoChannelGraph gamma gamma') (rlc_connectorMergedWiring gamma gamma') (rlc_twoChannelEdgeConfigExtend gamma gamma' eta.1) + N) :
-- imply
  rlc_twoChannelForcedDualEventMass gamma gamma' (BeffaraDC.selfDualPoint q) q (rlc_finiteTwoChannelConnectorEvent gamma gamma')ᶜ <= q ^ N * FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma') (rlc_connectorMergedWiring gamma gamma') (BeffaraDC.selfDualPoint q) q (rlc_finiteTwoChannelConnectorEvent gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_twoChannelForcedDualEventMass_compl_le_qpow_merged_of_dynamicRouteHall_score gamma gamma' hq N P routeAvailable hHall hscore

/--
[rlc_twoChannelForcedDualEventMass_compl_le_sqrt_pow_merged_of_dynamicRouteHall_score](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelDynamicEdgeEncoding.lean)
-/
@[path]
private lemma rlc_twoChannelForcedDualEventMass_compl_le_sqrt_pow_merged_of_dynamicRouteHall_score_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {q : Real}
  {N : Nat}
  {P : RlcTwoChannelDynamicRoutePlan gamma gamma'}
-- given
  (hq : 1 <= q)
  (routeAvailable : RlcTwoChannelEdgeFailure gamma gamma' -> P.Route -> Prop)
  (hHall : P.HasCodeHall routeAvailable)
  (hscore : forall rho eta, P.Compatible routeAvailable rho eta -> FK.openCount (rlc_connectorTwoChannelGraph gamma gamma') (rlc_twoChannelEdgeConfigExtend gamma gamma' rho.1) + 2 * FK.numClustersBC (rlc_connectorTwoChannelGraph gamma gamma') (rlc_connectorSeparateWiring gamma gamma') (rlc_twoChannelEdgeConfigExtend gamma gamma' rho.1) <= FK.openCount (rlc_connectorTwoChannelGraph gamma gamma') (rlc_twoChannelEdgeConfigExtend gamma gamma' eta.1) + 2 * FK.numClustersBC (rlc_connectorTwoChannelGraph gamma gamma') (rlc_connectorMergedWiring gamma gamma') (rlc_twoChannelEdgeConfigExtend gamma gamma' eta.1) + N) :
-- imply
  rlc_twoChannelForcedDualEventMass gamma gamma' (BeffaraDC.selfDualPoint q) q (rlc_finiteTwoChannelConnectorEvent gamma gamma')ᶜ <= (Real.sqrt q) ^ N * FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma') (rlc_connectorMergedWiring gamma gamma') (BeffaraDC.selfDualPoint q) q (rlc_finiteTwoChannelConnectorEvent gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_twoChannelForcedDualEventMass_compl_le_sqrt_pow_merged_of_dynamicRouteHall_score gamma gamma' hq N P routeAvailable hHall hscore

/--
[rlc_twoChannelForcedDualEventMass_compl_le_sqrt_pow_merged_of_dynamicRouteHall_hamming](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelDynamicEdgeEncoding.lean)
-/
@[path]
private lemma rlc_twoChannelForcedDualEventMass_compl_le_sqrt_pow_merged_of_dynamicRouteHall_hamming_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {q : Real}
  {K : Nat}
  {P : RlcTwoChannelDynamicRoutePlan gamma gamma'}
-- given
  (hq : 1 <= q)
  (routeAvailable : RlcTwoChannelEdgeFailure gamma gamma' -> P.Route -> Prop)
  (hHall : P.HasCodeHall routeAvailable)
  (hHamming : forall rho eta, P.Compatible routeAvailable rho eta -> FK.configHammingCount (rlc_connectorTwoChannelGraph gamma gamma') (rlc_twoChannelEdgeConfigExtend gamma gamma' rho.1) (rlc_twoChannelEdgeConfigExtend gamma gamma' eta.1) <= K) :
-- imply
  rlc_twoChannelForcedDualEventMass gamma gamma' (BeffaraDC.selfDualPoint q) q (rlc_finiteTwoChannelConnectorEvent gamma gamma')ᶜ <= (Real.sqrt q) ^ (K + 2) * FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma') (rlc_connectorMergedWiring gamma gamma') (BeffaraDC.selfDualPoint q) q (rlc_finiteTwoChannelConnectorEvent gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_twoChannelForcedDualEventMass_compl_le_sqrt_pow_merged_of_dynamicRouteHall_hamming gamma gamma' hq K P routeAvailable hHall hHamming


-- created on 2026-10-23
