import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelScoreAudit.Part2
open Finset SimpleGraph Set StatMech StatMech.Universality


/--
[rlc_twoChannelEdgeConfigExtend_eq_extendActive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelScoreAudit.lean)
-/
@[path]
private lemma rlc_twoChannelEdgeConfigExtend_eq_extendActive_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'} :
-- imply
  rlc_twoChannelEdgeConfigExtend gamma gamma' omega = FK.extendActive (rlc_connectorTwoChannelGraph gamma gamma') omega := by
-- proof
  apply StatMech.Universality.rlc_twoChannelEdgeConfigExtend_eq_extendActive gamma gamma' omega

/--
[rlc_twoChannelFullPhysicalPermConfig_activeOpenCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelScoreAudit.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysicalPermConfig_activeOpenCount_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'} :
-- imply
  FK.activeOpenCount (rlc_connectorTwoChannelGraph gamma gamma') (rlc_twoChannelFullPhysicalPermConfig gamma gamma' omega) = Fintype.card (rlc_connectorTwoChannelGraph gamma gamma').edgeSet - FK.activeOpenCount (rlc_connectorTwoChannelGraph gamma gamma') omega := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysicalPermConfig_activeOpenCount gamma gamma' omega

/--
[rlc_twoChannelFullPhysicalPermConfig_openCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelScoreAudit.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysicalPermConfig_openCount_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'} :
-- imply
  FK.openCount (rlc_connectorTwoChannelGraph gamma gamma') (rlc_twoChannelEdgeConfigExtend gamma gamma' (rlc_twoChannelFullPhysicalPermConfig gamma gamma' omega)) = (rlc_connectorTwoChannelGraph gamma gamma').edgeFinset.card - FK.openCount (rlc_connectorTwoChannelGraph gamma gamma') (rlc_twoChannelEdgeConfigExtend gamma gamma' omega) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysicalPermConfig_openCount gamma gamma' omega

/--
[rlc_twoChannelForced_clusterEuler](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelScoreAudit.lean)
-/
@[path]
private lemma rlc_twoChannelForced_clusterEuler_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))} :
-- imply
  let P := rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma' let K := FK.openSub P.G (rlc_connectorForceTraceConfig gamma gamma' rho) Nat.card P.V + Nat.card (BeffaraDC.pfdClosedDual P K).ConnectedComponent = K.edgeSet.ncard + FK.numClustersBC (rlc_connectorTwoChannelGraph gamma gamma') (rlc_connectorSeparateWiring gamma gamma') rho + 1 := by
-- proof
  apply StatMech.Universality.rlc_twoChannelForced_clusterEuler gamma gamma' rho

/--
[rlc_twoChannelForced_openCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelScoreAudit.lean)
-/
@[path]
private lemma rlc_twoChannelForced_openCount_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))} :
-- imply
  FK.openCount (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma').G (rlc_connectorForceTraceConfig gamma gamma' rho) = FK.openCount (rlc_connectorTwoChannelGraph gamma gamma') rho + (rlc_connectorTraceWiring gamma gamma').edgeFinset.card := by
-- proof
  apply StatMech.Universality.rlc_twoChannelForced_openCount gamma gamma' rho

/--
[rlc_twoChannelForced_clusterEuler_openCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelScoreAudit.lean)
-/
@[path]
private lemma rlc_twoChannelForced_clusterEuler_openCount_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))} :
-- imply
  let P := rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma' let K := FK.openSub P.G (rlc_connectorForceTraceConfig gamma gamma' rho) Nat.card P.V + Nat.card (BeffaraDC.pfdClosedDual P K).ConnectedComponent = FK.openCount (rlc_connectorTwoChannelGraph gamma gamma') rho + (rlc_connectorTraceWiring gamma gamma').edgeFinset.card + FK.numClustersBC (rlc_connectorTwoChannelGraph gamma gamma') (rlc_connectorSeparateWiring gamma gamma') rho + 1 := by
-- proof
  apply StatMech.Universality.rlc_twoChannelForced_clusterEuler_openCount gamma gamma' rho

/--
[rlc_twoChannelFullPhysicalPermutationScoreDefect_iff_eulerScoreBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelScoreAudit.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysicalPermutationScoreDefect_iff_eulerScoreBound_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {N : Nat} :
-- imply
  RlcTwoChannelFullPhysicalPermutationScoreDefect gamma gamma' N ↔ RlcTwoChannelFullPhysicalEulerScoreBound gamma gamma' N := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysicalPermutationScoreDefect_iff_eulerScoreBound gamma gamma' N


-- created on 2026-10-23
