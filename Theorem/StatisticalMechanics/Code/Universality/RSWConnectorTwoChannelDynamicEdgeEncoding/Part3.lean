/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelDynamicEdgeEncoding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelEdgeEncoding.Part2
import Theorem.StatisticalMechanics.Code.FK.SelfDualPointMassScore
import Theorem.StatisticalMechanics.Code.FK.BoundaryScoreLipschitz
import Theorem.StatisticalMechanics.Code.FrontierD.FKBoundarySingleMerge
import Def.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelDynamicEdgeEncoding.Part4
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem
    rlc_twoChannelForcedDualEventMass_compl_le_merged_q_one_of_dynamicRouteHall
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (P : RlcTwoChannelDynamicRoutePlan gamma gamma')
    (routeAvailable : RlcTwoChannelEdgeFailure gamma gamma' → P.Route → Prop)
    (hHall : P.HasCodeHall routeAvailable) :
    rlc_twoChannelForcedDualEventMass gamma gamma' (1 / 2) 1
        (rlc_finiteTwoChannelConnectorEvent gamma gamma')ᶜ <=
      FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_connectorMergedWiring gamma gamma') (1 / 2) 1
        (rlc_finiteTwoChannelConnectorEvent gamma gamma') := by
  exact rlc_twoChannelForcedDualEventMass_compl_le_merged_q_one_of_edgeCodeHall
    gamma gamma' (P.Compatible routeAvailable) hHall


theorem rlc_twoChannelForcedDualEventMass_compl_le_merged_of_dynamicRouteHall
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    {q : Real} (hq : 1 <= q)
    (P : RlcTwoChannelDynamicRoutePlan gamma gamma')
    (routeAvailable : RlcTwoChannelEdgeFailure gamma gamma' → P.Route → Prop)
    (hHall : P.HasCodeHall routeAvailable)
    (hdom : ∀ rho eta, P.Compatible routeAvailable rho eta →
      rlc_twoChannelForcedDualProb gamma gamma'
          (BeffaraDC.selfDualPoint q) q
          (rlc_twoChannelEdgeConfigExtend gamma gamma' rho.1) <=
        FK.bcProb (rlc_connectorTwoChannelGraph gamma gamma')
          (rlc_connectorMergedWiring gamma gamma')
          (BeffaraDC.selfDualPoint q) q
          (rlc_twoChannelEdgeConfigExtend gamma gamma' eta.1)) :
    rlc_twoChannelForcedDualEventMass gamma gamma'
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteTwoChannelConnectorEvent gamma gamma')ᶜ <=
      FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_connectorMergedWiring gamma gamma')
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteTwoChannelConnectorEvent gamma gamma') := by
  exact rlc_twoChannelForcedDualEventMass_compl_le_merged_of_edgeCodeHall
    gamma gamma' hq (P.Compatible routeAvailable) hHall hdom


theorem
    rlc_twoChannelForcedDualEventMass_compl_le_mul_merged_of_dynamicRouteHall
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    {q distortion : Real} (hq : 1 <= q) (hdistortion : 0 <= distortion)
    (P : RlcTwoChannelDynamicRoutePlan gamma gamma')
    (routeAvailable : RlcTwoChannelEdgeFailure gamma gamma' -> P.Route -> Prop)
    (hHall : P.HasCodeHall routeAvailable)
    (hdom : forall rho eta, P.Compatible routeAvailable rho eta ->
      rlc_twoChannelForcedDualProb gamma gamma'
          (BeffaraDC.selfDualPoint q) q
          (rlc_twoChannelEdgeConfigExtend gamma gamma' rho.1) <=
        distortion *
          FK.bcProb (rlc_connectorTwoChannelGraph gamma gamma')
            (rlc_connectorMergedWiring gamma gamma')
            (BeffaraDC.selfDualPoint q) q
            (rlc_twoChannelEdgeConfigExtend gamma gamma' eta.1)) :
    rlc_twoChannelForcedDualEventMass gamma gamma'
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteTwoChannelConnectorEvent gamma gamma')ᶜ <=
      distortion *
        FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma')
          (rlc_connectorMergedWiring gamma gamma')
          (BeffaraDC.selfDualPoint q) q
          (rlc_finiteTwoChannelConnectorEvent gamma gamma') := by
  exact
    rlc_twoChannelForcedDualEventMass_compl_le_mul_merged_of_edgeCodeHall
      gamma gamma' hq hdistortion (P.Compatible routeAvailable) hHall hdom


theorem
    rlc_twoChannelForcedDualEventMass_compl_le_qpow_merged_of_dynamicRouteHall_score
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    {q : Real} (hq : 1 <= q) (N : Nat)
    (P : RlcTwoChannelDynamicRoutePlan gamma gamma')
    (routeAvailable : RlcTwoChannelEdgeFailure gamma gamma' -> P.Route -> Prop)
    (hHall : P.HasCodeHall routeAvailable)
    (hscore : forall rho eta, P.Compatible routeAvailable rho eta ->
      FK.openCount (rlc_connectorTwoChannelGraph gamma gamma')
          (rlc_twoChannelEdgeConfigExtend gamma gamma' rho.1) +
          2 * FK.numClustersBC
            (rlc_connectorTwoChannelGraph gamma gamma')
            (rlc_connectorSeparateWiring gamma gamma')
            (rlc_twoChannelEdgeConfigExtend gamma gamma' rho.1) <=
        FK.openCount (rlc_connectorTwoChannelGraph gamma gamma')
            (rlc_twoChannelEdgeConfigExtend gamma gamma' eta.1) +
          2 * FK.numClustersBC
            (rlc_connectorTwoChannelGraph gamma gamma')
            (rlc_connectorMergedWiring gamma gamma')
            (rlc_twoChannelEdgeConfigExtend gamma gamma' eta.1) + N) :
    rlc_twoChannelForcedDualEventMass gamma gamma'
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteTwoChannelConnectorEvent gamma gamma')ᶜ <=
      q ^ N *
        FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma')
          (rlc_connectorMergedWiring gamma gamma')
          (BeffaraDC.selfDualPoint q) q
          (rlc_finiteTwoChannelConnectorEvent gamma gamma') := by
  exact
    rlc_twoChannelForcedDualEventMass_compl_le_qpow_merged_of_edgeCodeHall_score
      gamma gamma' hq N (P.Compatible routeAvailable) hHall hscore


theorem
    rlc_twoChannelForcedDualEventMass_compl_le_sqrt_pow_merged_of_dynamicRouteHall_score
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    {q : Real} (hq : 1 <= q) (N : Nat)
    (P : RlcTwoChannelDynamicRoutePlan gamma gamma')
    (routeAvailable : RlcTwoChannelEdgeFailure gamma gamma' -> P.Route -> Prop)
    (hHall : P.HasCodeHall routeAvailable)
    (hscore : forall rho eta, P.Compatible routeAvailable rho eta ->
      FK.openCount (rlc_connectorTwoChannelGraph gamma gamma')
          (rlc_twoChannelEdgeConfigExtend gamma gamma' rho.1) +
          2 * FK.numClustersBC
            (rlc_connectorTwoChannelGraph gamma gamma')
            (rlc_connectorSeparateWiring gamma gamma')
            (rlc_twoChannelEdgeConfigExtend gamma gamma' rho.1) <=
        FK.openCount (rlc_connectorTwoChannelGraph gamma gamma')
            (rlc_twoChannelEdgeConfigExtend gamma gamma' eta.1) +
          2 * FK.numClustersBC
            (rlc_connectorTwoChannelGraph gamma gamma')
            (rlc_connectorMergedWiring gamma gamma')
            (rlc_twoChannelEdgeConfigExtend gamma gamma' eta.1) + N) :
    rlc_twoChannelForcedDualEventMass gamma gamma'
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteTwoChannelConnectorEvent gamma gamma')ᶜ <=
      (Real.sqrt q) ^ N *
        FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma')
          (rlc_connectorMergedWiring gamma gamma')
          (BeffaraDC.selfDualPoint q) q
          (rlc_finiteTwoChannelConnectorEvent gamma gamma') := by
  exact
    rlc_twoChannelForcedDualEventMass_compl_le_sqrt_pow_merged_of_edgeCodeHall_score
      gamma gamma' hq N (P.Compatible routeAvailable) hHall hscore


theorem
    rlc_twoChannelForcedDualEventMass_compl_le_sqrt_pow_merged_of_dynamicRouteHall_hamming
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    {q : Real} (hq : 1 <= q) (K : Nat)
    (P : RlcTwoChannelDynamicRoutePlan gamma gamma')
    (routeAvailable : RlcTwoChannelEdgeFailure gamma gamma' -> P.Route -> Prop)
    (hHall : P.HasCodeHall routeAvailable)
    (hHamming : forall rho eta, P.Compatible routeAvailable rho eta ->
      FK.configHammingCount (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_twoChannelEdgeConfigExtend gamma gamma' rho.1)
        (rlc_twoChannelEdgeConfigExtend gamma gamma' eta.1) <= K) :
    rlc_twoChannelForcedDualEventMass gamma gamma'
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteTwoChannelConnectorEvent gamma gamma')ᶜ <=
      (Real.sqrt q) ^ (K + 2) *
        FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma')
          (rlc_connectorMergedWiring gamma gamma')
          (BeffaraDC.selfDualPoint q) q
          (rlc_finiteTwoChannelConnectorEvent gamma gamma') := by
  exact
    rlc_twoChannelForcedDualEventMass_compl_le_sqrt_pow_merged_of_edgeCodeHall_hamming
      gamma gamma' hq K (P.Compatible routeAvailable) hHall hHamming

end
end StatMech.Universality
