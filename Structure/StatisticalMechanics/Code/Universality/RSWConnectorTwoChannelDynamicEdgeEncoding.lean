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
import Abbrev.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelDynamicEdgeEncoding
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

structure RlcTwoChannelDynamicRoutePlan {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) where
  Route : Type
  reservedEdges : Route →
    Finset (rlc_connectorTwoChannelGraph gamma gamma').edgeSet
  payloadSlots : Route →
    Finset (rlc_connectorTwoChannelGraph gamma gamma').edgeSet
  reservedEdges_disjoint_payloadSlots : ∀ route,
    Disjoint (reservedEdges route) (payloadSlots route)
  tagState : Route → RlcTwoChannelEdgeConfig gamma gamma'
  success_of_reserved : ∀ route eta,
    (∀ e, e ∈ reservedEdges route → eta e = true) →
      rlc_twoChannelEdgeConfigExtend gamma gamma' eta ∈
        rlc_finiteTwoChannelConnectorEvent gamma gamma'

end
end StatMech.Universality
