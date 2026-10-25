/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelCanonicalRoute.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelDynamicEdgeEncoding.Part3
import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelCanonicalRoute.Part11
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

noncomputable def rlc_twoChannelCanonicalRoutePlan {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    RlcTwoChannelDynamicRoutePlan gamma gamma' where
  Route := RlcTwoChannelEdgeSuccess gamma gamma'
  reservedEdges route := rlc_twoChannelOpenEdgeSet route.1
  payloadSlots route := Finset.univ \ rlc_twoChannelOpenEdgeSet route.1
  reservedEdges_disjoint_payloadSlots route := by
    exact Finset.disjoint_sdiff
  tagState _ := fun _ => false
  success_of_reserved route eta hopen := by
    have hle :
        rlc_twoChannelEdgeConfigExtend gamma gamma' route.1 ≤
          rlc_twoChannelEdgeConfigExtend gamma gamma' eta := by
      intro e
      by_cases hedge : e ∈
          (rlc_connectorTwoChannelGraph gamma gamma').edgeSet
      · let edge : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet :=
          ⟨e, hedge⟩
        cases hroute : route.1 edge with
        | false =>
            simp [rlc_twoChannelEdgeConfigExtend,
              rlc_twoChannelConfigSplitEquiv, hedge, edge, hroute]
        | true =>
            have he : edge ∈ rlc_twoChannelOpenEdgeSet route.1 := by
              simpa using hroute
            have heta := hopen edge he
            simp [rlc_twoChannelEdgeConfigExtend,
              rlc_twoChannelConfigSplitEquiv, hedge, edge, hroute, heta]
      · simp [rlc_twoChannelEdgeConfigExtend,
          rlc_twoChannelConfigSplitEquiv, hedge]
    exact rlc_finiteTwoChannelConnectorEvent_isIncreasing
      gamma gamma' hle route.2


end
end StatMech.Universality
