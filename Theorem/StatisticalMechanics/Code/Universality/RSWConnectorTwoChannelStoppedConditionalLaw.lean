module
public import Theorem.StatisticalMechanics.Code.FK.EdgeSubsetDomainMarkov.Part5
public import Theorem.StatisticalMechanics.Code.FK.BoundaryEdgeAbsorption.Part3
public import Theorem.StatisticalMechanics.Code.FK.ConditionalFibreMass
public import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelStaticCutEndpoint
public import Theorem.StatisticalMechanics.Code.Universality.RSWSequentialStoppedConditionalLaw.Part16
public import Def.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelStoppedConditionalLaw
open Finset SimpleGraph Set


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelStoppedConditionalLaw.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_twoChannelActiveEvent_preimage {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    FK.restrictActive (rlc_connectorTwoChannelGraph gamma gamma') ⁻¹'
        rlc_twoChannelActiveEvent gamma gamma' =
      rlc_finiteTwoChannelConnectorEvent gamma gamma' := by
  ext rho
  change
    (∃ x y : RlcConnectorVertex n,
      rlc_connectorOnRight gamma x ∧ rlc_connectorOnLeft gamma' y ∧
        (FK.openSub (rlc_connectorTwoChannelGraph gamma gamma')
          (FK.extendActive (rlc_connectorTwoChannelGraph gamma gamma')
            (FK.restrictActive
              (rlc_connectorTwoChannelGraph gamma gamma') rho))).Reachable x y) ↔
    ∃ x y : RlcConnectorVertex n,
      rlc_connectorOnRight gamma x ∧ rlc_connectorOnLeft gamma' y ∧
        (FK.openSub (rlc_connectorTwoChannelGraph gamma gamma') rho).Reachable x y
  rw [FK.openSub_extendActive_restrictActive_eq]


end
end StatMech.Universality
