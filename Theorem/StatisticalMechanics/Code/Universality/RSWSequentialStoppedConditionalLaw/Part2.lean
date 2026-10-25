/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSequentialStoppedConditionalLaw.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWSequentialStoppedExplorationBridge
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorSeededMassCapstone.Part2
import Theorem.StatisticalMechanics.Code.FK.ActiveBoundaryEquiv.Part2
import Theorem.StatisticalMechanics.Code.FK.BoundaryEdgeAbsorption.Part3
import Theorem.StatisticalMechanics.Code.FK.FKDisjointBoxDomainMarkov.Part3
import Def.StatisticalMechanics.Code.Universality.RSWSequentialStoppedConditionalLaw.Part2
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_connectorForcedTraceActiveEventMass_eq_activeSeparate
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {p q : Real} (hp : 0 < p) :
    rlc_connectorForcedTraceActiveEventMass gamma gamma' p q =
      FK.activeBCProbOf (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma') (fun _ => p) q
        (rlc_connectorActiveEvent gamma gamma') := by
  unfold rlc_connectorForcedTraceActiveEventMass FK.activeBCProbOf
    FK.activeBCMean
  apply Finset.sum_congr rfl
  intro eta _
  rw [rlc_connectorForcedTraceActiveProb_eq_separate gamma gamma' hp eta]


theorem rlc_connectorActiveEvent_preimage {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    FK.restrictActive (rlc_connectorFiniteGraph gamma gamma') ⁻¹'
        rlc_connectorActiveEvent gamma gamma' =
      rlc_finiteConnectorEvent gamma gamma' := by
  ext tau
  simp only [Set.mem_preimage, rlc_connectorActiveEvent]
  unfold rlc_finiteConnectorEvent
  rw [Set.mem_setOf_eq, Set.mem_setOf_eq]
  rw [FK.openSub_extendActive_restrictActive_eq]


theorem rlc_connectorForcedTraceActiveEventMass_eq_separate {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    rlc_connectorForcedTraceActiveEventMass gamma gamma' p q =
      FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma') p q
        (rlc_finiteConnectorEvent gamma gamma') := by
  rw [rlc_connectorForcedTraceActiveEventMass_eq_activeSeparate
      gamma gamma' hp,
    FK.activeBCProbOf_eq_bcProb_preimage
      (rlc_connectorFiniteGraph gamma gamma')
      (rlc_connectorSeparateWiring gamma gamma') hp hp1 hq,
    rlc_connectorActiveEvent_preimage]
  rfl


end
end StatMech.Universality
