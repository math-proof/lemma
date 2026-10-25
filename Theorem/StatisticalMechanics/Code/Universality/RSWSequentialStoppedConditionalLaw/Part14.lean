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
import Def.StatisticalMechanics.Code.Universality.RSWSequentialStoppedConditionalLaw.Part14
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_numClustersBC_exteriorFibre_eq_induced {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (H B : SimpleGraph (RlcConnectorVertex n))
    [DecidableRel H.Adj] [DecidableRel B.Adj]
    (hGH : rlc_connectorFiniteGraph gamma gamma' ≤ H)
    (psi : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (eta : ConfigSpace (rlc_connectorFiniteGraph gamma gamma').edgeSet) :
    FK.numClustersBC H B
        (rlc_connectorExteriorFibreConfig gamma gamma' psi eta) =
      FK.numClustersBC (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorExteriorInducedWiring gamma gamma' H B psi)
        (FK.extendActive (rlc_connectorFiniteGraph gamma gamma') eta) := by
  unfold FK.numClustersBC
  rw [rlc_openSub_exteriorFibre_sup_frozen gamma gamma' H B hGH psi eta]
  exact Nat.card_congr (rlc_connectorExteriorComponentEquiv
    gamma gamma' H B psi
      (FK.openSub (rlc_connectorFiniteGraph gamma gamma')
        (FK.extendActive (rlc_connectorFiniteGraph gamma gamma') eta)))


end
end StatMech.Universality
