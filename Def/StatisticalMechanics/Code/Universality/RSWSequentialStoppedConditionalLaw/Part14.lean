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
import Theorem.StatisticalMechanics.Code.Universality.RSWSequentialStoppedConditionalLaw.Part13
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

noncomputable def rlc_connectorExteriorComponentEquiv {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (H B : SimpleGraph (RlcConnectorVertex n))
    (psi : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (A : SimpleGraph (RlcConnectorVertex n)) :
    (A ⊔ rlc_connectorFrozenExteriorGraph gamma gamma' H B psi).ConnectedComponent ≃
      (A ⊔ rlc_connectorExteriorInducedWiring gamma gamma' H B psi).ConnectedComponent := by
  let K := A ⊔ rlc_connectorFrozenExteriorGraph gamma gamma' H B psi
  let L := A ⊔ rlc_connectorExteriorInducedWiring gamma gamma' H B psi
  apply Equiv.ofBijective (fun C : K.ConnectedComponent =>
    L.connectedComponentMk C.out)
  constructor
  · intro C D hCD
    have hL : L.Reachable C.out D.out := ConnectedComponent.eq.mp hCD
    have hK : K.Reachable C.out D.out :=
      (rlc_sup_frozen_reachable_iff_induced
        gamma gamma' H B psi A C.out D.out).mpr hL
    rw [← C.out_eq, ← D.out_eq]
    exact ConnectedComponent.sound hK
  · intro D
    let C := K.connectedComponentMk D.out
    refine ⟨C, ?_⟩
    rw [← D.out_eq]
    apply ConnectedComponent.sound
    have hK : K.Reachable C.out D.out := ConnectedComponent.exact C.out_eq
    exact (rlc_sup_frozen_reachable_iff_induced
      gamma gamma' H B psi A C.out D.out).mp hK


end
end StatMech.Universality
