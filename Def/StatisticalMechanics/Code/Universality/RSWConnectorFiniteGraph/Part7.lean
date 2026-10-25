/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.RSWGapSymmetry.Part4
import Theorem.StatisticalMechanics.Code.Universality.RSWExtremalTraceContact
import Theorem.StatisticalMechanics.Code.Universality.RSWExtremalSelectionObstruction
import Theorem.StatisticalMechanics.Code.BeffaraDC.PlanarFKDuality.Part6
import Theorem.StatisticalMechanics.Code.FK.MonoBC.Part4
import Theorem.StatisticalMechanics.Code.FK.OffCentreDomination.Part13
import Theorem.StatisticalMechanics.Code.FK.WeightedParameterMonotoneClosed
import Theorem.StatisticalMechanics.Code.FrontierD.FKBoundarySingleMerge
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsHoleFreeBoundary.Part4
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorFiniteGraph.Part3
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

noncomputable def rlc_connectorTraceComponentEquiv {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (H : SimpleGraph (RlcConnectorVertex n)) :
    (H ⊔ rlc_connectorTraceWiring gamma gamma').ConnectedComponent ≃
      (H ⊔ rlc_connectorSeparateWiring gamma gamma').ConnectedComponent := by
  let A := H ⊔ rlc_connectorTraceWiring gamma gamma'
  let B := H ⊔ rlc_connectorSeparateWiring gamma gamma'
  apply Equiv.ofBijective (fun C : A.ConnectedComponent =>
    B.connectedComponentMk C.out)
  constructor
  · intro C D hCD
    have hB : B.Reachable C.out D.out := ConnectedComponent.eq.mp hCD
    have hA : A.Reachable C.out D.out :=
      (rlc_connectorTraceWiring_reachable_iff_separateWiring
        gamma gamma' H C.out D.out).mpr hB
    rw [← C.out_eq, ← D.out_eq]
    exact ConnectedComponent.sound hA
  · intro D
    let C := A.connectedComponentMk D.out
    refine ⟨C, ?_⟩
    rw [← D.out_eq]
    apply ConnectedComponent.sound
    have hA : A.Reachable C.out D.out :=
      ConnectedComponent.exact C.out_eq
    exact (rlc_connectorTraceWiring_reachable_iff_separateWiring
      gamma gamma' H C.out D.out).mp hA


end
end StatMech.Universality
