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
import Def.StatisticalMechanics.Code.Universality.RSWSequentialStoppedConditionalLaw.Part12
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_connectorExteriorFibreConfig_agreesOff {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (psi : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (eta : ConfigSpace (rlc_connectorFiniteGraph gamma gamma').edgeSet) :
    FK.AgreesOff (rlc_connectorFiniteGraph gamma gamma').edgeFinset psi
      (rlc_connectorExteriorFibreConfig gamma gamma' psi eta) := by
  intro e he
  have hnot : e ∉ (rlc_connectorFiniteGraph gamma gamma').edgeSet := by
    intro hmem
    exact he (SimpleGraph.mem_edgeFinset.mpr hmem)
  simp [rlc_connectorExteriorFibreConfig, hnot]

@[simp] theorem rlc_connectorExteriorFibreConfig_restrictActive {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (psi : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (eta : ConfigSpace (rlc_connectorFiniteGraph gamma gamma').edgeSet) :
    FK.restrictActive (rlc_connectorFiniteGraph gamma gamma')
      (rlc_connectorExteriorFibreConfig gamma gamma' psi eta) = eta := by
  funext e
  simp [FK.restrictActive, rlc_connectorExteriorFibreConfig, e.2]

theorem rlc_connectorExteriorFibreConfig_restrictActive_eq {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (psi rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hrho : FK.AgreesOff
      (rlc_connectorFiniteGraph gamma gamma').edgeFinset psi rho) :
    rlc_connectorExteriorFibreConfig gamma gamma' psi
        (FK.restrictActive (rlc_connectorFiniteGraph gamma gamma') rho) =
      rho := by
  funext e
  by_cases he : e ∈ (rlc_connectorFiniteGraph gamma gamma').edgeSet
  · simp [rlc_connectorExteriorFibreConfig, FK.restrictActive, he]
  · rw [rlc_connectorExteriorFibreConfig, dif_neg he]
    exact (hrho e (by
      simpa [SimpleGraph.mem_edgeFinset] using he)).symm


end
end StatMech.Universality
