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
import Theorem.StatisticalMechanics.Code.Universality.RSWSequentialStoppedConditionalLaw.Part12
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

noncomputable def rlc_connectorExteriorFibreEquiv {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (psi : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    ConfigSpace (rlc_connectorFiniteGraph gamma gamma').edgeSet ≃
      {rho : ConfigSpace (Sym2 (RlcConnectorVertex n)) //
        rho ∈ FK.condFibre
          (rlc_connectorFiniteGraph gamma gamma').edgeFinset psi} where
  toFun eta := ⟨rlc_connectorExteriorFibreConfig gamma gamma' psi eta, by
    rw [FK.mem_condFibre]
    exact rlc_connectorExteriorFibreConfig_agreesOff
      gamma gamma' psi eta⟩
  invFun rho := FK.restrictActive (rlc_connectorFiniteGraph gamma gamma') rho.1
  left_inv eta :=
    rlc_connectorExteriorFibreConfig_restrictActive gamma gamma' psi eta
  right_inv rho := by
    apply Subtype.ext
    exact rlc_connectorExteriorFibreConfig_restrictActive_eq
      gamma gamma' psi rho.1 (FK.mem_condFibre.mp rho.2)


end
end StatMech.Universality
