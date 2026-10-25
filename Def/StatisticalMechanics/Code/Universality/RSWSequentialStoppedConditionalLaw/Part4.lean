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
import Theorem.StatisticalMechanics.Code.Universality.RSWSequentialStoppedConditionalLaw.Part3
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

noncomputable def rlc_connectorTraceFibreEquiv {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    ConfigSpace (rlc_connectorFiniteGraph gamma gamma').edgeSet ≃
      {rho : ConfigSpace (Sym2 (RlcConnectorVertex n)) //
        rho ∈ FK.condFibre (rlc_connectorTraceFibreInside gamma gamma')
          (rlc_connectorTraceFibreReference gamma gamma')} where
  toFun eta := ⟨rlc_connectorTraceFibreConfig gamma gamma' eta, by
    rw [FK.mem_condFibre]
    exact rlc_connectorTraceFibreConfig_agreesOff gamma gamma' eta⟩
  invFun rho := FK.restrictActive (rlc_connectorFiniteGraph gamma gamma') rho.1
  left_inv eta := rlc_connectorTraceFibreConfig_restrictActive gamma gamma' eta
  right_inv rho := by
    apply Subtype.ext
    exact rlc_connectorTraceFibreConfig_restrictActive_eq gamma gamma'
      (FK.mem_condFibre.mp rho.2)


end
end StatMech.Universality
