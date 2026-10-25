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
import Theorem.StatisticalMechanics.Code.Universality.RSWSequentialStoppedConditionalLaw.Part15
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

noncomputable def rlc_connectorExteriorFibreCondEventMass {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (H B : SimpleGraph (RlcConnectorVertex n))
    [DecidableRel H.Adj] [DecidableRel B.Adj]
    (psi : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (p q : Real) : Real :=
  ∑ eta,
    (rlc_connectorActiveEvent gamma gamma').indicator
        (fun _ => (1 : Real)) eta *
      FK.condBcProb H B p q
        (rlc_connectorFiniteGraph gamma gamma').edgeFinset psi
        (rlc_connectorExteriorFibreConfig gamma gamma' psi eta)


end
end StatMech.Universality
