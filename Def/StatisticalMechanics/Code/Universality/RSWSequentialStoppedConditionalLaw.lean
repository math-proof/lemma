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
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

noncomputable def rlc_connectorForcedTraceActiveWeight {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (p q : Real)
    (eta : ConfigSpace (rlc_connectorFiniteGraph gamma gamma').edgeSet) : Real :=
  FK.fkWeight (rlc_connectorAugmentedPlanarDomain gamma gamma').G p q
    (rlc_connectorForceTraceConfig gamma gamma'
      (FK.extendActive (rlc_connectorFiniteGraph gamma gamma') eta))


noncomputable def rlc_connectorForcedTraceActiveZ {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (p q : Real) : Real :=
  ∑ eta, rlc_connectorForcedTraceActiveWeight gamma gamma' p q eta


noncomputable def rlc_connectorForcedTraceActiveProb {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (p q : Real)
    (eta : ConfigSpace (rlc_connectorFiniteGraph gamma gamma').edgeSet) : Real :=
  rlc_connectorForcedTraceActiveWeight gamma gamma' p q eta /
    rlc_connectorForcedTraceActiveZ gamma gamma' p q


end
end StatMech.Universality
