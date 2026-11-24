module
public import Theorem.StatisticalMechanics.Code.Universality.RSWSequentialStoppedExplorationBridge
public import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorSeededMassCapstone.Part2
public import Theorem.StatisticalMechanics.Code.FK.ActiveBoundaryEquiv.Part2
public import Theorem.StatisticalMechanics.Code.FK.BoundaryEdgeAbsorption.Part3
public import Theorem.StatisticalMechanics.Code.FK.FKDisjointBoxDomainMarkov.Part3
public import Theorem.StatisticalMechanics.Code.Universality.RSWSequentialStoppedConditionalLaw.Part11
open Finset SimpleGraph Set


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSequentialStoppedConditionalLaw.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

noncomputable def rlc_connectorExteriorFibreConfig {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (psi : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (eta : ConfigSpace (rlc_connectorFiniteGraph gamma gamma').edgeSet) :
    ConfigSpace (Sym2 (RlcConnectorVertex n)) := fun e =>
  if h : e ∈ (rlc_connectorFiniteGraph gamma gamma').edgeSet
    then eta ⟨e, h⟩ else psi e

end
end StatMech.Universality
