module
public import Theorem.StatisticalMechanics.Code.Universality.RSWSequentialStoppedExplorationBridge
public import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorSeededMassCapstone.Part2
public import Theorem.StatisticalMechanics.Code.FK.ActiveBoundaryEquiv.Part2
public import Theorem.StatisticalMechanics.Code.FK.BoundaryEdgeAbsorption.Part3
public import Theorem.StatisticalMechanics.Code.FK.FKDisjointBoxDomainMarkov.Part3
public import Theorem.StatisticalMechanics.Code.Universality.RSWSequentialStoppedConditionalLaw.Part2
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

noncomputable def rlc_connectorTraceFibreInside {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    Finset (Sym2 (RlcConnectorVertex n)) :=
  (rlc_connectorFiniteGraph gamma gamma').edgeFinset


noncomputable def rlc_connectorTraceFibreConfig {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (eta : ConfigSpace (rlc_connectorFiniteGraph gamma gamma').edgeSet) :
    ConfigSpace (Sym2 (RlcConnectorVertex n)) :=
  rlc_connectorForceTraceConfig gamma gamma'
    (FK.extendActive (rlc_connectorFiniteGraph gamma gamma') eta)


noncomputable def rlc_connectorTraceFibreReference {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    ConfigSpace (Sym2 (RlcConnectorVertex n)) :=
  rlc_connectorTraceFibreConfig gamma gamma' (fun _ => false)


end
end StatMech.Universality
