module
public import Theorem.StatisticalMechanics.Code.Universality.RSWSequentialStoppedExplorationBridge
public import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorSeededMassCapstone.Part2
public import Theorem.StatisticalMechanics.Code.FK.ActiveBoundaryEquiv.Part2
public import Theorem.StatisticalMechanics.Code.FK.BoundaryEdgeAbsorption.Part3
public import Theorem.StatisticalMechanics.Code.FK.FKDisjointBoxDomainMarkov.Part3
public import Instance.StatisticalMechanics.Code.Universality.RSWSequentialStoppedConditionalLaw.Part2
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

noncomputable def rlc_connectorExtendConfig {n : Int}
    (psi : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    ConfigSpace (Sym2 (Site 2)) :=
  Function.extend
    (Sym2.map (Subtype.val : RlcConnectorVertex n → Site 2)) psi
    (fun _ => false)

end
end StatMech.Universality
