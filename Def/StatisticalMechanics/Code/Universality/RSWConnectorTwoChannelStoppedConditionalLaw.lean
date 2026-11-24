module
public import Theorem.StatisticalMechanics.Code.FK.EdgeSubsetDomainMarkov.Part5
public import Theorem.StatisticalMechanics.Code.FK.BoundaryEdgeAbsorption.Part3
public import Theorem.StatisticalMechanics.Code.FK.ConditionalFibreMass
public import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelStaticCutEndpoint
public import Theorem.StatisticalMechanics.Code.Universality.RSWSequentialStoppedConditionalLaw.Part16
open Finset SimpleGraph Set


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelStoppedConditionalLaw.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

def rlc_twoChannelActiveEvent {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    Set (ConfigSpace (rlc_connectorTwoChannelGraph gamma gamma').edgeSet) :=
  FK.extendActive (rlc_connectorTwoChannelGraph gamma gamma') ⁻¹'
    rlc_finiteTwoChannelConnectorEvent gamma gamma'


end
end StatMech.Universality
