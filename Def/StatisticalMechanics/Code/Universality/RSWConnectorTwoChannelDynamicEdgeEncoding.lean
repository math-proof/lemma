module
public import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelEdgeEncoding.Part2
public import Theorem.StatisticalMechanics.Code.FK.SelfDualPointMassScore
public import Theorem.StatisticalMechanics.Code.FK.BoundaryScoreLipschitz
public import Theorem.StatisticalMechanics.Code.FrontierD.FKBoundarySingleMerge
public import Structure.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelDynamicEdgeEncoding
open Finset SimpleGraph Set


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelDynamicEdgeEncoding.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

def RlcTwoChannelDynamicRoutePlan.codeSet {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (P : RlcTwoChannelDynamicRoutePlan gamma gamma')
    (route : P.Route) : Set (RlcTwoChannelEdgeConfig gamma gamma') :=
  {eta | (∀ e, e ∈ P.reservedEdges route → eta e = true) ∧
    ∀ e, e ∉ P.reservedEdges route → e ∉ P.payloadSlots route →
      eta e = P.tagState route e}

end
end StatMech.Universality
