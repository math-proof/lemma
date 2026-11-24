module
public import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelEdgeEncoding.Part2
public import Theorem.StatisticalMechanics.Code.FK.SelfDualPointMassScore
public import Theorem.StatisticalMechanics.Code.FK.BoundaryScoreLipschitz
public import Theorem.StatisticalMechanics.Code.FrontierD.FKBoundarySingleMerge
public import Def.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelDynamicEdgeEncoding.Part2
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

theorem RlcTwoChannelDynamicRoutePlan.code_card {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (P : RlcTwoChannelDynamicRoutePlan gamma gamma')
    (route : P.Route) :
    Fintype.card (P.Code route) = 2 ^ (P.payloadSlots route).card := by
  rw [Fintype.card_congr (P.codeEquivPayload route), Fintype.card_fun,
    Fintype.card_bool, Fintype.card_coe]


end
end StatMech.Universality
