/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelDynamicEdgeEncoding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelEdgeEncoding.Part2
import Theorem.StatisticalMechanics.Code.FK.SelfDualPointMassScore
import Theorem.StatisticalMechanics.Code.FK.BoundaryScoreLipschitz
import Theorem.StatisticalMechanics.Code.FrontierD.FKBoundarySingleMerge
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelDynamicEdgeEncoding.Part2
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

def RlcTwoChannelDynamicRoutePlan.Compatible {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (P : RlcTwoChannelDynamicRoutePlan gamma gamma')
    (routeAvailable : RlcTwoChannelEdgeFailure gamma gamma' → P.Route → Prop)
    (rho : RlcTwoChannelEdgeFailure gamma gamma')
    (eta : RlcTwoChannelEdgeSuccess gamma gamma') : Prop :=
  ∃ route : P.Route, routeAvailable rho route ∧ eta.1 ∈ P.codeSet route

def RlcTwoChannelDynamicRoutePlan.HasCodeHall {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (P : RlcTwoChannelDynamicRoutePlan gamma gamma')
    (routeAvailable : RlcTwoChannelEdgeFailure gamma gamma' → P.Route → Prop) :
    Prop :=
  RlcTwoChannelEdgeCodeHall gamma gamma'
    (P.Compatible routeAvailable)


end
end StatMech.Universality
