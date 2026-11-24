module
public import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelDynamicEdgeEncoding.Part3
public import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelCanonicalRoute.Part8
open Finset SimpleGraph Set


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelCanonicalRoute.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

noncomputable instance rlc_twoChannelEdgeSuccessLinearOrder {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    LinearOrder (RlcTwoChannelEdgeSuccess gamma gamma') :=
  LinearOrder.lift'
    (Fintype.equivFin (RlcTwoChannelEdgeSuccess gamma gamma'))
    (Fintype.equivFin _).injective


end
end StatMech.Universality
