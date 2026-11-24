module
public import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceFilledBoundary.Part46
public import Theorem.StatisticalMechanics.Code.Foundations.WeightedFiniteInjection
public import Def.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannel
open Finset SimpleGraph Set


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannel.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

noncomputable instance rlc_connectorTwoChannelGraphDecidableAdj
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n) :
    DecidableRel (rlc_connectorTwoChannelGraph gamma gamma').Adj :=
  Classical.decRel _


end
end StatMech.Universality
