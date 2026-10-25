/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFibreCube.Part3
import Theorem.StatisticalMechanics.Code.Lattice.CollaredWalkCrossing
import Theorem.StatisticalMechanics.Code.TwoDim.ZhangFaithfulExclusive.Part2
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part4
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

def rlc_twoChannelPIMSVariableToFullPhysical {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (target : RlcTwoChannelPIMSVariableTargetEdge gamma gamma') :
    RlcTwoChannelFullPhysicalTargetEdge gamma gamma' :=
  ⟨target.1, ⟨⟨rlc_twoChannelPIMSSourceEdge target,
    rlc_twoChannelPIMSSourceEdge_map target⟩⟩⟩


def RlcTwoChannelFullPhysicalPermutationSuccess {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (_hfaith : RlcBookFaithfulTracePair gamma gamma') : Prop :=
  forall rho : RlcTwoChannelEdgeFailure gamma gamma',
    rlc_twoChannelEdgeConfigExtend gamma gamma'
        (rlc_twoChannelFullPhysicalPermConfig gamma gamma' rho.1) ∈
      rlc_finiteTwoChannelConnectorEvent gamma gamma'


def RlcTwoChannelFullVariableConnectorSuccess {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') : Prop :=
  ∃ x y : RlcConnectorVertex n,
    rlc_connectorOnRight gamma x ∧ rlc_connectorOnLeft gamma' y ∧
      (FK.openSub (rlc_twoChannelFullVariableGraph gamma gamma')
        (rlc_twoChannelFullDualConfig gamma gamma' omega)).Reachable x y


end
end StatMech.Universality
