module
public import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFibreCube.Part3
public import Theorem.StatisticalMechanics.Code.Lattice.CollaredWalkCrossing
public import Theorem.StatisticalMechanics.Code.TwoDim.ZhangFaithfulExclusive.Part2
public import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part71
open Finset SimpleGraph Set


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

def RlcFiniteBidirectionalStrictRankTransition
    {R : Type*} [DecidableEq R] (states : Finset R)
    (rank : R → Nat) (next : R → R) : Prop :=
  ∀ z ∈ states, next z ∈ states ∧
    (rank (next z) < rank z ∨ rank z < rank (next z))


end
end StatMech.Universality
