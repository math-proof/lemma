module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Ising.TwoReplica.Part7
public import Theorem.StatisticalMechanics.Code.Ising.TwoReplicaWeighted.Part2
public import Theorem.StatisticalMechanics.Code.Ising.BackboneExists
public import Theorem.StatisticalMechanics.Code.Ising.HdomNativeWeight.Part3
public import Theorem.StatisticalMechanics.Code.Sharpness.RandomCurrent.Part10
public import Theorem.StatisticalMechanics.Code.Sharpness.TwoReplica.Part3
public import Theorem.StatisticalMechanics.Code.Ising.AizenmanSignDominance.Part2
open Finset Classical
open scoped symmDiff BigOperators
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/HdomMultiplicity.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


def hmu_addBackbone (P : Finset (Sym2 V)) (m : Current V) : Current V :=
  fun e => m e + (if e ∈ P then 1 else 0)

end Ising
end StatMech
