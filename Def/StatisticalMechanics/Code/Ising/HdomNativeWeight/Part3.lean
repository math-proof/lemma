/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/HdomNativeWeight.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.TwoReplica.Part7
import Theorem.StatisticalMechanics.Code.Ising.TwoReplicaWeighted.Part2
import Theorem.StatisticalMechanics.Code.Ising.BackboneExists
import Theorem.StatisticalMechanics.Code.Sharpness.RandomCurrent.Part10
import Theorem.StatisticalMechanics.Code.Sharpness.TwoReplica.Part3
import Theorem.StatisticalMechanics.Code.Ising.AizenmanSignDominance.Part2
import Theorem.StatisticalMechanics.Code.Ising.HdomNativeWeight.Part2
open Finset Classical
open scoped symmDiff BigOperators

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000


namespace StatMech

namespace Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


def hnw_coherent (m : Current V) (o x y : V) : Prop :=
  (connP (oddEdges G.edgeFinset m) x y ↔ connP (posEdges G.edgeFinset m) x y)
  ∧ (connP (oddEdges G.edgeFinset m) o y ↔ connP (posEdges G.edgeFinset m) o y)
  ∧ (connP (oddEdges G.edgeFinset m) o x ↔ connP (posEdges G.edgeFinset m) o x)


end Ising
end StatMech
