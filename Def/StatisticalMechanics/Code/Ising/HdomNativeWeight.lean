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
open Finset Classical
open scoped symmDiff BigOperators

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000


namespace StatMech

namespace Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def hnw_mass (β : ℝ) (J : Sym2 V → ℝ) (m : Current V) (S : Finset V) : ℝ :=
  splitWeightedSum G β J m 1 S


noncomputable def hnw_gap (β : ℝ) (J : Sym2 V → ℝ) (m : Current V) (A : Finset V)
    (o x y : V) : ℝ :=
  hnw_mass G β J m A - hnw_mass G β J m (A ∆ {x, y})
    - hnw_mass G β J m (A ∆ {o, y}) - hnw_mass G β J m (A ∆ {o, x})


end Ising
end StatMech
