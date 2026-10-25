/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/TwoCurrentProbBound.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Sharpness.RandomCurrent.Part10
import Theorem.StatisticalMechanics.Code.Ising.TwoReplica.Part7
import Theorem.StatisticalMechanics.Code.Ising.TwoReplicaWeighted.Part2
import Theorem.StatisticalMechanics.Code.Ising.AizenmanSignDominance.Part2
import Theorem.StatisticalMechanics.Code.Ising.HdomNativeWeight.Part3
open Finset Classical
open scoped symmDiff BigOperators

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000


namespace StatMech

namespace Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def tcp_partitionFunction (β : ℝ) (J : Sym2 V → ℝ) (M : Finset (Current V))
    (B : Finset V) : ℝ :=
  ∑ m ∈ M, hnw_mass G β J m B


noncomputable def tcp_allConnMass (β : ℝ) (J : Sym2 V → ℝ) (M : Finset (Current V))
    (B : Finset V) (o x y : V) : ℝ :=
  ∑ m ∈ M.filter (fun m => hnw_allConn G m o x y), hnw_mass G β J m B


noncomputable def tcp_allConnProb (β : ℝ) (J : Sym2 V → ℝ) (M : Finset (Current V))
    (B : Finset V) (o x y : V) : ℝ :=
  tcp_allConnMass G β J M B o x y / tcp_partitionFunction G β J M B


end Ising
end StatMech
