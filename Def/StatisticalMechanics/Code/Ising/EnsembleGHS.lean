module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Sharpness.RandomCurrent.Part10
public import Theorem.StatisticalMechanics.Code.Ising.TwoReplica.Part7
public import Theorem.StatisticalMechanics.Code.Ising.TwoReplicaWeighted.Part2
public import Theorem.StatisticalMechanics.Code.Ising.AizenmanSignDominance.Part2
public import Theorem.StatisticalMechanics.Code.Ising.HdomNativeWeight.Part3
public import Theorem.StatisticalMechanics.Code.Ising.TwoCurrentProbBound
public import Theorem.StatisticalMechanics.Code.Ising.CrossClassHdom
public import Theorem.StatisticalMechanics.Code.Ising.AizenmanBarsky.Part5
open Finset Classical
open scoped symmDiff BigOperators
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/EnsembleGHS.lean -/
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


noncomputable def egh_ensembleUrsell (β : ℝ) (J : Sym2 V → ℝ) (M : Finset (Current V))
    (B : Finset V) (o x y : V) : ℝ :=
  ∑ m ∈ M.filter (fun m => hnw_allConn G m o x y), hnw_gap G β J m B o x y


end Ising
end StatMech
