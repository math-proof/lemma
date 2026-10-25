/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc21fiberconn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc20closure.Part2
import Theorem.StatisticalMechanics.Code.Walls.gc19switching.Part2
import Theorem.StatisticalMechanics.Code.Walls.gc18core.Part2
import Theorem.StatisticalMechanics.Code.Walls.gc16core.Part4
import Theorem.StatisticalMechanics.Code.Walls.gc7core
import Theorem.StatisticalMechanics.Code.Walls.gc6_munonneg
import Theorem.StatisticalMechanics.Code.Ising.TwoReplica.Part7
import Theorem.StatisticalMechanics.Code.Ising.TwoReplicaWeighted.Part2
import Theorem.StatisticalMechanics.Code.Ising.HdomNativeWeight.Part3
import Theorem.StatisticalMechanics.Code.Ising.AizenmanSignDominance.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.FluxEdgeCopyBridge.Part3
import Theorem.StatisticalMechanics.Code.Walls.gc21fiberconn.Part2
open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.unusedDecidableInType false
set_option maxHeartbeats 1600000


namespace StatMech.Walls

open StatMech StatMech.Ising StatMech.Sharpness

open StatMech.Sharpness.RandomCurrent StatMech.Sharpness.FluxEdgeCopy

open StatMech.Sharpness.FieldGhostDict


variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


def gc21_FibreOddArcBridge (m : ↥(withGhost G).edgeFinset → ℕ) : Prop :=
  ∀ (K₁ : {K : ↥(withGhost G).edgeFinset → ℕ // ∀ e, K e ≤ m e}) (u v : Option V),
    connP (posEdges (withGhost G).edgeFinset
        (ofEdgeFun (withGhost G) (fun e => m e - K₁.1 e))) u v →
    connP (oddEdges (withGhost G).edgeFinset
        (ofEdgeFun (withGhost G) (fun e => m e - K₁.1 e))) u v


end StatMech.Walls
