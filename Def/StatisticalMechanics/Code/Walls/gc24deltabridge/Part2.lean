/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc24deltabridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc23allconn.Part2
import Theorem.StatisticalMechanics.Code.Walls.gc22edgecopy.Part2
import Theorem.StatisticalMechanics.Code.Walls.gc15core.Part5
import Theorem.StatisticalMechanics.Code.Walls.gc10deltasupport
import Theorem.StatisticalMechanics.Code.Walls.gc10ensembleprob
import Theorem.StatisticalMechanics.Code.Sharpness.DeltaRewriteDichotomy.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.GhostCurrentRep
import Theorem.StatisticalMechanics.Code.Sharpness.FluxEdgeCopyBridge.Part3
import Theorem.StatisticalMechanics.Code.Ising.CurrentWeight.Part2
import Theorem.StatisticalMechanics.Code.Ising.AizenmanSignDominance.Part2
import Theorem.StatisticalMechanics.Code.Walls.gc24deltabridge
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

open StatMech.Walls.Gc5EqGap StatMech.Walls.GhcEqGap

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


def gc24_ThreeReplicaResummation (β h : ℝ) (o x y : V) : Prop :=
  ∃ (ι : Type) (_ : DecidableEq ι) (_ : Fintype ι) (ends : ι → Sym2 (Option V))
    (F : Finset ι → ℝ),
      (∀ m, 0 ≤ F m)
      ∧ (∀ i, ¬ (ends i).IsDiag)
      ∧ (∀ m : Finset ι, (¬ connK ends m (some o) none) →
            RandomCurrent.sources ends m = {some o, some x, some y, none})
      ∧ (∑' m, gc15_threeGap G β h o x y m)
          = -2 * gc10_allConnMass ends (some o) (some x) (some y) none F


end StatMech.Walls
