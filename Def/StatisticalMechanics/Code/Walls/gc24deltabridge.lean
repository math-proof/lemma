module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Walls.gc23allconn.Part2
public import Theorem.StatisticalMechanics.Code.Walls.gc22edgecopy.Part2
public import Theorem.StatisticalMechanics.Code.Walls.gc15core.Part5
public import Theorem.StatisticalMechanics.Code.Walls.gc10deltasupport
public import Theorem.StatisticalMechanics.Code.Walls.gc10ensembleprob
public import Theorem.StatisticalMechanics.Code.Sharpness.DeltaRewriteDichotomy.Part2
public import Theorem.StatisticalMechanics.Code.Sharpness.GhostCurrentRep
public import Theorem.StatisticalMechanics.Code.Sharpness.FluxEdgeCopyBridge.Part3
public import Theorem.StatisticalMechanics.Code.Ising.CurrentWeight.Part2
public import Theorem.StatisticalMechanics.Code.Ising.AizenmanSignDominance.Part2
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


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc24deltabridge.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Walls

open StatMech StatMech.Ising StatMech.Sharpness

open StatMech.Sharpness.RandomCurrent StatMech.Sharpness.FluxEdgeCopy

open StatMech.Sharpness.FieldGhostDict

open StatMech.Walls.Gc5EqGap StatMech.Walls.GhcEqGap

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def gc24_fibreCount (p : ↥G.edgeFinset → ℕ) (A : Finset V) : ℕ :=
  #((univ : Finset (Finset (Copy G p))).filter
      (fun S => RandomCurrent.sources (endsM G p) S = A))


end StatMech.Walls
