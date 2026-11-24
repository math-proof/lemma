module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Ising.GKS.Part5
public import Theorem.StatisticalMechanics.Code.Ising.GKS2.Part4
public import Theorem.StatisticalMechanics.Code.Ising.AizenmanBarsky.Part5
public import Theorem.StatisticalMechanics.Code.Walls.ghc_urselleqgap
public import Theorem.StatisticalMechanics.Code.Walls.gc31surgery.Part3
public import Theorem.StatisticalMechanics.Code.Ising.BackboneResummation.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.BoxSurfaceVolume.Part5
public import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneUniqueness.Part3
public import Theorem.StatisticalMechanics.Code.Percolation.RootedForestPeelClose.Part4
public import Theorem.StatisticalMechanics.Code.Walls.bc28forestroot.Part2
public import Theorem.StatisticalMechanics.Code.Inequalities.Reimer.Part3
public import Theorem.StatisticalMechanics.Code.Inequalities.ReimerCompression.Part5
public import Theorem.StatisticalMechanics.Code.Walls.rc18nonmono.Part2
public import Theorem.StatisticalMechanics.Code.Walls.rc19doublecover.Part4
public import Theorem.StatisticalMechanics.Code.Walls.FaithfulnessAudit
open scoped BigOperators
open Finset SimpleGraph
open StatMech StatMech.Ising StatMech.Walls.GhcEqGap
open StatMech.Lattice StatMech.Percolation


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/FaithfulnessAudit.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Walls

set_option linter.unusedSectionVars false

set_option maxHeartbeats 800000


variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


variable {d : ℕ}


def fa_reimer_parA : Set (ConfigSpace (Fin 4)) := {ω | ω 0 = ω 1}


def fa_reimer_parB : Set (ConfigSpace (Fin 4)) := {ω | ω 2 = ω 3}


end StatMech.Walls
