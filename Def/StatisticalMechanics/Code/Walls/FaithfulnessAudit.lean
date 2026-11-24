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


noncomputable def fa_flipAll {V : Type*} (s : ConfigSpace V) : ConfigSpace V := fun i => !(s i)


end StatMech.Walls
