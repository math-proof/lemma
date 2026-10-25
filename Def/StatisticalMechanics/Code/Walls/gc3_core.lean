/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc3_core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc_core.Part2
import Theorem.StatisticalMechanics.Code.Walls.gc3_signedperSuper
import Theorem.StatisticalMechanics.Code.Walls.gc3_backbonetrichotomy
import Theorem.StatisticalMechanics.Code.Walls.gc3_backbonenotsigndef
import Theorem.StatisticalMechanics.Code.Ising.AizenmanInclusionExclusion.Part3
import Theorem.StatisticalMechanics.Code.Walls.gc3_core
open Finset BigOperators SimpleGraph Set
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000


namespace StatMech.Walls

open StatMech.Sharpness StatMech.Sharpness.RandomCurrent

open StatMech.Ising

open StatMech.Walls.GhcEqGap


variable {ι V : Type*} [DecidableEq ι] [DecidableEq V] [Fintype V] [Fintype ι]


def GHS3SummedGapNonpos (ends : ι → Sym2 V) (M : Finset (Finset ι)) (A : Finset V)
    (Φ : Finset ι → Finset ι → ℝ) (o x y : V) : Prop :=
  ∑ m ∈ M, aie_gap ends m (Φ m) A o x y ≤ 0


end StatMech.Walls
