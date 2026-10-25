/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc2_core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Sharpness.Switching.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.FluxEdgeCopyBridge.Part3
import Theorem.StatisticalMechanics.Code.Walls.gc2_pairsubconfig
import Theorem.StatisticalMechanics.Code.Walls.gc2_shiftbij
import Theorem.StatisticalMechanics.Code.Walls.gc_subgraphcount
open Finset BigOperators
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000


namespace StatMech.Walls

open StatMech.Sharpness StatMech.Sharpness.RandomCurrent

variable {ι V : Type*} [DecidableEq ι] [DecidableEq V] [Fintype V] [Fintype ι]


def gc2_FB (ends : ι → Sym2 V) (M : Finset ι) (B : Finset V) : Prop :=
  ∀ u : V, Even (#((compOf ends M u).filter (fun x => x ∈ B)))


end StatMech.Walls
