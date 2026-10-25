/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc3_slabimgeqinter.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.PerOrbitCardClose.Part8
import Theorem.StatisticalMechanics.Code.Walls.rmr_reflectinvolution.Part2
import Theorem.StatisticalMechanics.Code.Walls.rmr_topkey.Part2
import Theorem.StatisticalMechanics.Code.Walls.rc2_cardformiffinter
import Def.StatisticalMechanics.Code.Walls.rc3_slabimgeqinter
open Finset
open scoped FinsetFamily


namespace StatMech.Walls

open StatMech

variable {α : Type*} [Fintype α] [DecidableEq α]


omit [Fintype α] [DecidableEq α] in
@[simp] theorem rc3_mem_slab (k : ConfigSpace α × ConfigSpace α) (ω : ConfigSpace α) :
    ω ∈ rc3_slab k ↔ orbitKey (ω, poc_keyFlip k ω) = k := Iff.rfl


end StatMech.Walls
