/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc2_slabimgeqinter.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.PerOrbitCardClose.Part8
import Theorem.StatisticalMechanics.Code.Walls.rmr_reflectinvolution.Part2
import Theorem.StatisticalMechanics.Code.Walls.rmr_topkey.Part2
open Finset
open scoped FinsetFamily


namespace StatMech.Walls

open StatMech

variable {α : Type*} [Fintype α] [DecidableEq α]


open Classical in


theorem rc2_slabImg_top_eq_inter (A B : Set (ConfigSpace α)) :
    poc_slabImg A B poc_topKey =
      Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ A ∩ rmr_reflect B) := by
  rw [poc_slabImg_top]
  refine Finset.filter_congr (fun ω _ => ?_)
  simp only [Set.mem_inter_iff, rmr_mem_reflect]
  rfl


end StatMech.Walls
