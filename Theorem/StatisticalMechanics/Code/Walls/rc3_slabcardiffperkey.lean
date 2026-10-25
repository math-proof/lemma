/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc3_slabcardiffperkey.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc2_slabimgeqinter.Part3
import Theorem.StatisticalMechanics.Code.Walls.rc2_slabcardallisbridge
open Finset
open scoped FinsetFamily NNReal


namespace StatMech.Walls

open StatMech

variable {α : Type*} [Fintype α] [DecidableEq α]


open Classical in


theorem rc3_slabBox_eq_inter (A B : Set (ConfigSpace α)) (k : ConfigSpace α × ConfigSpace α) :
    poc_slabBox A B k =
      Finset.univ.filter
        (fun ω : ConfigSpace α => ω ∈ disjointOccurrence A B ∧ ω ∈ rc2_slab k) := by
  unfold poc_slabBox
  refine Finset.filter_congr (fun ω _ => ?_)
  simp only [rc2_mem_slab]


end StatMech.Walls
