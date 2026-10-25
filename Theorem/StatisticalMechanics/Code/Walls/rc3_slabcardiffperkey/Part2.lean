/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc3_slabcardiffperkey.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc2_slabimgeqinter.Part3
import Theorem.StatisticalMechanics.Code.Walls.rc2_slabcardallisbridge
import Def.StatisticalMechanics.Code.Walls.rc3_slabcardiffperkey
open Finset
open scoped FinsetFamily NNReal


namespace StatMech.Walls

open StatMech

variable {α : Type*} [Fintype α] [DecidableEq α]


open Classical in


theorem rc3_slabCardKey_iff_perKey (A B : Set (ConfigSpace α))
    (k : ConfigSpace α × ConfigSpace α) :
    (#(poc_slabBox A B k) ≤ #(poc_slabImg A B k)) ↔ rc3_PerKey A B k := by
  rw [rc3_slabBox_eq_inter, rc2_slabImg_eq_inter]; rfl

open Classical in


theorem rc3_slabCard_iff_perKey (A B : Set (ConfigSpace α)) :
    poc_SlabCard A B ↔ ∀ k : ConfigSpace α × ConfigSpace α, rc3_PerKey A B k := by
  unfold poc_SlabCard
  exact forall_congr' (fun k => rc3_slabCardKey_iff_perKey A B k)


open Classical in


theorem rc3_perKey_top (A B : Set (ConfigSpace α)) :
    rc3_PerKey A B poc_topKey ↔
      #(Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ disjointOccurrence A B)) ≤
        #(Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ A ∩ rmr_reflect B)) := by
  rw [← rc3_slabCardKey_iff_perKey, rc2_slabCard_top_iff_inter]


end StatMech.Walls
