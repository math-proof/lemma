/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc58bipartiteflow.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc57witnessed.Part4
import Theorem.StatisticalMechanics.Code.Walls.rc22doublecover.Part6
import Mathlib.Combinatorics.Hall.Basic
import Def.StatisticalMechanics.Code.Walls.rc58bipartiteflow
set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


set_option maxRecDepth 4000 in

theorem rc58_box_mono_card :
    (rc20_famCylBoxComp 2 rc58_Amono rc58_Bmono).card = 2 := by
  rw [rc58_Amono, rc58_Bmono]; decide

set_option maxRecDepth 4000 in


theorem rc58_box_mono_compressed_card :
    (rc20_famCylBoxComp 2 (Down.compression 0 rc58_Amono) (Down.compression 0 rc58_Bmono)).card = 1 := by
  rw [rc58_Amono, rc58_Bmono]; decide

set_option maxRecDepth 4000 in


theorem rc58_box_strict_shrink :
    (rc20_famCylBoxComp 2 (Down.compression 0 rc58_Amono) (Down.compression 0 rc58_Bmono)).card
      < (rc20_famCylBoxComp 2 rc58_Amono rc58_Bmono).card := by
  rw [rc58_box_mono_compressed_card, rc58_box_mono_card]; norm_num

open Classical in


theorem rc58_boxCompressionMono_false : ¬ rc22_BoxCompressionMono := by
  intro h
  have hle := h 2 rc58_Amono rc58_Bmono 0
  have hstrict := rc58_box_strict_shrink
  rw [rc20_famCylBoxComp_eq, rc20_famCylBoxComp_eq] at hstrict
  exact absurd hle (not_le.mpr hstrict)

set_option maxRecDepth 4000 in


theorem rc58_wall_holds_on_monoCE :
    (rc20_famCylBoxComp 2 rc58_Amono rc58_Bmono).card
      ≤ (rc20_reflInterComp 2 rc58_Amono rc58_Bmono).card := by
  rw [rc58_Amono, rc58_Bmono]; decide


open Classical in


theorem rc58_matching_iff_wall (𝒜 ℬ : Finset (Finset α)) :
    #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) ↔
      Nonempty ((rc20_famCylBox 𝒜 ℬ : Finset (Finset α)) ↪ (rc10_reflInter 𝒜 ℬ : Finset (Finset α))) := by
  rw [Function.Embedding.nonempty_iff_card_le, Fintype.card_coe, Fintype.card_coe]


end StatMech.Walls
