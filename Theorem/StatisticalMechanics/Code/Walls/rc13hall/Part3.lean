/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc13hall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc12reimerinjection.Part5
import Theorem.StatisticalMechanics.Code.Walls.rc10core.Part4
import Def.StatisticalMechanics.Code.Walls.rc13hall.Part3
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

set_option maxRecDepth 100000

variable {α : Type*} [Fintype α] [DecidableEq α]


open Classical in

theorem rc13_admComp_eq (𝒜 ℬ : Finset (Finset α)) (S : Finset α) :
    rc13_admComp 𝒜 ℬ S = rc13_adm 𝒜 ℬ S := by
  ext R
  rw [rc13_admComp, rc13_adm]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨T, hT, hTS, hST, hTR, hdisj⟩; exact ⟨T, hTS, hT, hST, hTR, hdisj⟩
  · rintro ⟨T, hTS, hT, hST, hTR, hdisj⟩; exact ⟨T, hT, hTS, hST, hTR, hdisj⟩


end StatMech.Walls
