/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerDoubled.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.ReimerStep.Part3
import Mathlib.Combinatorics.SetFamily.Compression.UV
import Def.StatisticalMechanics.Code.Inequalities.ReimerDoubled.Part5
open Finset
open scoped FinsetFamily


namespace StatMech

variable {α : Type*} [DecidableEq α]


@[simp] theorem doubleCompress_card (i : α) (𝒜 : Finset (Finset (α ⊕ α))) :
    (doubleCompress i 𝒜).card = 𝒜.card := by
  unfold doubleCompress
  rw [upRight_card, downLeft_card]


end StatMech
