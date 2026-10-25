/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerDoubled.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.ReimerStep.Part3
import Mathlib.Combinatorics.SetFamily.Compression.UV
import Def.StatisticalMechanics.Code.Inequalities.ReimerDoubled.Part3
open Finset
open scoped FinsetFamily


namespace StatMech

variable {α : Type*} [DecidableEq α]


@[simp] theorem upComp_card (a : α ⊕ α) (𝒜 : Finset (Finset (α ⊕ α))) :
    (upComp a 𝒜).card = 𝒜.card := by
  unfold upComp; exact UV.card_compression _ _ _


@[simp] theorem upComp_idem (a : α ⊕ α) (𝒜 : Finset (Finset (α ⊕ α))) :
    upComp a (upComp a 𝒜) = upComp a 𝒜 := by
  unfold upComp; exact UV.compression_idem _ _ _


end StatMech
