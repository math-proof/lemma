module
public import Theorem.StatisticalMechanics.Code.Inequalities.ReimerStep.Part3
public import Mathlib.Combinatorics.SetFamily.Compression.UV
public import Def.StatisticalMechanics.Code.Inequalities.ReimerDoubled.Part4
open Finset
open scoped FinsetFamily


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerDoubled.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

variable {α : Type*} [DecidableEq α]


@[simp] theorem downLeft_card (i : α) (𝒜 : Finset (Finset (α ⊕ α))) :
    (downLeft i 𝒜).card = 𝒜.card := by
  unfold downLeft; exact Down.card_compression _ _


@[simp] theorem upRight_card (i : α) (𝒜 : Finset (Finset (α ⊕ α))) :
    (upRight i 𝒜).card = 𝒜.card := by
  unfold upRight; exact upComp_card _ _


end StatMech
