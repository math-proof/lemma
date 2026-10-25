/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerDoubled.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.ReimerStep.Part3
import Mathlib.Combinatorics.SetFamily.Compression.UV
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerDoubled.Part5
open Finset
open scoped FinsetFamily


namespace StatMech

variable {α : Type*} [DecidableEq α]


def IsDownAtLeft (i : α) (𝒜 : Finset (Finset (α ⊕ α))) : Prop :=
  ∀ s ∈ 𝒜, s.erase (Sum.inl i) ∈ 𝒜


def IsUpAtRight (i : α) (𝒜 : Finset (Finset (α ⊕ α))) : Prop :=
  ∀ s ∈ 𝒜, insert (Sum.inr i) s ∈ 𝒜


end StatMech
