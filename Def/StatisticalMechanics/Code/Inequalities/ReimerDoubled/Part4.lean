/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerDoubled.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.ReimerStep.Part3
import Mathlib.Combinatorics.SetFamily.Compression.UV
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerDoubled.Part3
open Finset
open scoped FinsetFamily


namespace StatMech

variable {α : Type*} [DecidableEq α]


noncomputable def downLeft (i : α) (𝒜 : Finset (Finset (α ⊕ α))) : Finset (Finset (α ⊕ α)) :=
  Down.compression (Sum.inl i) 𝒜


noncomputable def upRight (i : α) (𝒜 : Finset (Finset (α ⊕ α))) : Finset (Finset (α ⊕ α)) :=
  upComp (Sum.inr i) 𝒜


end StatMech
