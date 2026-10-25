/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc12reimerinjection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc11core.Part3
import Def.StatisticalMechanics.Code.Walls.rc12reimerinjection.Part4
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

set_option maxRecDepth 100000

variable {α : Type*} [Fintype α] [DecidableEq α]


instance (n : ℕ) (𝒜 : Finset (Finset (Fin n))) : Decidable (rc12_isUpperFin n 𝒜) := by
  unfold rc12_isUpperFin; infer_instance

end StatMech.Walls
