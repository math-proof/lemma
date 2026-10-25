/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc68countmarriage.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc67marriagesplit.Part3
import Theorem.StatisticalMechanics.Code.Walls.rc68countmarriage
set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {n : ℕ}


open Classical in


def rc68_CountForm (𝒜 ℬ : Finset (Finset (Fin n))) (T : Finset (Finset (Fin n))) : Prop :=
  (rc67_Toff 𝒜 ℬ T).card ≤ ((T.biUnion (rc59_nbhd 𝒜 ℬ)) \ rc67_Tin 𝒜 ℬ T).card

end StatMech.Walls
