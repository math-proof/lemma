/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc65marriagetwo.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc64consolidation.Part3
import Theorem.StatisticalMechanics.Code.Walls.rc41hall.Part3
import Theorem.StatisticalMechanics.Code.Walls.rc40sdr.Part3
import Theorem.StatisticalMechanics.Code.Walls.rc65marriagetwo
set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {n : ℕ}


def rc65_MarriageTwoPair (𝒜 ℬ : Finset (Finset (Fin n))) (S₁ S₂ : Finset (Fin n)) : Prop :=
  2 ≤ (rc59_nbhd 𝒜 ℬ S₁ ∪ rc59_nbhd 𝒜 ℬ S₂).card


end StatMech.Walls
