/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc37doubledhall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc36hallmarriage.Part2
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerDoubled.Part6
import Theorem.StatisticalMechanics.Code.Walls.rc37doubledhall
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


noncomputable def rc37_complBoxDoubled (𝒜 ℬ : Finset (Finset α)) : Finset (Finset (α ⊕ α)) :=
  (rc10_reflInter 𝒜 ℬ).image (fun R => dbl R Rᶜ)


end StatMech.Walls
