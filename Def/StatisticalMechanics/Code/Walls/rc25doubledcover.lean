/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc25doubledcover.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc24countbridge.Part3
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerButterflyStep
import Theorem.StatisticalMechanics.Code.Walls.rc25doubledcover
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


open Classical in


noncomputable def rc25_witness (𝒜 ℬ : Finset (Finset α)) (S : Finset α) : Finset α :=
  if h : S ∈ rc24_complCylBox 𝒜 ℬ then Classical.choose ((rc24_mem_complCylBox 𝒜 ℬ S).mp h) else ∅

end StatMech.Walls
