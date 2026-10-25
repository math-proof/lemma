/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc22doublecover.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc21persupport.Part5
import Theorem.StatisticalMechanics.Code.Walls.rc2_dpairsdowndownmono
import Theorem.StatisticalMechanics.Code.Walls.rc2_blendpoint
import Theorem.StatisticalMechanics.Code.Walls.rc16sliceunion
import Mathlib.Combinatorics.SetFamily.Compression.UV
import Theorem.StatisticalMechanics.Code.Walls.rc22doublecover.Part2
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


def rc22_InterCountResidue : Prop :=
  ∀ (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))),
    #(rc20_famCylBox 𝒜 ℬ) ≤ #(𝒜 ∩ rc22_complFam ℬ)


end StatMech.Walls
