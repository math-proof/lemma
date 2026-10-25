/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc35hallproof.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc34butterfly.Part2
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


noncomputable def rc35_traceSlice (𝒜 ℬ : Finset (Finset α)) (K S : Finset α) :
    Finset (Finset α) :=
  (rc10_reflInter 𝒜 ℬ).filter (fun R => R ∩ K = S ∩ K)

end StatMech.Walls
