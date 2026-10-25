/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc80structuredwall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc79toporbit.Part4
import Theorem.StatisticalMechanics.Code.Walls.rc80structuredwall.Part2
set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace


variable {ι : Type*} [Fintype ι] [DecidableEq ι]


variable {κ : Type*} [Fintype κ] [DecidableEq κ]


def rc80_projL (K : Finset (ι ⊕ κ)) : Finset ι := Finset.univ.filter (fun i => Sum.inl i ∈ K)

def rc80_projR (K : Finset (ι ⊕ κ)) : Finset κ := Finset.univ.filter (fun j => Sum.inr j ∈ K)

end StatMech.Walls
