/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc80structuredwall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc79toporbit.Part4
import Theorem.StatisticalMechanics.Code.Walls.rc80structuredwall
set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace


variable {ι : Type*} [Fintype ι] [DecidableEq ι]


variable {κ : Type*} [Fintype κ] [DecidableEq κ]


def rc80_restL (w : ConfigSpace (ι ⊕ κ)) : ConfigSpace ι := fun i => w (Sum.inl i)

def rc80_restR (w : ConfigSpace (ι ⊕ κ)) : ConfigSpace κ := fun j => w (Sum.inr j)


def rc80_prodFam (A₁ : Finset (ConfigSpace ι)) (A₂ : Finset (ConfigSpace κ)) :
    Finset (ConfigSpace (ι ⊕ κ)) :=
  Finset.univ.filter (fun w => rc80_restL w ∈ A₁ ∧ rc80_restR w ∈ A₂)

end StatMech.Walls
