/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc49doubled.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc48cover.Part4
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerDoubled.Part6
import Mathlib.Combinatorics.Hall.Basic
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


def rc49_jointImage (S K L : Finset α) : Finset α :=
  (S ∩ K) ∪ (L ∩ Sᶜ) ∪ (S ∩ (K ∪ L)ᶜ)


end StatMech.Walls
