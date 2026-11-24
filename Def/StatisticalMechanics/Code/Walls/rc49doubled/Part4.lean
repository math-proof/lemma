module
public import Theorem.StatisticalMechanics.Code.Walls.rc48cover.Part4
public import Theorem.StatisticalMechanics.Code.Inequalities.ReimerDoubled.Part6
public import Mathlib.Combinatorics.Hall.Basic
public import Theorem.StatisticalMechanics.Code.Walls.rc49doubled.Part3
open Finset
open scoped FinsetFamily StatMech NNReal


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc49doubled.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


open Classical in


def rc49_HallDoubled : Prop :=
  ∀ (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))), rc49_HallCond 𝒜 ℬ

end StatMech.Walls
