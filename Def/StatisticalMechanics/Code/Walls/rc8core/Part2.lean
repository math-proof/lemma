/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc8core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc7core.Part4
import Theorem.StatisticalMechanics.Code.Inequalities.Harris
import Theorem.StatisticalMechanics.Code.Inequalities.Reimer.Part3
import Theorem.StatisticalMechanics.Code.Walls.rc8core
open Finset MeasureTheory
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


def rc8_DeficitBridgeNonOpp : Prop :=
  ∀ (n : ℕ) (A B : Set (ConfigSpace (Fin n))),
    ¬ ((IsIncreasing A ∧ IsDecreasing B) ∨ (IsDecreasing A ∧ IsIncreasing B)) →
      rc5_deficit A B ≤ 0


end StatMech.Walls
