/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc10core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc9core.Part2
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerCompressLib.Part2
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerIterationClose.Part4
import Theorem.StatisticalMechanics.Code.Walls.rc10core.Part3
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


def rc10_DeficitBridgeIncInc : Prop :=
  ∀ (n : ℕ) (A B : Set (ConfigSpace (Fin n))), IsIncreasing A → IsIncreasing B →
    rc5_deficit A B ≤ 0


end StatMech.Walls
