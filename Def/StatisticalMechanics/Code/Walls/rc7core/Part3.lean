/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc7core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc6core.Part3
import Theorem.StatisticalMechanics.Code.Walls.rc7core.Part3
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace


def rc7_DeficitBridge : Prop :=
  ∀ (n : ℕ) (A B : Set (ConfigSpace (Fin n))), rc5_deficit A B ≤ 0


end StatMech.Walls
