/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc3_hallforswapinjection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.ReimerSwapInjClose.Part3
import Theorem.StatisticalMechanics.Code.Walls.rc2_hallavailable
import Mathlib.Combinatorics.Hall.Basic
open Finset Function
open StatMech ConfigSpace


namespace StatMech.Walls

variable {α : Type*} [Fintype α] [DecidableEq α]


def swapRel (A B : Set (ConfigSpace α)) :
    {p : ConfigSpace α × ConfigSpace α // p.1 ∈ disjointOccurrence A B} →
      (ConfigSpace α × ConfigSpace α) → Prop :=
  fun p q => sameOrbit p.val q ∧ q.1 ∈ A ∧ q.2 ∈ B


end StatMech.Walls
