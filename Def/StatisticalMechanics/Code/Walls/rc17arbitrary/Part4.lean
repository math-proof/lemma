/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc17arbitrary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc16sliceunion
import Theorem.StatisticalMechanics.Code.Walls.rc9core.Part2
import Theorem.StatisticalMechanics.Code.Walls.rc8core.Part2
import Theorem.StatisticalMechanics.Code.Inequalities.Reimer.Part3
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerButterflyInjClose.Part2
import Theorem.StatisticalMechanics.Code.Walls.rc17arbitrary.Part4
open Finset MeasureTheory
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


noncomputable def rc17_upClosure {n : ℕ} (A : Set (ConfigSpace (Fin n))) :
    Set (ConfigSpace (Fin n)) :=
  {ω | ∃ ω₀ ∈ A, ω₀ ≤ ω}


end StatMech.Walls
