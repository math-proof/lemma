/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/PerOrbitCardClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.ReimerSwapInjClose.Part3
open Finset MeasureTheory
open scoped NNReal FinsetFamily


namespace StatMech

open ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


def poc_flip (d : α → Bool) (ω : ConfigSpace α) : ConfigSpace α :=
  fun a => if d a then !ω a else ω a


def poc_keyFlip (k : ConfigSpace α × ConfigSpace α) : ConfigSpace α → ConfigSpace α :=
  poc_flip (fun a => decide (k.1 a ≠ k.2 a))

end StatMech
