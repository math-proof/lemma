/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6overlapsplit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc3_minimalwitnessencoded
import Instance.StatisticalMechanics.Code.Walls.rc6overlapsplit
open Finset


namespace StatMech.Walls

open StatMech ConfigSpace


open WitnessClass

variable {α : Type*}


noncomputable def rc6_classify (K L : Set α) (i : α) : WitnessClass := by
  classical
  exact
    if i ∈ K then (if i ∈ L then both else onlyK)
    else (if i ∈ L then onlyL else neither)


end StatMech.Walls
