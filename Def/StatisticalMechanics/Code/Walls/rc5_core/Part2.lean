/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc5_reflectinvolution.Part4
import Theorem.StatisticalMechanics.Code.Walls.rc5_reindextransfer
import Theorem.StatisticalMechanics.Code.Walls.rc5_doubledboxcount.Part2
import Theorem.StatisticalMechanics.Code.Walls.rc5_dpairsmodular
import Theorem.StatisticalMechanics.Code.Walls.rc5_itercompcard
import Theorem.StatisticalMechanics.Code.Walls.rc5_nonvacuity
import Theorem.StatisticalMechanics.Code.Walls.rc2_core.Part3
import Theorem.StatisticalMechanics.Code.Walls.rc5_core.Part2
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace


def rc5_BoxReflectInjectionAll : Prop :=
  ∀ (n : ℕ) (A B : Set (ConfigSpace (Fin n))), rc5_BoxReflectInjection A B


end StatMech.Walls
