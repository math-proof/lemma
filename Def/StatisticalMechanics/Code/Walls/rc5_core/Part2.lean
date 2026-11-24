module
public import Theorem.StatisticalMechanics.Code.Walls.rc5_reflectinvolution.Part4
public import Theorem.StatisticalMechanics.Code.Walls.rc5_reindextransfer
public import Theorem.StatisticalMechanics.Code.Walls.rc5_doubledboxcount.Part2
public import Theorem.StatisticalMechanics.Code.Walls.rc5_dpairsmodular
public import Theorem.StatisticalMechanics.Code.Walls.rc5_itercompcard
public import Theorem.StatisticalMechanics.Code.Walls.rc5_nonvacuity
public import Theorem.StatisticalMechanics.Code.Walls.rc2_core.Part3
public import Theorem.StatisticalMechanics.Code.Walls.rc5_core.Part2
open Finset
open scoped FinsetFamily StatMech NNReal


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_core.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Walls

open StatMech ConfigSpace


def rc5_BoxReflectInjectionAll : Prop :=
  ∀ (n : ℕ) (A B : Set (ConfigSpace (Fin n))), rc5_BoxReflectInjection A B


end StatMech.Walls
