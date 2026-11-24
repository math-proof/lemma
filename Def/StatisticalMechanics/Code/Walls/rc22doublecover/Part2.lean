module
public import Theorem.StatisticalMechanics.Code.Walls.rc21persupport.Part5
public import Theorem.StatisticalMechanics.Code.Walls.rc2_dpairsdowndownmono
public import Theorem.StatisticalMechanics.Code.Walls.rc2_blendpoint
public import Theorem.StatisticalMechanics.Code.Walls.rc16sliceunion
public import Mathlib.Combinatorics.SetFamily.Compression.UV
public import Theorem.StatisticalMechanics.Code.Walls.rc22doublecover
open Finset
open scoped FinsetFamily StatMech NNReal


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc22doublecover.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


noncomputable def rc22_complFam (ℬ : Finset (Finset α)) : Finset (Finset α) :=
  ℬ.image compl

end StatMech.Walls
