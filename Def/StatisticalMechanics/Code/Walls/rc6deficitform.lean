module
public import Theorem.StatisticalMechanics.Code.Walls.rmr_reflectinvolution.Part2
public import Theorem.StatisticalMechanics.Code.Walls.rc3_core.Part3
public import Theorem.StatisticalMechanics.Code.Walls.rc6deficitform
open Finset
open scoped StatMech


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6deficitform.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


def rc6_complEquiv : ConfigSpace α ≃ ConfigSpace α :=
  Function.Involutive.toPerm rmr_compl rmr_compl_involutive

end StatMech.Walls
