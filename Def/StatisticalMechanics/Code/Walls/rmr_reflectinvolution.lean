/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rmr_reflectinvolution.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.PerOrbitCardClose.Part8
open Finset
open scoped StatMech


namespace StatMech.Walls

variable {α : Type*} [Fintype α] [DecidableEq α]


def rmr_compl (ω : ConfigSpace α) : ConfigSpace α := fun a => !ω a

end StatMech.Walls
