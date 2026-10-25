/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rmr_reflectinvolution.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.PerOrbitCardClose.Part8
import Theorem.StatisticalMechanics.Code.Walls.rmr_reflectinvolution
open Finset
open scoped StatMech


namespace StatMech.Walls

variable {α : Type*} [Fintype α] [DecidableEq α]


def rmr_reflect (B : Set (ConfigSpace α)) : Set (ConfigSpace α) := rmr_compl ⁻¹' B

end StatMech.Walls
