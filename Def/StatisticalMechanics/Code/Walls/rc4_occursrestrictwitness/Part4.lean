/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc4_occursrestrictwitness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc3_core.Part3
import Theorem.StatisticalMechanics.Code.Inequalities.PerOrbitCardClose.Part8
import Theorem.StatisticalMechanics.Code.Walls.rc2_slabimgeqinter.Part3
import Theorem.StatisticalMechanics.Code.Walls.rc4_occursrestrictwitness.Part3
open Finset
open scoped StatMech


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*}


noncomputable def pocFrozenRestrict (k : ConfigSpace α × ConfigSpace α)
    (A : Set (ConfigSpace α)) : Set (ConfigSpace (DifferSub k)) := pocUnrestrict k ⁻¹' A

end StatMech.Walls
