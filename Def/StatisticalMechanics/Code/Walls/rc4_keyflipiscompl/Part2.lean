/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc4_keyflipiscompl.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rmr_reflectinvolution.Part2
import Theorem.StatisticalMechanics.Code.Walls.rc3_core.Part3
import Instance.StatisticalMechanics.Code.Walls.rc4_keyflipiscompl
open Finset
open scoped StatMech


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*}


def rc4_restrict (k : ConfigSpace α × ConfigSpace α) (ω : ConfigSpace α) :
    ConfigSpace (rc4_differ k) := fun b => ω b.val

end StatMech.Walls
