/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc4_keyflipiscompl.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rmr_reflectinvolution.Part2
import Theorem.StatisticalMechanics.Code.Walls.rc3_core.Part3
import Def.StatisticalMechanics.Code.Walls.rc4_keyflipiscompl
open Finset
open scoped StatMech


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*}


instance instDecidableEqDiffer (k : ConfigSpace α × ConfigSpace α) [DecidableEq α] :
    DecidableEq (rc4_differ k) :=
  inferInstanceAs (DecidableEq {a : α // k.1 a ≠ k.2 a})

instance instFintypeDiffer (k : ConfigSpace α × ConfigSpace α) [Fintype α] [DecidableEq α] :
    Fintype (rc4_differ k) :=
  inferInstanceAs (Fintype {a : α // k.1 a ≠ k.2 a})


end StatMech.Walls
