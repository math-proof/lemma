/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc63doubledinjection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc62reflfunctional.Part3
import Def.StatisticalMechanics.Code.Walls.rc63doubledinjection.Part2
set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {n : ℕ}


set_option maxRecDepth 8000 in
set_option maxHeartbeats 8000000 in 


theorem rc63_downdown_not_good :
    rc63_opGood (Down.compression 0) (Down.compression 0) = false := by
  decide


end StatMech.Walls
