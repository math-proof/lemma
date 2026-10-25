/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc92basecase.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc80structuredwall.Part3
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace


set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in 


theorem rc92_wall_fin2 :
    ∀ A B : Finset (ConfigSpace (Fin 2)),
      (rc80_disjOccG A B).card ≤ (rc80_reflInterG A B).card := by
  decide


end StatMech.Walls
