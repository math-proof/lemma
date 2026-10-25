/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationLoopWalk.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationTransitionWalk.Part4
import Theorem.StatisticalMechanics.Code.Onsager.DecorationCycleWeight
import Def.StatisticalMechanics.Code.Onsager.DecorationLoopWalk.Part3


namespace StatMech.Onsager

open Finset SimpleGraph

@[simp] theorem ons_decKWChainLast_append_singleton
    (start : ons_Dart L) (tail : List (ons_Dart L)) (finish : ons_Dart L) :
    ons_decKWChainLast start (tail ++ [finish]) = finish := by
  induction tail generalizing start with
  | nil => rfl
  | cons target rest ih => exact ih target

end StatMech.Onsager
