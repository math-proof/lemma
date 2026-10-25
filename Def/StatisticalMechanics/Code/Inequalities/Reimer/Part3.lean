/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/Reimer.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.BK.Part4
import Theorem.StatisticalMechanics.Code.Inequalities.DisjointOccurrence.Part3
import Theorem.StatisticalMechanics.Code.Inequalities.Reimer.Part2
open MeasureTheory Finset
open scoped NNReal


namespace StatMech

open ConfigSpace

variable {E F : Type*}


def flipEquiv : ConfigSpace E ≃ ConfigSpace E where
  toFun := flipCfg
  invFun := flipCfg
  left_inv := flipCfg_flipCfg
  right_inv := flipCfg_flipCfg

end StatMech
