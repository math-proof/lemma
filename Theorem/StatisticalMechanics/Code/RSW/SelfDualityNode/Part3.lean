/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/SelfDualityNode.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Theorem.StatisticalMechanics.Code.BeffaraDC.SelfDualValue
import Theorem.StatisticalMechanics.Code.Universality.G3PercDualityFull.Part2
import Def.StatisticalMechanics.Code.RSW.SelfDualityNode.Part3
open scoped BigOperators ENNReal NNReal
open MeasureTheory


namespace StatMech

namespace RSW

@[simp] theorem rsd_dualBC_wired : rsd_dualBC .wired = .free := rfl

@[simp] theorem rsd_dualBC_free : rsd_dualBC .free = .wired := rfl


@[simp] theorem rsd_dualBC_dualBC (bc : rsd_BC) : rsd_dualBC (rsd_dualBC bc) = bc := by
  cases bc <;> rfl


end RSW
end StatMech
