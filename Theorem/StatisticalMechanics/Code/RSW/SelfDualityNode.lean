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
import Def.StatisticalMechanics.Code.RSW.SelfDualityNode
open scoped BigOperators ENNReal NNReal
open MeasureTheory


namespace StatMech

namespace RSW

theorem rsd_dualParam_coupling {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    rsd_dualCoupling p (BeffaraDC.dualParam p q) q := by
  unfold rsd_dualCoupling
  
  
  have h := BeffaraDC.dualParam_product_eq hp hp1 hq
  rw [mul_comm p (BeffaraDC.dualParam p q),
    mul_comm (1 - p) (1 - BeffaraDC.dualParam p q)]
  exact h


end RSW
end StatMech
