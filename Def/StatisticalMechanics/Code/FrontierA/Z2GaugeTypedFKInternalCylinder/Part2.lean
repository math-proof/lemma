/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFKInternalCylinder.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeTypedFKCylinderGeometry.Part8
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeInfiniteVolume.Part7
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeTypedFKInternalCylinder
open scoped BigOperators symmDiff


namespace StatMech.FrontierA

noncomputable section

def cubicalInternalCentralBlockSpin (N m : Nat) :
    CubicalDualVertex (oddCubeSide m) (oddCubeSide m) (oddCubeSide m) -> Bool
  | none => false
  | some q => decide
      (m <= q.x.val ∧ q.x.val < m + N ∧
       m <= q.y.val ∧ q.y.val < m + N ∧
       m - N <= q.z.val ∧ q.z.val < m)

end
end StatMech.FrontierA
