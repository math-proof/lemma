/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDualBarrierAuxiliary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectSeamPatternPreservation.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectAugmentedBarrierWindingMass.Part2


namespace StatMech.FrontierD

noncomputable section

def fkRectColumnBand (R : FKRectTorus)
    (left right lower upper : Nat) : Set R.Vertex :=
  {v | left <= v.1.val ∧ v.1.val <= right ∧
    lower <= v.2.val ∧ v.2.val <= upper}

end
end StatMech.FrontierD
