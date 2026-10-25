/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectAugmentedBarrierWindingMass.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectAugmentedSourceBarrier.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectAugmentedBarrierWindingMass
open SimpleGraph


namespace StatMech.FrontierD

noncomputable section

def fkRectSeparatedVerticalWindingEvent (R : FKRectTorus)
    (leftRight : Nat) : Set R.Configuration :=
  fkRectNoLeftStripCrossingEvent R leftRight ∩
    fkRectVerticalWindingEvent R

end
end StatMech.FrontierD
