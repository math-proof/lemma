/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFKInternalCylinder.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeTypedFKCylinderGeometry.Part8
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeInfiniteVolume.Part7
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeTypedFKInternalCylinder.Part2
open scoped BigOperators symmDiff


namespace StatMech.FrontierA

noncomputable section

def cubicalInternalCentralComplement (N m : Nat) (hNm : N <= m) :
    Finset (CubicalPlaquette (oddCubeSide m) (oddCubeSide m) (oddCubeSide m)) :=
  multibondCut cubicalDualEnds (cubicalInternalCentralBlockSpin N m) \
    cubicalInternalCentralSheet N m hNm

end
end StatMech.FrontierA
