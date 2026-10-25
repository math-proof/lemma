/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredLoopPairing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairLoopFiber.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryToggleParity.Part3
import Structure.StatisticalMechanics.Code.FrontierD.SixVertexColoredLoopPairing.Part2


namespace StatMech.FrontierD

noncomputable section

@[ext] theorem FKColoredLocalPairing.ext
    {a b : FKColoredLocalPairing}
    (hpairing : a.pairing = b.pairing)
    (hwest : a.west = b.west) (heast : a.east = b.east) : a = b := by
  cases a
  cases b
  simp_all

end
end StatMech.FrontierD
