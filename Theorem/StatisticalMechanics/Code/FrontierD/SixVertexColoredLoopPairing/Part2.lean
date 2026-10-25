/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredLoopPairing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairLoopFiber.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryToggleParity.Part3
import Structure.StatisticalMechanics.Code.FrontierD.SixVertexColoredLoopPairing


namespace StatMech.FrontierD

noncomputable section

@[ext] theorem FKColoredLoopPairing.ext
    {T : EvenTorus} {a b : FKColoredLoopPairing T}
    (hpairing : a.pairing = b.pairing) (hcolor : a.color = b.color) :
    a = b := by
  cases a
  cases b
  simp_all

end
end StatMech.FrontierD
