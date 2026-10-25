/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredLoopPairing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairLoopFiber.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryToggleParity.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexColoredLoopPairing.Part4


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem FKColoredLocalPairing.sideColor_west
    (cfg : FKColoredLocalPairing) : cfg.sideColor .west = cfg.west := by
  rcases cfg with ⟨pairing, west, east⟩
  cases pairing <;> rfl

@[simp] theorem FKColoredLocalPairing.sideColor_east
    (cfg : FKColoredLocalPairing) : cfg.sideColor .east = cfg.east := by
  rcases cfg with ⟨pairing, west, east⟩
  cases pairing <;> rfl

end
end StatMech.FrontierD
