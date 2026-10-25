/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredLoopPairing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairLoopFiber.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryToggleParity.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexColoredLoopPairing


namespace StatMech.FrontierD

noncomputable section

structure FKColoredLoopPairing (T : EvenTorus) where
  pairing : FKMedialLoopPairing T
  color : FKMedialDart T → Bool
  color_localMate : ∀ d, color (fkMedialLocalMate pairing d) = color d
  color_bondMate : ∀ d, color (fkMedialBondMate T d) = color d

end
end StatMech.FrontierD
