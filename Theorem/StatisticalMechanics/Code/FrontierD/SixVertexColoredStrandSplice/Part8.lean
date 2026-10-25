/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredStrandSplice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexColoredLoopPairing.Part16
import Def.StatisticalMechanics.Code.FrontierD.SixVertexColoredStrandSplice.Part8
open Finset


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem FKColoredStrandSplice.symm_target
    {T : EvenTorus} {source : FKColoredLoopPairingPair T}
    (splice : FKColoredStrandSplice source) :
    splice.symm.target = source := by
  funext layer
  apply FKColoredLoopPairing.ext
  · rfl
  · funext d
    exact splice.symm_rawColor (layer, d)

end
end StatMech.FrontierD
