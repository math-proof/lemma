/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/ScratchSixVertexAlignedFirstReturn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoDisagreementStrand.Part16
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialCheckerboard
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryToggleParity.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FiniteFirstReturn.Part8
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairSwitchNoUnitCounterexample.Part2
import Def.StatisticalMechanics.Code.FrontierD.ScratchSixVertexAlignedFirstReturn.Part2
open StatMech.FrontierD


namespace ScratchLocalRetieC

theorem localPreferredPairing_compatible
    (p : SixVertexLocalIncomingPattern) (hp : p.Ice) :
    compatible (localPreferredPairing p) p := by
  unfold localPreferredPairing compatible at *
  decide +revert

theorem compatible_iff_fkLoopPairingCompatible
    {T : EvenTorus} (omega : SixVertexArrows T)
    (v : T.Vertex) (pairing : Bool) :
    compatible pairing (sixVertexLocalIncomingPattern omega v) <->
      fkLoopPairingCompatible pairing omega v := by
  unfold compatible fkLoopPairingCompatible
    sixVertexLocalIncomingPattern
  cases pairing <;> simp [bne_iff_ne]

end ScratchLocalRetieC
