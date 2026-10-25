/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredStrandSplice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexColoredLoopPairing.Part16
import Def.StatisticalMechanics.Code.FrontierD.SixVertexColoredStrandSplice.Part3
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem fkColoredStrandSpliceBondCoherent_iff_boundaryInvariant
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (targetPairing : Bool -> FKMedialLoopPairing T)
    (slotEquiv : FKLayeredStrandSlot T ≃ FKLayeredStrandSlot T) :
    FKColoredStrandSpliceBondCoherent source targetPairing slotEquiv ↔
      forall x : FKLayeredMedialDart T,
        fkColoredStrandSpliceRawColor source targetPairing slotEquiv
            (x.1, fkMedialBoundaryStep (targetPairing x.1) x.2) =
          fkColoredStrandSpliceRawColor source targetPairing slotEquiv x := by
  constructor
  · intro hbond x
    rw [fkMedialBoundaryStep_apply]
    exact (hbond
      (x.1, fkMedialLocalMate (targetPairing x.1) x.2)).trans
        (fkColoredStrandSpliceRawColor_localMate
          source targetPairing slotEquiv x.1 x.2)
  · intro hboundary x
    let dlocal := fkMedialLocalMate (targetPairing x.1) x.2
    have h := hboundary (x.1, dlocal)
    rw [fkMedialBoundaryStep_apply,
      fkMedialLocalMate_involutive] at h
    exact h.trans
      (fkColoredStrandSpliceRawColor_localMate
        source targetPairing slotEquiv x.1 x.2)

end
end StatMech.FrontierD
