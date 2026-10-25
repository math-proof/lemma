/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredLoopPairing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairLoopFiber.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryToggleParity.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexColoredLoopPairing.Part10


namespace StatMech.FrontierD

noncomputable section

theorem fkColoredVertexCrossRawColor_localMate
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (mask : T.Vertex -> Bool) (layer : Bool) (d : FKMedialDart T) :
    fkColoredVertexCrossRawColor source mask
        (layer, fkMedialLocalMate (source layer).pairing d) =
      fkColoredVertexCrossRawColor source mask (layer, d) := by
  rcases d with ⟨v, side⟩
  let pair := ((source false).localPairing v,
    (source true).localPairing v)
  let crossed := fkColoredLocalPairCrossIf (mask v) pair
  let cfg := if layer then crossed.2 else crossed.1
  have hp : cfg.pairing = (source layer).pairing v := by
    cases layer
    · simpa [cfg, crossed, pair] using
        (fkColoredLocalPairCrossIf_pairing (mask v) false pair)
    · simpa [cfg, crossed, pair] using
        (fkColoredLocalPairCrossIf_pairing (mask v) true pair)
  rw [fkMedialLocalMate_eq_localSideMate]
  change cfg.sideColor
      (fkMedialLocalSideMate ((source layer).pairing v) side) =
    cfg.sideColor side
  rw [← hp]
  exact cfg.sideColor_localMate side


end
end StatMech.FrontierD
