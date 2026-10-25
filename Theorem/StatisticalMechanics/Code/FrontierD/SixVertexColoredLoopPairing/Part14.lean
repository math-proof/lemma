/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredLoopPairing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairLoopFiber.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryToggleParity.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexColoredLoopPairing.Part11


namespace StatMech.FrontierD

noncomputable section

theorem fkColoredVertexCrossTarget_localPairing
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (mask : T.Vertex -> Bool)
    (hbond : FKColoredVertexCrossBondCoherent source mask)
    (v : T.Vertex) :
    ((fkColoredVertexCrossTarget source mask hbond false).localPairing v,
        (fkColoredVertexCrossTarget source mask hbond true).localPairing v) =
      fkColoredLocalPairCrossIf (mask v)
        ((source false).localPairing v, (source true).localPairing v) := by
  cases hm : mask v <;>
    by_cases hwest : (source false).color (v, .west) =
      (source true).color (v, .west)
  all_goals apply Prod.ext
  all_goals apply FKColoredLocalPairing.ext
  all_goals simp [fkColoredVertexCrossTarget,
    FKColoredLoopPairing.localPairing, fkColoredVertexCrossRawColor,
    fkColoredLocalPairCrossIf, fkColoredLocalPairReconnection,
    hm, hwest]

theorem fkColoredVertexCrossRawColor_target
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (mask : T.Vertex -> Bool)
    (hbond : FKColoredVertexCrossBondCoherent source mask)
    (x : FKLayeredMedialDart T) :
    fkColoredVertexCrossRawColor
        (fkColoredVertexCrossTarget source mask hbond) mask x =
      fkLayeredLoopColor source x := by
  rcases x with ⟨layer, ⟨v, side⟩⟩
  unfold fkColoredVertexCrossRawColor
  rw [fkColoredVertexCrossTarget_localPairing]
  let pair := ((source false).localPairing v,
    (source true).localPairing v)
  change (if layer then
      (fkColoredLocalPairCrossIf (mask v)
        (fkColoredLocalPairCrossIf (mask v) pair)).2
    else
      (fkColoredLocalPairCrossIf (mask v)
        (fkColoredLocalPairCrossIf (mask v) pair)).1).sideColor side = _
  rw [fkColoredLocalPairCrossIf_involutive]
  unfold fkLayeredLoopColor
  cases layer
  · exact (source false).localPairing_sideColor v side
  · exact (source true).localPairing_sideColor v side

theorem fkColoredVertexCrossTarget_bondCoherent
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (mask : T.Vertex -> Bool)
    (hbond : FKColoredVertexCrossBondCoherent source mask) :
    FKColoredVertexCrossBondCoherent
      (fkColoredVertexCrossTarget source mask hbond) mask := by
  intro x
  rw [fkColoredVertexCrossRawColor_target,
    fkColoredVertexCrossRawColor_target]
  rcases x with ⟨layer, d⟩
  exact (source layer).color_bondMate d


@[simp] theorem fkColoredVertexCrossTarget_involutive
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (mask : T.Vertex -> Bool)
    (hbond : FKColoredVertexCrossBondCoherent source mask) :
    fkColoredVertexCrossTarget
        (fkColoredVertexCrossTarget source mask hbond) mask
        (fkColoredVertexCrossTarget_bondCoherent source mask hbond) =
      source := by
  funext layer
  apply FKColoredLoopPairing.ext
  · rfl
  · funext d
    exact fkColoredVertexCrossRawColor_target source mask hbond (layer, d)

end
end StatMech.FrontierD
