module
public import Def.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairLoopFiber.Part5
public import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryToggleParity.Part3
public import Def.StatisticalMechanics.Code.FrontierD.SixVertexColoredLoopPairing.Part12


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredLoopPairing.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

theorem fkColoredVertexCrossTarget_totalC
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (mask : T.Vertex -> Bool)
    (hbond : FKColoredVertexCrossBondCoherent source mask) :
    fkColoredLoopPairingPairTotalC
        (fkColoredVertexCrossTarget source mask hbond) =
      fkColoredLoopPairingPairTotalC source := by
  unfold fkColoredLoopPairingPairTotalC sixVertexTorusCTypeCount
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v hv
  rw [← FKColoredLoopPairingPair.localCTypeCount,
    ← FKColoredLoopPairingPair.localCTypeCount,
    fkColoredVertexCrossTarget_localPairing]
  cases hm : mask v
  · rfl
  · exact fkColoredLocalPairReconnection_cTypeCount _

end
end StatMech.FrontierD
