/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredLoopPairing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairLoopFiber.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryToggleParity.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexColoredLoopPairing.Part13


namespace StatMech.FrontierD

noncomputable section

theorem fkColoredVertexCrossTarget_upCount
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (mask : T.Vertex -> Bool)
    (hbond : FKColoredVertexCrossBondCoherent source mask)
    (layer : Bool) :
    (sixVertexUpCount
        (svTorusVerticalRows T
          (fkColoredVertexCrossTarget source mask hbond layer).arrows
          (svFinLast T.height_pos)) : Int) =
      (sixVertexUpCount
        (svTorusVerticalRows T (source layer).arrows
          (svFinLast T.height_pos)) : Int) +
        fkColoredVertexCrossSeamDelta source mask hbond layer := by
  let targetRow := svTorusVerticalRows T
    (fkColoredVertexCrossTarget source mask hbond layer).arrows
    (svFinLast T.height_pos)
  let sourceRow := svTorusVerticalRows T (source layer).arrows
    (svFinLast T.height_pos)
  have htarget : (∑ i, ((targetRow i).toNat : Int)) =
      (sixVertexUpCount targetRow : Int) := by
    exact_mod_cast sum_bool_toNat_eq_sixVertexUpCount targetRow
  have hsource : (∑ i, ((sourceRow i).toNat : Int)) =
      (sixVertexUpCount sourceRow : Int) := by
    exact_mod_cast sum_bool_toNat_eq_sixVertexUpCount sourceRow
  unfold fkColoredVertexCrossSeamDelta
  change (sixVertexUpCount targetRow : Int) =
    (sixVertexUpCount sourceRow : Int) +
      ∑ i, (((targetRow i).toNat : Int) - ((sourceRow i).toNat : Int))
  rw [Finset.sum_sub_distrib, htarget, hsource]
  ring

theorem fkColoredVertexCrossTarget_middleSectors
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (mask : T.Vertex -> Bool)
    (hbond : FKColoredVertexCrossBondCoherent source mask)
    (n : Nat) (hn : 0 < n)
    (hlower : sixVertexUpCount
        (svTorusVerticalRows T (source false).arrows
          (svFinLast T.height_pos)) = n - 1)
    (hupper : sixVertexUpCount
        (svTorusVerticalRows T (source true).arrows
          (svFinLast T.height_pos)) = n + 1)
    (hdeltaLower : fkColoredVertexCrossSeamDelta
      source mask hbond false = 1)
    (hdeltaUpper : fkColoredVertexCrossSeamDelta
      source mask hbond true = -1) :
    sixVertexUpCount
        (svTorusVerticalRows T
          (fkColoredVertexCrossTarget source mask hbond false).arrows
          (svFinLast T.height_pos)) = n /\
      sixVertexUpCount
        (svTorusVerticalRows T
          (fkColoredVertexCrossTarget source mask hbond true).arrows
          (svFinLast T.height_pos)) = n := by
  constructor
  · have h := fkColoredVertexCrossTarget_upCount
      source mask hbond false
    rw [hlower, hdeltaLower] at h
    have hnInt : ((n - 1 : Nat) : Int) + 1 = (n : Int) := by omega
    rw [hnInt] at h
    exact_mod_cast h
  · have h := fkColoredVertexCrossTarget_upCount
      source mask hbond true
    rw [hupper, hdeltaUpper] at h
    have hnInt : ((n + 1 : Nat) : Int) + (-1) = (n : Int) := by omega
    rw [hnInt] at h
    exact_mod_cast h

end
end StatMech.FrontierD
