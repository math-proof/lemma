/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredStrandSplice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexColoredLoopPairing.Part16
import Def.StatisticalMechanics.Code.FrontierD.SixVertexColoredStrandSplice.Part11
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem FKColoredStrandSplice.target_upCount
    {T : EvenTorus} {source : FKColoredLoopPairingPair T}
    (splice : FKColoredStrandSplice source) (layer : Bool) :
    (sixVertexUpCount
        (svTorusVerticalRows T (splice.target layer).arrows
          (svFinLast T.height_pos)) : Int) =
      (sixVertexUpCount
        (svTorusVerticalRows T (source layer).arrows
          (svFinLast T.height_pos)) : Int) + splice.seamDelta layer := by
  let targetRow := svTorusVerticalRows T (splice.target layer).arrows
    (svFinLast T.height_pos)
  let sourceRow := svTorusVerticalRows T (source layer).arrows
    (svFinLast T.height_pos)
  have htarget : (∑ i, ((targetRow i).toNat : Int)) =
      (sixVertexUpCount targetRow : Int) := by
    exact_mod_cast sum_bool_toNat_eq_sixVertexUpCount targetRow
  have hsource : (∑ i, ((sourceRow i).toNat : Int)) =
      (sixVertexUpCount sourceRow : Int) := by
    exact_mod_cast sum_bool_toNat_eq_sixVertexUpCount sourceRow
  unfold FKColoredStrandSplice.seamDelta
  change (sixVertexUpCount targetRow : Int) =
    (sixVertexUpCount sourceRow : Int) +
      ∑ i, (((targetRow i).toNat : Int) - ((sourceRow i).toNat : Int))
  rw [Finset.sum_sub_distrib, htarget, hsource]
  ring

theorem FKColoredStrandSplice.target_middleSectors
    {T : EvenTorus} {source : FKColoredLoopPairingPair T}
    (splice : FKColoredStrandSplice source)
    (n : Nat) (hn : 0 < n)
    (hlower : sixVertexUpCount
        (svTorusVerticalRows T (source false).arrows
          (svFinLast T.height_pos)) = n - 1)
    (hupper : sixVertexUpCount
        (svTorusVerticalRows T (source true).arrows
          (svFinLast T.height_pos)) = n + 1)
    (hdeltaLower : splice.seamDelta false = 1)
    (hdeltaUpper : splice.seamDelta true = -1) :
    sixVertexUpCount
        (svTorusVerticalRows T (splice.target false).arrows
          (svFinLast T.height_pos)) = n /\
      sixVertexUpCount
        (svTorusVerticalRows T (splice.target true).arrows
          (svFinLast T.height_pos)) = n := by
  constructor
  · have h := splice.target_upCount false
    rw [hlower, hdeltaLower] at h
    have hnInt : ((n - 1 : Nat) : Int) + 1 = (n : Int) := by omega
    rw [hnInt] at h
    exact_mod_cast h
  · have h := splice.target_upCount true
    rw [hupper, hdeltaUpper] at h
    have hnInt : ((n + 1 : Nat) : Int) + (-1) = (n : Int) := by omega
    rw [hnInt] at h
    exact_mod_cast h

end
end StatMech.FrontierD
