/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDualBarrierAuxiliary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectSeamPatternPreservation.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectAugmentedBarrierWindingMass.Part2
import Def.StatisticalMechanics.Code.FrontierD.FKRectDualBarrierAuxiliary.Part3


namespace StatMech.FrontierD

noncomputable section

theorem fkRectColumnBandConnectionChainSpans_connectionPathPairs
    (R : FKRectTorus) (left right : Nat) (x : Fin R.width)
    (hleft : left <= x.val) (hright : x.val <= right)
    (n : Nat)
    (v : Fin (n + 1) ->
      FKRectColumnBandVertex R left right 1 (R.height - 1))
    (hfirst : v 0 =
      fkRectColumnBandRowOne R left right x hleft hright)
    (hlast : v (Fin.last n) =
      fkRectColumnBandLastRow R left right x hleft hright) :
    FKRectColumnBandConnectionChainSpans R left right x hleft hright
      (connectionPathPairs n v) := by
  intro sigma hchain
  rw [← hfirst, ← hlast]
  apply reachable_first_last_of_connectionPathPairs n v
  intro i
  exact hchain _ (connectionPathPairs_pair_mem n v i)


end
end StatMech.FrontierD
