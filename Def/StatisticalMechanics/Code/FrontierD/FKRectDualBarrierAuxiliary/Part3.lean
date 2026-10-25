/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDualBarrierAuxiliary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectSeamPatternPreservation.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectAugmentedBarrierWindingMass.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDualBarrierAuxiliary


namespace StatMech.FrontierD

noncomputable section

def FKRectColumnBandConnectionChainSpans
    (R : FKRectTorus) (left right : Nat) (x : Fin R.width)
    (hleft : left <= x.val) (hright : x.val <= right)
    (t : Finset
      (FKRectColumnBandVertex R left right 1 (R.height - 1) ×
        FKRectColumnBandVertex R left right 1 (R.height - 1))) : Prop :=
  ∀ sigma,
    sigma ∈ fkRectInducedConnectionChainEvent R
      (fkRectColumnBand R left right 1 (R.height - 1)) t ->
    (FK.openSub
      (fkRectInducedGraph R
        (fkRectColumnBand R left right 1 (R.height - 1))) sigma).Reachable
      (fkRectColumnBandRowOne R left right x hleft hright)
      (fkRectColumnBandLastRow R left right x hleft hright)

end
end StatMech.FrontierD
