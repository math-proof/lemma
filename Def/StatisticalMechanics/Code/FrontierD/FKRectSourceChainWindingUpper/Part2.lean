/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectSourceChainWindingUpper.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectSourceSeamWindingUpper.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectSourceChainWindingUpper
open SimpleGraph


namespace StatMech.FrontierD

noncomputable section

def FKRectRightBandConnectionChainSpans
    (R : FKRectTorus) (cut : Nat) (x : Fin R.width)
    (hx : cut <= x.val)
    (t : Finset (FKRectRightStripBandVertex R cut 1 (R.height - 1) ×
      FKRectRightStripBandVertex R cut 1 (R.height - 1))) : Prop :=
  forall sigma,
    sigma ∈ fkRectInducedConnectionChainEvent R
      (fkRectRightStripBand R cut 1 (R.height - 1)) t ->
    (FK.openSub
      (fkRectInducedGraph R
        (fkRectRightStripBand R cut 1 (R.height - 1))) sigma).Reachable
      (fkRectRightBandRowOne R cut x hx)
      (fkRectRightBandLastRow R cut x hx)


end
end StatMech.FrontierD
