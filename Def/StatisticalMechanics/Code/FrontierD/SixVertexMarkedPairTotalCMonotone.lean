/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairTotalCMonotone.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairDecoratedHall.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairTotalCMonotone
open Finset Matrix Polynomial


namespace StatMech.FrontierD

noncomputable section

noncomputable def markedDecoratedPairEmbeddingOfTotalCLe
    (T : EvenTorus) (lower middle upper : Fin (T.width + 1)) (k : Nat)
    (base :
      (SixVertexMarkedSectorConfiguration T lower ×
        SixVertexMarkedSectorConfiguration T upper) ↪
      (SixVertexMarkedSectorConfiguration T middle ×
        SixVertexMarkedSectorConfiguration T middle))
    (htotal : forall pair,
      sixVertexTorusCTypeCount pair.1.1 +
          sixVertexTorusCTypeCount pair.2.1 <=
        sixVertexTorusCTypeCount (base pair).1.1 +
          sixVertexTorusCTypeCount (base pair).2.1) :
    SixVertexMarkedDecoratedPair T lower upper k ↪
      SixVertexMarkedDecoratedPair T middle middle k :=
  Function.Embedding.sigmaMap base fun pair => by
    apply Classical.choice
    apply Function.Embedding.nonempty_of_card_le
    simp only [Fintype.card_fin]
    exact sixVertexMarkedPairMultiplicityNat_mono_of_totalC (htotal pair)

end
end StatMech.FrontierD
