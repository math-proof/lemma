/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairTotalCMonotone.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairDecoratedHall.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairTotalCMonotone
open Finset Matrix Polynomial


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexMarkedSectorPairMass_le_of_totalCEmbedding
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
    sixVertexMarkedSectorPairMass T lower upper k <=
      sixVertexMarkedSectorPairMass T middle middle k := by
  apply sixVertexMarkedSectorPairMass_le_of_decoratedHall
    (related := fun _ _ => True)
  rw [sixVertexMarkedDecoratedPairHall_iff_exists_injective]
  let embedding := markedDecoratedPairEmbeddingOfTotalCLe
    T lower middle upper k base htotal
  exact ⟨embedding, embedding.injective, fun _ => trivial⟩


theorem sixVertexMarkedTraceCoefficientwiseLogConcave_of_totalCEmbedding
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (base :
      (SixVertexMarkedSectorConfiguration T
          ⟨middle.val - 1, by omega⟩ ×
        SixVertexMarkedSectorConfiguration T
          ⟨middle.val + 1, by omega⟩) ↪
      (SixVertexMarkedSectorConfiguration T middle ×
        SixVertexMarkedSectorConfiguration T middle))
    (htotal : forall pair,
      sixVertexTorusCTypeCount pair.1.1 +
          sixVertexTorusCTypeCount pair.2.1 <=
        sixVertexTorusCTypeCount (base pair).1.1 +
          sixVertexTorusCTypeCount (base pair).2.1) :
    SixVertexMarkedTraceCoefficientwiseLogConcave
      T.width T.height middle.val := by
  apply sixVertexMarkedTraceCoefficientwiseLogConcave_of_decoratedHall
    T middle hmiddle_pos hmiddle_lt
  intro k
  refine ⟨fun _ _ => True, ?_⟩
  rw [sixVertexMarkedDecoratedPairHall_iff_exists_injective]
  let embedding := markedDecoratedPairEmbeddingOfTotalCLe T
    ⟨middle.val - 1, by omega⟩ middle
    ⟨middle.val + 1, by omega⟩ k base htotal
  exact ⟨embedding, embedding.injective, fun _ => trivial⟩

end
end StatMech.FrontierD
