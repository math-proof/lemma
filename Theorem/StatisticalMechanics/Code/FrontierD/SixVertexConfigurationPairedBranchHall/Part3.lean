/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexConfigurationPairedBranchHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPairBigrade.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairDecoratedHall.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPairedBranchHall.Part4
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem SixVertexConfigurationPairedBranchEmbeddings.inverse_degree
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (embeddings : SixVertexConfigurationPairedBranchEmbeddings T middle
      hmiddle_pos hmiddle_lt grade)
    (target : SixVertexConfigurationPairBigradeFiber T middle middle grade) :
    (Finset.univ.filter fun source =>
      SixVertexConfigurationPairedBranchRelated
        embeddings source target).card <= 2 := by
  have hcard := Fintype.card_le_of_embedding
    (embeddings.inverseCode target)
  simpa [Fintype.card_subtype] using hcard

theorem SixVertexConfigurationPairedBranchEmbeddings.hall
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (embeddings : SixVertexConfigurationPairedBranchEmbeddings T middle
      hmiddle_pos hmiddle_lt grade) :
    forall sources : Finset (SixVertexConfigurationPairBigradeFiber T
      (sixVertexConfigurationLowerSector middle hmiddle_pos)
      (sixVertexConfigurationUpperSector middle hmiddle_lt) grade),
      sources.card <=
        (Finset.univ.filter fun target => exists source,
          source ∈ sources ∧
            SixVertexConfigurationPairedBranchRelated
              embeddings source target).card := by
  apply finiteRelationHall_of_bidegree
    (SixVertexConfigurationPairedBranchRelated embeddings) 2 (by omega)
  · exact embeddings.source_degree
  · exact embeddings.inverse_degree


end
end StatMech.FrontierD
