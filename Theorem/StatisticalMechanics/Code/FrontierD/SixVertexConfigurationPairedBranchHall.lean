/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexConfigurationPairedBranchHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPairBigrade.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairDecoratedHall.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPairedBranchHall.Part2
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem SixVertexConfigurationPairedBranchEmbeddings.source_degree
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (embeddings : SixVertexConfigurationPairedBranchEmbeddings T middle
      hmiddle_pos hmiddle_lt grade)
    (source : SixVertexConfigurationPairBigradeFiber T
      (sixVertexConfigurationLowerSector middle hmiddle_pos)
      (sixVertexConfigurationUpperSector middle hmiddle_lt) grade) :
    2 <= (Finset.univ.filter
      (SixVertexConfigurationPairedBranchRelated embeddings source)).card := by
  have hcard := Fintype.card_le_of_embedding
    (embeddings.sourceCertificates source)
  simpa [Fintype.card_subtype] using hcard

end
end StatMech.FrontierD
