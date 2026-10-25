/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairedBranchResidualHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalOffDiagonalTwoCycleMatching
import Def.StatisticalMechanics.Code.FrontierD.SixVertexPairedBranchResidualHall.Part3
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem SixVertexHorizontalPairedBranchResidualAtlas.source_degree
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (atlas : SixVertexHorizontalPairedBranchResidualAtlas T middle
      hmiddle_pos hmiddle_lt grade)
    (source : SixVertexHorizontalActualDeficitTokens T grade
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt) middle middle) :
    2 <= (Finset.univ.filter
      (SixVertexHorizontalPairedBranchResidualRelated atlas source)).card := by
  have hcard := Fintype.card_le_of_embedding
    (atlas.sourceCertificates source)
  simpa [Fintype.card_subtype] using hcard

theorem SixVertexHorizontalPairedBranchResidualAtlas.source_nonempty
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (atlas : SixVertexHorizontalPairedBranchResidualAtlas T middle
      hmiddle_pos hmiddle_lt grade)
    (source : SixVertexHorizontalActualDeficitTokens T grade
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt) middle middle) :
    (Finset.univ.filter
      (SixVertexHorizontalPairedBranchResidualRelated atlas source)).Nonempty := by
  apply Finset.card_pos.mp
  have hdegree := atlas.source_degree source
  omega

theorem SixVertexHorizontalPairedBranchResidualAtlas.inverse_degree
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (atlas : SixVertexHorizontalPairedBranchResidualAtlas T middle
      hmiddle_pos hmiddle_lt grade)
    (target : SixVertexHorizontalActualSurplusTokens T grade
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt) middle middle) :
    (Finset.univ.filter fun source =>
      SixVertexHorizontalPairedBranchResidualRelated atlas source target).card <=
        2 := by
  have hcard := Fintype.card_le_of_embedding (atlas.inverseCode target)
  simpa [SixVertexHorizontalPairedBranchResidualRelated,
    Fintype.card_subtype] using hcard


theorem SixVertexHorizontalPairedBranchResidualAtlas.hall
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (atlas : SixVertexHorizontalPairedBranchResidualAtlas T middle
      hmiddle_pos hmiddle_lt grade) :
    forall sources : Finset
      (SixVertexHorizontalActualDeficitTokens T grade
        (sixVertexHorizontalLowerSector middle hmiddle_pos)
        (sixVertexHorizontalUpperSector middle hmiddle_lt) middle middle),
      sources.card <=
        (Finset.univ.filter fun target => exists source,
          source ∈ sources ∧
            SixVertexHorizontalPairedBranchResidualRelated
              atlas source target).card := by
  apply finiteRelationHall_of_bidegree
    (SixVertexHorizontalPairedBranchResidualRelated atlas) 2 (by omega)
  · exact atlas.source_degree
  · exact atlas.inverse_degree


end
end StatMech.FrontierD
