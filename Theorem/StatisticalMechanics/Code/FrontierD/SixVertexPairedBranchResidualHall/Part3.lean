/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairedBranchResidualHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalOffDiagonalTwoCycleMatching
import Def.StatisticalMechanics.Code.FrontierD.SixVertexPairedBranchResidualHall.Part4
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem pairedBranchResidualAtlases_of_constructions
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    (hconstruction : SixVertexHorizontalPairedBranchResidualConstructions
      T middle hmiddle_pos hmiddle_lt) :
    SixVertexHorizontalPairedBranchResidualAtlases T middle
      hmiddle_pos hmiddle_lt := by
  intro grade
  obtain ⟨construction⟩ := hconstruction grade
  exact ⟨construction.toAtlas⟩


theorem offDiagonalTwoCycleMatching_of_pairedBranchConstructions_direct
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    (hconstruction : SixVertexHorizontalPairedBranchResidualConstructions
      T middle hmiddle_pos hmiddle_lt) :
    SixVertexHorizontalOffDiagonalTwoCycleMatching T middle
      hmiddle_pos hmiddle_lt := by
  intro grade
  obtain ⟨construction⟩ := hconstruction grade
  exact ⟨fun source => construction.target source false,
    construction.branch_injective false,
    fun source => construction.supported source false⟩


theorem pairedBranchResidualConstructions_of_nonempty_sources
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    (hconstruction : forall grade : Nat × Nat,
      Nonempty
        (SixVertexHorizontalActualDeficitTokens T grade
          (sixVertexHorizontalLowerSector middle hmiddle_pos)
          (sixVertexHorizontalUpperSector middle hmiddle_lt) middle middle) ->
      Nonempty
        (SixVertexHorizontalPairedBranchResidualConstruction T middle
          hmiddle_pos hmiddle_lt grade)) :
    SixVertexHorizontalPairedBranchResidualConstructions T middle
      hmiddle_pos hmiddle_lt := by
  intro grade
  cases isEmpty_or_nonempty
      (SixVertexHorizontalActualDeficitTokens T grade
        (sixVertexHorizontalLowerSector middle hmiddle_pos)
        (sixVertexHorizontalUpperSector middle hmiddle_lt) middle middle) with
  | inl hempty =>
      exact ⟨sixVertexHorizontalPairedBranchResidualConstructionOfIsEmpty
        hempty⟩
  | inr hnonempty => exact hconstruction grade hnonempty


theorem offDiagonalTwoCycleMatching_of_pairedBranchAtlases
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    (hatlas : SixVertexHorizontalPairedBranchResidualAtlases T middle
      hmiddle_pos hmiddle_lt) :
    SixVertexHorizontalOffDiagonalTwoCycleMatching T middle
      hmiddle_pos hmiddle_lt := by
  intro grade
  obtain ⟨atlas⟩ := hatlas grade
  have hmatching :=
    (Fintype.all_card_le_filter_rel_iff_exists_injective
      (SixVertexHorizontalPairedBranchResidualRelated atlas)).mp atlas.hall
  obtain ⟨matching, hinjective, hrelated⟩ := hmatching
  refine ⟨matching, hinjective, ?_⟩
  intro source
  obtain ⟨branch, htarget⟩ := hrelated source
  rw [← htarget]
  exact atlas.supported source branch

theorem sixVertexMarkedTraceCoefficientwiseLogConcave_of_pairedBranchAtlases
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (hatlas : SixVertexHorizontalPairedBranchResidualAtlases T middle
      hmiddle_pos hmiddle_lt) :
    SixVertexMarkedTraceCoefficientwiseLogConcave
      T.width T.height middle.val :=
  sixVertexMarkedTraceCoefficientwiseLogConcave_of_offDiagonalTwoCycleMatching
    T middle hmiddle_pos hmiddle_lt
      (offDiagonalTwoCycleMatching_of_pairedBranchAtlases hatlas)

theorem sixVertexSectorTrace_logConcave_of_pairedBranchAtlases
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    {c : Real} (hc : 2 <= c)
    (hatlas : SixVertexHorizontalPairedBranchResidualAtlases T middle
      hmiddle_pos hmiddle_lt) :
    Matrix.trace
          (sixVertexSectorTransfer T.width (middle.val - 1) c ^ T.height) *
        Matrix.trace
          (sixVertexSectorTransfer T.width (middle.val + 1) c ^ T.height) <=
      Matrix.trace
          (sixVertexSectorTransfer T.width middle.val c ^ T.height) ^ 2 :=
  sixVertexSectorTrace_logConcave_of_offDiagonalTwoCycleMatching
    T middle hmiddle_pos hmiddle_lt hc
      (offDiagonalTwoCycleMatching_of_pairedBranchAtlases hatlas)

theorem sixVertexMarkedTraceCoefficientwiseLogConcave_of_pairedBranchConstructions
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (hconstruction : SixVertexHorizontalPairedBranchResidualConstructions
      T middle hmiddle_pos hmiddle_lt) :
    SixVertexMarkedTraceCoefficientwiseLogConcave
      T.width T.height middle.val :=
  sixVertexMarkedTraceCoefficientwiseLogConcave_of_offDiagonalTwoCycleMatching
    T middle hmiddle_pos hmiddle_lt
      (offDiagonalTwoCycleMatching_of_pairedBranchConstructions_direct
        hconstruction)

theorem sixVertexSectorTrace_logConcave_of_pairedBranchConstructions
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    {c : Real} (hc : 2 <= c)
    (hconstruction : SixVertexHorizontalPairedBranchResidualConstructions
      T middle hmiddle_pos hmiddle_lt) :
    Matrix.trace
          (sixVertexSectorTransfer T.width (middle.val - 1) c ^ T.height) *
        Matrix.trace
          (sixVertexSectorTransfer T.width (middle.val + 1) c ^ T.height) <=
      Matrix.trace
          (sixVertexSectorTransfer T.width middle.val c ^ T.height) ^ 2 :=
  sixVertexSectorTrace_logConcave_of_offDiagonalTwoCycleMatching
    T middle hmiddle_pos hmiddle_lt hc
      (offDiagonalTwoCycleMatching_of_pairedBranchConstructions_direct
        hconstruction)

end
end StatMech.FrontierD
