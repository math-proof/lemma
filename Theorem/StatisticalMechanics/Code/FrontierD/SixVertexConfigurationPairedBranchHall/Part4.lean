/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexConfigurationPairedBranchHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPairBigrade.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairDecoratedHall.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPairedBranchHall.Part5
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem configurationPairedBranchConstructions_of_nonempty_sources
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    (hconstruction : forall grade,
      Nonempty (SixVertexConfigurationPairBigradeFiber T
        (sixVertexConfigurationLowerSector middle hmiddle_pos)
        (sixVertexConfigurationUpperSector middle hmiddle_lt) grade) ->
      Nonempty
        (SixVertexConfigurationPairedBranchGeometricConstruction T middle
          hmiddle_pos hmiddle_lt grade)) :
    SixVertexConfigurationPairedBranchConstructions T middle
      hmiddle_pos hmiddle_lt := by
  intro grade
  cases isEmpty_or_nonempty (SixVertexConfigurationPairBigradeFiber T
      (sixVertexConfigurationLowerSector middle hmiddle_pos)
      (sixVertexConfigurationUpperSector middle hmiddle_lt) grade) with
  | inl hempty =>
      exact ⟨sixVertexConfigurationPairedBranchConstructionOfIsEmpty
        hempty⟩
  | inr hnonempty => exact hconstruction grade hnonempty

theorem configurationBigradeFibers_of_pairedBranchConstructions
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    (hconstruction : SixVertexConfigurationPairedBranchConstructions
      T middle hmiddle_pos hmiddle_lt) :
    SixVertexConfigurationPairBigradeFiberDominates T
      (sixVertexConfigurationLowerSector middle hmiddle_pos)
      (sixVertexConfigurationUpperSector middle hmiddle_lt) middle middle := by
  intro grade
  obtain ⟨geometric⟩ := hconstruction grade
  let embeddings := geometric.toEmbeddings
  let sources : Finset (SixVertexConfigurationPairBigradeFiber T
      (sixVertexConfigurationLowerSector middle hmiddle_pos)
      (sixVertexConfigurationUpperSector middle hmiddle_lt) grade) := Finset.univ
  have hHall := embeddings.hall sources
  calc
    Fintype.card (SixVertexConfigurationPairBigradeFiber T
        (sixVertexConfigurationLowerSector middle hmiddle_pos)
        (sixVertexConfigurationUpperSector middle hmiddle_lt) grade) =
        sources.card := by simp [sources]
    _ <= (Finset.univ.filter fun target => exists source,
          source ∈ sources ∧
            SixVertexConfigurationPairedBranchRelated
              embeddings source target).card := hHall
    _ <= Fintype.card
        (SixVertexConfigurationPairBigradeFiber T middle middle grade) := by
      simpa only [Finset.card_univ] using Finset.card_le_univ
        (Finset.univ.filter fun target => exists source,
          source ∈ sources ∧
            SixVertexConfigurationPairedBranchRelated
              embeddings source target)

theorem sixVertexMarkedTraceCoefficientwiseLogConcave_of_configurationPairedBranches
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (hconstruction : SixVertexConfigurationPairedBranchConstructions
      T middle hmiddle_pos hmiddle_lt) :
    SixVertexMarkedTraceCoefficientwiseLogConcave
      T.width T.height middle.val := by
  apply sixVertexMarkedTraceCoefficientwiseLogConcave_of_configurationBigradeFibers
    T middle hmiddle_pos hmiddle_lt
  exact configurationBigradeFibers_of_pairedBranchConstructions hconstruction

theorem sixVertexSectorTrace_logConcave_of_configurationPairedBranches
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    {c : Real} (hc : 2 <= c)
    (hconstruction : SixVertexConfigurationPairedBranchConstructions
      T middle hmiddle_pos hmiddle_lt) :
    Matrix.trace
          (sixVertexSectorTransfer T.width (middle.val - 1) c ^ T.height) *
        Matrix.trace
          (sixVertexSectorTransfer T.width (middle.val + 1) c ^ T.height) <=
      Matrix.trace
          (sixVertexSectorTransfer T.width middle.val c ^ T.height) ^ 2 :=
  sixVertexSectorTrace_logConcave_of_markedCoefficientwise
    T.width T.height middle.val hc
      (sixVertexMarkedTraceCoefficientwiseLogConcave_of_configurationPairedBranches
        T middle hmiddle_pos hmiddle_lt hconstruction)

end
end StatMech.FrontierD
