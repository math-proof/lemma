/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalCompletionBigrade.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexCheckerHorizontalBigrade
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPairBigrade.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalCompletionBigrade.Part8
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexHorizontalForcedTrueColumns_subset_trueAllowed
    {T : EvenTorus} (horizontal : SixVertexHorizontalField T) :
    sixVertexHorizontalForcedTrueColumns horizontal ⊆
      sixVertexHorizontalTrueAllowedColumns horizontal :=
  Finset.filter_subset _ _


theorem sixVertexHorizontalColumnSeamAllowed_false_or_true
    {T : EvenTorus} {horizontal : SixVertexHorizontalField T}
    (completion : SixVertexVerticalCompletion T horizontal)
    (i : Fin T.width) :
    sixVertexHorizontalColumnSeamAllowed horizontal i false \/
      sixVertexHorizontalColumnSeamAllowed horizontal i true := by
  let column := sixVertexVerticalCompletionToColumns completion i
  cases hseam : column.1 (svFinLast T.height_pos)
  · left
    exact ⟨⟨column, hseam⟩⟩
  · right
    exact ⟨⟨column, hseam⟩⟩


theorem sixVertexHorizontalAdmissibleSeamRow_iff_subset
    {T : EvenTorus} {horizontal : SixVertexHorizontalField T}
    (completion : SixVertexVerticalCompletion T horizontal)
    (sector : Fin (T.width + 1))
    (row : SixVertexSector T.width sector.val) :
    Nonempty ((i : Fin T.width) ->
        SixVertexVerticalColumnCompletionAtSeam T horizontal i
          (sixVertexSectorRow row i)) <->
      sixVertexHorizontalForcedTrueColumns horizontal ⊆ row.1 /\
        row.1 ⊆ sixVertexHorizontalTrueAllowedColumns horizontal := by
  constructor
  · rintro ⟨columns⟩
    constructor
    · intro i hi
      have hiData := Finset.mem_filter.mp hi
      by_contra hiRow
      have hfalse : sixVertexSectorRow row i = false := by
        simp [sixVertexSectorRow, hiRow]
      have hallowed :
          sixVertexHorizontalColumnSeamAllowed horizontal i false := by
        rw [<- hfalse]
        exact ⟨columns i⟩
      exact hiData.2 hallowed
    · intro i hiRow
      have htrue : sixVertexSectorRow row i = true := by
        simp [sixVertexSectorRow, hiRow]
      have hallowed :
          sixVertexHorizontalColumnSeamAllowed horizontal i true := by
        rw [<- htrue]
        exact ⟨columns i⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hallowed⟩
  · rintro ⟨hforced, htrue⟩
    refine ⟨fun i => ?_⟩
    by_cases hiRow : i ∈ row.1
    · have hiTrue : i ∈ sixVertexHorizontalTrueAllowedColumns horizontal :=
        htrue hiRow
      have hallowed :
          sixVertexHorizontalColumnSeamAllowed horizontal i true :=
        (Finset.mem_filter.mp hiTrue).2
      have hbit : sixVertexSectorRow row i = true := by
        simp [sixVertexSectorRow, hiRow]
      rw [hbit]
      exact Classical.choice hallowed
    · have hallowed :
          sixVertexHorizontalColumnSeamAllowed horizontal i false := by
        rcases sixVertexHorizontalColumnSeamAllowed_false_or_true
            completion i with hfalse | htrueAllowed
        · exact hfalse
        · by_contra hfalse
          have hiTrue :
              i ∈ sixVertexHorizontalTrueAllowedColumns horizontal :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, htrueAllowed⟩
          have hiForced :
              i ∈ sixVertexHorizontalForcedTrueColumns horizontal :=
            Finset.mem_filter.mpr ⟨hiTrue, hfalse⟩
          exact hiRow (hforced hiForced)
      have hbit : sixVertexSectorRow row i = false := by
        simp [sixVertexSectorRow, hiRow]
      rw [hbit]
      exact Classical.choice hallowed


end
end StatMech.FrontierD
