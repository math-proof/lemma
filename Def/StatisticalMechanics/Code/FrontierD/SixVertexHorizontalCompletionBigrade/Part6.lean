/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalCompletionBigrade.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexCheckerHorizontalBigrade
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPairBigrade.Part2
import Abbrev.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalCompletionBigrade.Part5
open Finset


namespace StatMech.FrontierD

noncomputable section

def sixVertexHorizontalSectorCompletionEquivColumns
    (T : EvenTorus) (sector : Fin (T.width + 1))
    (horizontal : SixVertexHorizontalField T) :
    SixVertexHorizontalSectorCompletion T sector horizontal ≃
      SixVertexColumnCompletionFamilyInSector
        T sector horizontal :=
  Equiv.subtypeEquiv
    (sixVertexVerticalCompletionEquivColumns T horizontal)
    fun completion => by
      rfl


def sixVertexColumnCompletionFamilyEquivSectorRow
    (T : EvenTorus) (sector : Fin (T.width + 1))
    (horizontal : SixVertexHorizontalField T) :
    SixVertexColumnCompletionFamilyInSector T sector horizontal ≃
      Sigma fun row : SixVertexSector T.width sector.val =>
        (i : Fin T.width) ->
          SixVertexVerticalColumnCompletionAtSeam T horizontal i
            (sixVertexSectorRow row i) where
  toFun columns := by
    let seamRow : SixVertexRow T.width :=
      fun i => (columns.1 i).1 (svFinLast T.height_pos)
    let row : SixVertexSector T.width sector.val :=
      svRowSectorAt seamRow columns.2
    refine ⟨row, fun i => ⟨columns.1 i, ?_⟩⟩
    change seamRow i = sixVertexSectorRow row i
    rw [svRowSectorAt_row]
  invFun data := by
    refine ⟨fun i => (data.2 i).1, ?_⟩
    have hrow :
        (fun i => ((data.2 i).1.1 (svFinLast T.height_pos))) =
          sixVertexSectorRow data.1 := by
      funext i
      exact (data.2 i).2
    rw [hrow, sixVertexSectorRow_upCount]
  left_inv columns := by
    apply Subtype.ext
    funext i
    apply Subtype.ext
    rfl
  right_inv data := by
    let seamRow : SixVertexRow T.width :=
      fun i => ((data.2 i).1.1 (svFinLast T.height_pos))
    have hcount : sixVertexUpCount seamRow = sector.val := by
      have hrow : seamRow = sixVertexSectorRow data.1 := by
        funext i
        exact (data.2 i).2
      rw [hrow, sixVertexSectorRow_upCount]
    let row : SixVertexSector T.width sector.val :=
      svRowSectorAt seamRow hcount
    have hrow : row = data.1 := by
      apply sixVertexSectorRow_injective
      rw [svRowSectorAt_row]
      funext i
      exact (data.2 i).2
    change (⟨row, _⟩ : Sigma fun row :
        SixVertexSector T.width sector.val =>
      (i : Fin T.width) ->
        SixVertexVerticalColumnCompletionAtSeam T horizontal i
          (sixVertexSectorRow row i)) = data
    apply Sigma.ext hrow
    let fiber := fun row : SixVertexSector T.width sector.val =>
      (i : Fin T.width) ->
        SixVertexVerticalColumnCompletionAtSeam T horizontal i
          (sixVertexSectorRow row i)
    have htype : fiber row = fiber data.1 := congrArg fiber hrow
    let lhs : fiber row := fun i =>
      ⟨(data.2 i).1, by
        rw [hrow]
        exact (data.2 i).2⟩
    have hcast : cast htype lhs = data.2 := by
      letI (i : Fin T.width) : Subsingleton
          (SixVertexVerticalColumnCompletionAtSeam T horizontal i
            (sixVertexSectorRow data.1 i)) :=
        sixVertexVerticalColumnCompletionAtSeam_subsingleton i _
      exact Subsingleton.elim _ _
    exact (cast_heq htype lhs).symm.trans (heq_of_eq hcast)


end
end StatMech.FrontierD
