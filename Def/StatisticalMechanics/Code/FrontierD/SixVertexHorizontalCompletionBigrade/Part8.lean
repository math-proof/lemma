/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalCompletionBigrade.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexCheckerHorizontalBigrade
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPairBigrade.Part2
import Abbrev.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalCompletionBigrade.Part6
open Finset


namespace StatMech.FrontierD

noncomputable section

noncomputable def sixVertexHorizontalSectorCompletionEquivAdmissibleSeamRow
    (T : EvenTorus) (sector : Fin (T.width + 1))
    (horizontal : SixVertexHorizontalField T) :
    SixVertexHorizontalSectorCompletion T sector horizontal ≃
      SixVertexHorizontalAdmissibleSeamRow T sector horizontal := by
  letI (row : SixVertexSector T.width sector.val)
      (i : Fin T.width) :
      Subsingleton
        (SixVertexVerticalColumnCompletionAtSeam T horizontal i
          (sixVertexSectorRow row i)) :=
    sixVertexVerticalColumnCompletionAtSeam_subsingleton i _
  exact (sixVertexHorizontalSectorCompletionEquivColumns
      T sector horizontal).trans
    ((sixVertexColumnCompletionFamilyEquivSectorRow
      T sector horizontal).trans
      (sigmaSubsingletonEquivSubtypeNonempty fun row =>
        (i : Fin T.width) ->
          SixVertexVerticalColumnCompletionAtSeam T horizontal i
            (sixVertexSectorRow row i)))


def sixVertexHorizontalColumnSeamAllowed
    {T : EvenTorus} (horizontal : SixVertexHorizontalField T)
    (i : Fin T.width) (seam : Bool) : Prop :=
  Nonempty
    (SixVertexVerticalColumnCompletionAtSeam T horizontal i seam)


def sixVertexHorizontalTrueAllowedColumns
    {T : EvenTorus} (horizontal : SixVertexHorizontalField T) :
    Finset (Fin T.width) :=
  Finset.univ.filter fun i =>
    sixVertexHorizontalColumnSeamAllowed horizontal i true


def sixVertexHorizontalForcedTrueColumns
    {T : EvenTorus} (horizontal : SixVertexHorizontalField T) :
    Finset (Fin T.width) :=
  (sixVertexHorizontalTrueAllowedColumns horizontal).filter fun i =>
    Not (sixVertexHorizontalColumnSeamAllowed horizontal i false)

end
end StatMech.FrontierD
