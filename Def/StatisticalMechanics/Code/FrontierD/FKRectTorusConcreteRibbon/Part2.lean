/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusConcreteRibbon.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusRibbonClassification
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectMedialClosedCycles.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusConcreteRibbon.Part2
open Equiv Finset


namespace StatMech.FrontierD

open StatMech.FrontierA

noncomputable section

variable {T : EvenTorus}


noncomputable def fkRectCellularRibbonDualData (R : FKRectTorus) :
    CellularRibbonDualData (fkRectRibbonSystem R) where
  primalVertexCount := Fintype.card R.Vertex
  dualVertexCount := fkRectTorusCellularFaceCount R
  genus := 1
  rotationCycles_eq_primalVertexCount := by
    change StatMech.FrontierA.permCycleCount
        (fkMedialBlackBoundaryPerm (fkRectClosedMedialPairing R)) = _
    rw [permCycleCount_fkMedialBlackBoundaryPerm]
    simpa [fkRectMedialLoopCount,
      fkRectConfigurationToMedialPairing_empty] using
      fkRectMedialLoopCount_empty R
  cellularEuler := fkRectTorus_cellularEuler_genus_one R


end
end StatMech.FrontierD
