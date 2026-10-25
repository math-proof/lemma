/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusConcreteRibbon.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusRibbonClassification
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectMedialClosedCycles.Part2
import Def.StatisticalMechanics.Code.FrontierD.FKRectTorusConcreteRibbon.Part2
open Equiv Finset


namespace StatMech.FrontierD

open StatMech.FrontierA

noncomputable section

variable {T : EvenTorus}


theorem fkRectEulerHomologyDefect_classified_of_concreteRibbon
    (R : FKRectTorus) (F : Finset R.EdgeIndex) :
    fkRectEulerHomologyDefect R (fkRectConfigurationOfEdges R F) = 0 ∨
      fkRectEulerHomologyDefect R (fkRectConfigurationOfEdges R F) = 2 := by
  apply fkRectEulerHomologyDefect_classified_of_ribbonBoundary
    R (fkRectRibbonSystem R) (fkRectCellularRibbonDualData R)
  · rfl
  · rfl
  · exact fkRectRibbonSystem_boundaryComponents R
  · rw [fkRectRibbonSystem_boundaryComponents,
      fkRectMedialLoopCount_univ]
    rfl

end
end StatMech.FrontierD
