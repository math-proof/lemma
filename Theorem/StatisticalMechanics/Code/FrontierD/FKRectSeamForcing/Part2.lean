/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectSeamForcing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectNoLoopNormalization
import Def.StatisticalMechanics.Code.FrontierD.FKRectSeamForcing.Part2
open Finset


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem fkRectForceCutClosed_of_mem
    (R : FKRectTorus) (omega : R.Configuration) (a : R.EdgeIndex)
    (ha : a ∈ fkRectTorusCutEdges R) :
    fkRectForceCutClosed R omega a = false := by
  simp [fkRectForceCutClosed, ha]

@[simp] theorem fkRectForceCutClosed_of_not_mem
    (R : FKRectTorus) (omega : R.Configuration) (a : R.EdgeIndex)
    (ha : a ∉ fkRectTorusCutEdges R) :
    fkRectForceCutClosed R omega a = omega a := by
  simp [fkRectForceCutClosed, ha]

@[simp] theorem fkRectForceCutClosed_idem
    (R : FKRectTorus) (omega : R.Configuration) :
    fkRectForceCutClosed R (fkRectForceCutClosed R omega) =
      fkRectForceCutClosed R omega := by
  funext a
  by_cases ha : a ∈ fkRectTorusCutEdges R <;>
    simp [fkRectForceCutClosed, ha]


end
end StatMech.FrontierD
