/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedDualPrimalInteractionAlgebra.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedDualOpenWalkCarrier
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedOpenWalkCarrier
open scoped BigOperators


namespace StatMech.FrontierD

open StatMech.Onsager

noncomputable section

theorem fkRectIntegralSquareDartList_translate_comp
    (l : List FKRectIntegralSquareDart) (a b : Int × Int) :
    ((l.map (fkRectIntegralSquareDartTranslate a)).map
        (fkRectIntegralSquareDartTranslate b)) =
      l.map (fkRectIntegralSquareDartTranslate
        (a.1 + b.1, a.2 + b.2)) := by
  simp only [List.map_map]
  apply List.map_congr_left
  intro d hd
  simp only [Function.comp_apply]
  rw [fkRectIntegralSquareDartTranslate_comp]


end
end StatMech.FrontierD
