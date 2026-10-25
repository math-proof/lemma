/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialPrimalLabel.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialToggleCount
import Def.StatisticalMechanics.Code.FrontierD.FKRectMedialPrimalLabel


namespace StatMech.FrontierD

theorem fkRectTorusIndexedEdge_eq_medialPrimals
    (R : FKRectTorus) (e : R.EdgeIndex) :
    fkRectTorusIndexedEdge R e =
      s(fkRectMedialWestPrimal R e, fkRectMedialEastPrimal R e) := by
  rcases e with ⟨b, x, y⟩
  cases b <;> by_cases hy : Even y.val <;>
    simp [fkRectTorusIndexedEdge, fkRectMedialWestPrimal,
      fkRectMedialEastPrimal, hy, Sym2.eq_swap]


end StatMech.FrontierD
