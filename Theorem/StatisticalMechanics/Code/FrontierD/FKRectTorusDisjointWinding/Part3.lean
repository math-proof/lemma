/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusDisjointWinding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusSquareCoverIntersection.Part7
import Def.StatisticalMechanics.Code.FrontierD.FKRectTorusDisjointWinding.Part3
open SimpleGraph


namespace StatMech.FrontierD

open StatMech.Onsager

noncomputable section

theorem fkRectSquareCoverPointVertex_eq_of_pointMod
    (R : FKRectTorus) (z : Int × Int)
    (p : ZMod (fkRectSquareCoverSide R) ×
      ZMod (fkRectSquareCoverSide R))
    (h : fkRectIntegralSquarePointMod (fkRectSquareCoverSide R) z = p) :
    fkRectSquareRepresentativeVertex R z =
      fkRectSquareCoverPointVertex R p := by
  apply fkRectSquareRepresentativeVertex_eq_of_pointMod_eq R
  rw [h]
  apply Prod.ext <;>
    simp [fkRectIntegralSquarePointMod]


end
end StatMech.FrontierD
