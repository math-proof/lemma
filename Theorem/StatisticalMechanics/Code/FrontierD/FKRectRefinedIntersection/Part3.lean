/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedIntersection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedInteractionCore.Part4
import Def.StatisticalMechanics.Code.FrontierD.FKRectRefinedIntersection.Part2
open scoped BigOperators
open Finset


namespace StatMech.FrontierD

open StatMech.Onsager

open IntegralSquareTorusCycle

noncomputable section

variable {L : Nat} [Fact (8 < L)]

theorem fkRectRefinedScaleDart_path (d : FKRectIntegralSquareDart) :
    FKRectIntegralSquareDartPath
      (fkRectRefinedScalePoint d.1)
      (fkRectRefinedScalePoint (fkRectIntegralSquareDartEnd d))
      (fkRectRefinedScaleDart d) := by
  rcases d with ⟨⟨x, y⟩, mu⟩
  fin_cases mu
  · convert fkRectRefinedFourEast_path
      (fkRectRefinedScalePoint (x, y)) using 1 <;>
      simp [fkRectRefinedScalePoint, fkRectIntegralSquareDartEnd,
        StatMech.Onsager.ons_dirExponentX,
        StatMech.Onsager.ons_dirExponentY] <;> ring
  · convert fkRectRefinedFourNorth_path_public
      (fkRectRefinedScalePoint (x, y)) using 1 <;>
      simp [fkRectRefinedScalePoint, fkRectIntegralSquareDartEnd,
        StatMech.Onsager.ons_dirExponentX,
        StatMech.Onsager.ons_dirExponentY] <;> ring
  · convert fkRectRefinedFourWest_path_public
      (fkRectRefinedScalePoint (x, y)) using 1 <;>
      simp [fkRectRefinedScalePoint, fkRectIntegralSquareDartEnd,
        StatMech.Onsager.ons_dirExponentX,
        StatMech.Onsager.ons_dirExponentY] <;> ring
  · convert fkRectRefinedFourSouth_path
      (fkRectRefinedScalePoint (x, y)) using 1 <;>
      simp [fkRectRefinedScalePoint, fkRectIntegralSquareDartEnd,
        StatMech.Onsager.ons_dirExponentX,
        StatMech.Onsager.ons_dirExponentY] <;> ring


end
end StatMech.FrontierD
