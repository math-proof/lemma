/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedDiagonalShearSubdivision.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDiagonalShearSubdivision.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusSquareCoverIntersection.Part7
import Def.StatisticalMechanics.Code.FrontierD.FKRectRefinedDiagonalShearSubdivision
open SimpleGraph


namespace StatMech.FrontierD

open StatMech.Lattice

noncomputable section

theorem FKRectIntegralSquareDartPath.diagonalShearWalk_support_cases
    {p q : Int × Int} {l : List FKRectIntegralSquareDart}
    (h : FKRectIntegralSquareDartPath p q l) {z : Site 2}
    (hz : z ∈ h.diagonalShearWalk.support) :
    z = fkRectDiagonalShearPoint p ∨
      ∃ d ∈ l,
        z = fkRectDiagonalShearMidpoint
            d.1 (fkRectIntegralSquareDartEnd d) ∨
          z = fkRectDiagonalShearPoint
            (fkRectIntegralSquareDartEnd d) :=
  Classical.choose_spec h.exists_diagonalShearWalk z hz

end
end StatMech.FrontierD
