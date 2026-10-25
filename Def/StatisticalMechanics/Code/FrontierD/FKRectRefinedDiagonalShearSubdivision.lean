/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedDiagonalShearSubdivision.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDiagonalShearSubdivision.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusSquareCoverIntersection.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedDiagonalShearSubdivision
open SimpleGraph


namespace StatMech.FrontierD

open StatMech.Lattice

noncomputable section

noncomputable def FKRectIntegralSquareDartPath.diagonalShearWalk
    {p q : Int × Int} {l : List FKRectIntegralSquareDart}
    (h : FKRectIntegralSquareDartPath p q l) :
    (hypercubicLattice 2).Walk
      (fkRectDiagonalShearPoint p) (fkRectDiagonalShearPoint q) :=
  Classical.choose h.exists_diagonalShearWalk


end
end StatMech.FrontierD
