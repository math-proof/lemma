/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDiagonalShearSubdivision.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusSquareDevelopment.Part12
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDiagonalShearSubdivision
open SimpleGraph


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.Universality

noncomputable section

noncomputable def FKRectSquareWalkLift.diagonalShearWalk
    (R : FKRectTorus) {G : SimpleGraph R.Vertex}
    {x y : R.Vertex} {w : G.Walk x y} {p q : Int × Int}
    (h : FKRectSquareWalkLift R w p q) :
    (hypercubicLattice 2).Walk
      (fkRectDiagonalShearPoint (fkRectSquareDevelopPoint p))
      (fkRectDiagonalShearPoint (fkRectSquareDevelopPoint q)) :=
  Classical.choose (h.exists_diagonalShearWalk R)


end
end StatMech.FrontierD
