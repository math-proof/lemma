/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDiagonalShearSubdivision.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusSquareDevelopment.Part12
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Def.StatisticalMechanics.Code.FrontierD.FKRectDiagonalShearSubdivision.Part2
open SimpleGraph


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.Universality

noncomputable section

theorem FKRectSquareWalkLift.diagonalShearWalk_support_cases
    (R : FKRectTorus) {G : SimpleGraph R.Vertex}
    {x y : R.Vertex} {w : G.Walk x y} {p q : Int × Int}
    (h : FKRectSquareWalkLift R w p q) {z : Site 2}
    (hz : z ∈ (h.diagonalShearWalk R).support) :
    (∃ a ∈ w.support, ∃ u : Int × Int,
      fkRectLiftedVertex R u = a ∧
        z = fkRectDiagonalShearPoint (fkRectSquareDevelopPoint u)) ∨
    ∃ a b, s(a, b) ∈ w.edges ∧ ∃ u v : Int × Int,
      fkRectLiftedVertex R u = a ∧ fkRectLiftedVertex R v = b ∧
        z = fkRectDiagonalShearMidpoint
          (fkRectSquareDevelopPoint u) (fkRectSquareDevelopPoint v) :=
  Classical.choose_spec (h.exists_diagonalShearWalk R) z hz

end
end StatMech.FrontierD
