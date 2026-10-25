/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderPlanarization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCylinderExploration
import Theorem.StatisticalMechanics.Code.FrontierD.FKFreeConnectionBoxEmbedding
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusWindingEvent.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectFaithfulHorizontalExtension
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectFaithfulCarrierDisjoint
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectFaithfulShearCoordinates
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectFaithfulWalkVerticalBound
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusDisjointWinding.Part4
import Def.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCylinderPlanarization.Part5
open Finset SimpleGraph


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem fkRectHorizontalCylinderUnexploredLiftSite_mem_box
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex))
    (S : Finset (Fin R.width))
    (x : FKRectHorizontalCylinderUnexploredVertex R rho S) :
    fkRectHorizontalCylinderUnexploredLiftSite R rho S x ∈
      box 2 (fkRectHorizontalCylinderUnexploredLiftRadius R rho S) := by
  intro i
  have hmax : max
      ((fkRectHorizontalCylinderUnexploredLiftSite R rho S x 0).natAbs)
      ((fkRectHorizontalCylinderUnexploredLiftSite R rho S x 1).natAbs) ≤
      fkRectHorizontalCylinderUnexploredLiftRadius R rho S := by
    exact Finset.le_sup (s := Finset.univ) (f := fun y =>
      max ((fkRectHorizontalCylinderUnexploredLiftSite R rho S y 0).natAbs)
        ((fkRectHorizontalCylinderUnexploredLiftSite R rho S y 1).natAbs))
      (Finset.mem_univ x)
  fin_cases i
  · exact (le_max_left _ _).trans hmax
  · exact (le_max_right _ _).trans hmax


end
end StatMech.FrontierD
