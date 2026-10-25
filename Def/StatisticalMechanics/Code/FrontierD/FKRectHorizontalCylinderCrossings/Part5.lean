/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderCrossings.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCylinderLaw.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCylinderCrossings.Part4
open Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

def FKRectHorizontalCylinderDistinctPairedWitness
    (R : FKRectTorus) (pair : Fin R.width -> Fin R.width)
    (S : Finset (Fin R.width))
    (rho : ConfigSpace (Sym2 R.Vertex)) : Prop :=
  (∀ x ∈ S,
    (FK.openSub (fkRectHorizontalCylinderGraph R) rho).Reachable
      (x, fkRectBottomRow R) (pair x, fkRectTopRow R)) ∧
  (∀ x ∈ S, ∀ y ∈ S, x ≠ y ->
    ¬ (FK.openSub (fkRectHorizontalCylinderGraph R) rho).Reachable
      (x, fkRectBottomRow R) (y, fkRectBottomRow R))


end
end StatMech.FrontierD
