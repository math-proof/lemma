/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderCrossings.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCylinderLaw.Part5
import Def.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCylinderCrossings.Part2
open Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

theorem fkRectHorizontalCylinderCrossingRepresentative_component
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex))
    (C : {C :
      (FK.openSub (fkRectHorizontalCylinderGraph R) rho).ConnectedComponent //
        FKRectHorizontalCylinderCrossingComponent R rho C}) :
    (FK.openSub (fkRectHorizontalCylinderGraph R) rho).connectedComponentMk
        (fkRectHorizontalCylinderCrossingRepresentative R rho C,
          fkRectBottomRow R) = C.1 :=
  Classical.choose_spec C.2.1

theorem fkRectHorizontalCylinderCrossingRepresentative_source
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex))
    (C : {C :
      (FK.openSub (fkRectHorizontalCylinderGraph R) rho).ConnectedComponent //
        FKRectHorizontalCylinderCrossingComponent R rho C}) :
    FKRectHorizontalCylinderCrossingSource R rho
      (fkRectHorizontalCylinderCrossingRepresentative R rho C) := by
  rcases C.2.2 with ⟨y, hy⟩
  refine ⟨y, SimpleGraph.ConnectedComponent.exact ?_⟩
  exact (fkRectHorizontalCylinderCrossingRepresentative_component
    R rho C).trans hy.symm

theorem fkRectHorizontalCylinderCrossingRepresentative_injective
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex)) :
    Function.Injective
      (fkRectHorizontalCylinderCrossingRepresentative R rho) := by
  intro C D hCD
  apply Subtype.ext
  exact (fkRectHorizontalCylinderCrossingRepresentative_component
    R rho C).symm.trans
      ((congrArg
        (fun x =>
          (FK.openSub (fkRectHorizontalCylinderGraph R) rho).connectedComponentMk
            (x, fkRectBottomRow R)) hCD).trans
        (fkRectHorizontalCylinderCrossingRepresentative_component R rho D))


end
end StatMech.FrontierD
