/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderCrossings.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCylinderLaw.Part5
open Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

def fkRectBottomRow (R : FKRectTorus) : Fin R.height :=
  ⟨0, R.height_pos⟩


def fkRectTopRow (R : FKRectTorus) : Fin R.height :=
  ⟨R.height - 1, Nat.sub_lt R.height_pos Nat.zero_lt_one⟩


def FKRectHorizontalCylinderCrossingComponent
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex))
    (C : (FK.openSub (fkRectHorizontalCylinderGraph R) rho).ConnectedComponent) :
    Prop :=
  (∃ x : Fin R.width,
      (FK.openSub (fkRectHorizontalCylinderGraph R) rho).connectedComponentMk
        (x, fkRectBottomRow R) = C) ∧
    ∃ y : Fin R.width,
      (FK.openSub (fkRectHorizontalCylinderGraph R) rho).connectedComponentMk
        (y, fkRectTopRow R) = C


noncomputable def fkRectHorizontalCylinderCrossingClusterCount
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex)) : Nat := by
  classical
  exact Fintype.card
    {C // FKRectHorizontalCylinderCrossingComponent R rho C}


def FKRectHorizontalCutPrimalCrossingComponent
    (R : FKRectTorus) (eta : R.Configuration)
    (C : (fkRectOpenGraph R eta).ConnectedComponent) : Prop :=
  (∃ x : Fin R.width,
      (fkRectOpenGraph R eta).connectedComponentMk
        (x, fkRectBottomRow R) = C) ∧
    ∃ y : Fin R.width,
      (fkRectOpenGraph R eta).connectedComponentMk
        (y, fkRectTopRow R) = C


noncomputable def fkRectHorizontalCutPrimalCrossingClusterCount
    (R : FKRectTorus) (eta : R.Configuration) : Nat := by
  classical
  exact Fintype.card
    {C // FKRectHorizontalCutPrimalCrossingComponent R eta C}


end
end StatMech.FrontierD
