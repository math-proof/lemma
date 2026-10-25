/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalDualCrossings.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusDualEdges.Part3
open Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

def FKRectRawHorizontalCrossingComponent
    (R : FKRectTorus) (eta : R.Configuration)
    (C : (fkRectOpenGraph R eta).ConnectedComponent) : Prop :=
  (∃ y : Fin R.height,
      (fkRectOpenGraph R eta).connectedComponentMk
        (fkRectLeftColumn R, y) = C) ∧
    ∃ z : Fin R.height,
      (fkRectOpenGraph R eta).connectedComponentMk
        (fkRectRightColumn R, z) = C


noncomputable def fkRectRawHorizontalCrossingClusterCount
    (R : FKRectTorus) (eta : R.Configuration) : Nat := by
  classical
  exact Fintype.card
    {C // FKRectRawHorizontalCrossingComponent R eta C}


def FKRectRawHorizontalCrossingSource
    (R : FKRectTorus) (eta : R.Configuration) (y : Fin R.height) : Prop :=
  ∃ z : Fin R.height,
    (fkRectOpenGraph R eta).Reachable
      (fkRectLeftColumn R, y) (fkRectRightColumn R, z)

noncomputable def fkRectRawHorizontalCrossingSourceCount
    (R : FKRectTorus) (eta : R.Configuration) : Nat := by
  classical
  exact (Finset.univ.filter fun y : Fin R.height =>
    FKRectRawHorizontalCrossingSource R eta y).card

end
end StatMech.FrontierD
