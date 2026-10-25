/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectSeamForcing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectNoLoopNormalization
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectSeamForcing.Part3
open Finset


namespace StatMech.FrontierD

noncomputable section

def fkRectLeftColumn (R : FKRectTorus) : Fin R.width :=
  ⟨0, R.width_pos⟩


def fkRectRightColumn (R : FKRectTorus) : Fin R.width :=
  ⟨R.width - 1, Nat.sub_lt R.width_pos Nat.zero_lt_one⟩


def FKRectCutHorizontalCrossingSource
    (R : FKRectTorus) (omega : R.Configuration) (y : Fin R.height) : Prop :=
  ∃ z : Fin R.height,
    (fkRectOpenGraph R (fkRectForceCutClosed R omega)).Reachable
      (fkRectLeftColumn R, y) (fkRectRightColumn R, z)


def FKRectCutHorizontalCrossingComponent
    (R : FKRectTorus) (omega : R.Configuration)
    (C : (fkRectOpenGraph R
      (fkRectForceCutClosed R omega)).ConnectedComponent) : Prop :=
  (∃ y : Fin R.height,
      (fkRectOpenGraph R
        (fkRectForceCutClosed R omega)).connectedComponentMk
          (fkRectLeftColumn R, y) = C) ∧
    ∃ z : Fin R.height,
      (fkRectOpenGraph R
        (fkRectForceCutClosed R omega)).connectedComponentMk
          (fkRectRightColumn R, z) = C


noncomputable def fkRectCutHorizontalCrossingClusterCount
    (R : FKRectTorus) (omega : R.Configuration) : Nat := by
  classical
  exact Fintype.card {C // FKRectCutHorizontalCrossingComponent R omega C}


noncomputable def fkRectCutHorizontalCrossingSourceCount
    (R : FKRectTorus) (omega : R.Configuration) : Nat := by
  classical
  exact (Finset.univ.filter fun y : Fin R.height =>
    FKRectCutHorizontalCrossingSource R omega y).card

end
end StatMech.FrontierD
