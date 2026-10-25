/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusRandomCluster.Part5
import Theorem.StatisticalMechanics.Code.Foundations.FiniteNonnegativeMatrixRate.Part2
import Theorem.StatisticalMechanics.Code.Lattice.EulerFaces2.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryConnectivityTransfer.Part16
open Finset Matrix Filter Topology


namespace StatMech.FrontierD

noncomputable section

attribute [local instance] Classical.propDecidable


def fkRectBoundarySeamRow (R : FKRectTorus) : Fin R.height :=
  ⟨0, R.height_pos⟩


def fkRectBoundaryNonSeamRow (R : FKRectTorus)
    (i : Fin (R.height - 1)) : Fin R.height :=
  finCongr (Nat.sub_add_cancel
    (Nat.one_le_iff_ne_zero.mpr R.height_pos.ne')) i.succ

end
end StatMech.FrontierD
