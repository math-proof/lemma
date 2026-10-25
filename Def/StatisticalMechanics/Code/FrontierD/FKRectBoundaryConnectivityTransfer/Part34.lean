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
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryConnectivityTransfer.Part31
open Finset Matrix Filter Topology


namespace StatMech.FrontierD

noncomputable section

attribute [local instance] Classical.propDecidable


def fkRectConfigurationScheduleEquiv (R : FKRectTorus) :
    R.Configuration ≃
      (Bool × Fin R.width -> Bool) ×
        (Fin (R.height - 1) -> Bool × Fin R.width -> Bool) :=
  (fkRectConfigurationLayersEquiv R).trans
    ((Equiv.arrowCongr (finCongr (Nat.sub_add_cancel
        (Nat.one_le_iff_ne_zero.mpr R.height_pos.ne'))).symm
      (Equiv.refl _)).trans
    ((Equiv.arrowCongr (finSuccEquiv (R.height - 1))
      (Equiv.refl _)).trans Equiv.piOptionEquivProd))

end
end StatMech.FrontierD
