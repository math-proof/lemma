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
import Instance.StatisticalMechanics.Code.FrontierD.FKRectBoundaryConnectivityTransfer.Part2
open Finset Matrix Filter Topology


namespace StatMech.FrontierD

noncomputable section

attribute [local instance] Classical.propDecidable


def fkRectConfigurationLayer (R : FKRectTorus) (omega : R.Configuration)
    (y : Fin R.height) : Bool × Fin R.width -> Bool :=
  fun a => omega (a.1, (a.2, y))


def fkRectConfigurationLayersEquiv (R : FKRectTorus) :
    R.Configuration ≃ (Fin R.height -> Bool × Fin R.width -> Bool) where
  toFun omega y a := omega (a.1, (a.2, y))
  invFun layers a := layers a.2.2 (a.1, a.2.1)
  left_inv omega := by
    funext a
    rfl
  right_inv layers := by
    funext y a
    rfl

end
end StatMech.FrontierD
