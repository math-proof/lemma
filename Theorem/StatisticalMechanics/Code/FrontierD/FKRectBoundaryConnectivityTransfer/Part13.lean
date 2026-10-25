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
import Def.StatisticalMechanics.Code.FrontierD.FKRectBoundaryConnectivityTransfer.Part15
open Finset Matrix Filter Topology


namespace StatMech.FrontierD

noncomputable section

attribute [local instance] Classical.propDecidable


@[simp] theorem fkRectStripBoundary_false {W : Nat} (n : Nat) (x : Fin W) :
    fkRectStripBoundary n (false, x) = fkRectStripInitial n x := rfl

@[simp] theorem fkRectStripBoundary_true {W : Nat} (n : Nat) (x : Fin W) :
    fkRectStripBoundary n (true, x) = fkRectStripCurrent n x := rfl


end
end StatMech.FrontierD
