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
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryConnectivityTransfer.Part13
open Finset Matrix Filter Topology


namespace StatMech.FrontierD

noncomputable section

attribute [local instance] Classical.propDecidable


def fkRectStripLayerEmbed {W : Nat} (n : Nat) :
    FKRectLayerVertex W -> FKRectStripVertex W (n + 1) := fun u =>
  if u.1 = fkRectLayerInitialRole then
    Sum.inl (fkRectStripInitial n u.2)
  else if u.1 = fkRectLayerOldRole then
    Sum.inl (fkRectStripCurrent n u.2)
  else
    Sum.inr u.2

end
end StatMech.FrontierD
