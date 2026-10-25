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
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryConnectivityTransfer.Part35
open Finset Matrix Filter Topology


namespace StatMech.FrontierD

noncomputable section

attribute [local instance] Classical.propDecidable


def fkRectStripTorusRowEquiv (R : FKRectTorus) :
    Fin (R.height - 1 + 1) ≃ Fin R.height :=
  finCongr (Nat.sub_add_cancel
    (Nat.one_le_iff_ne_zero.mpr R.height_pos.ne'))


def fkRectStripCoordinateTorusEquiv (R : FKRectTorus) :
    (Fin R.width × Fin (R.height - 1 + 1)) ≃ R.Vertex :=
  Equiv.prodCongr (Equiv.refl _) (fkRectStripTorusRowEquiv R)


def fkRectStripTorusVertexEquiv (R : FKRectTorus) :
    FKRectStripVertex R.width (R.height - 1) ≃ R.Vertex :=
  (fkRectStripVertexEquiv R.width (R.height - 1)).trans
    (fkRectStripCoordinateTorusEquiv R)

end
end StatMech.FrontierD
