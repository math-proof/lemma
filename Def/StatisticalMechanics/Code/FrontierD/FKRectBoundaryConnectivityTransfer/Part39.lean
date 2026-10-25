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
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryConnectivityTransfer.Part36
open Finset Matrix Filter Topology


namespace StatMech.FrontierD

noncomputable section

attribute [local instance] Classical.propDecidable


def fkRectConfigurationStripSeamGraph (R : FKRectTorus)
    (omega : R.Configuration) :
    SimpleGraph (FKRectStripVertex R.width (R.height - 1)) :=
  fkRectStripSeamGraph R.width_pos (R.height - 1)
    (fkRectConfigurationNonSeamLayerFn R omega)
    (fkRectConfigurationLayer R omega (fkRectBoundarySeamRow R))


noncomputable def fkRectConfigurationStripSeamIso
    (R : FKRectTorus) (omega : R.Configuration) :
    fkRectConfigurationStripSeamGraph R omega ≃g
      fkRectOpenGraph R omega where
  toEquiv := fkRectStripTorusVertexEquiv R
  map_rel_iff' := by
    intro u v
    change (fkRectOpenGraph R omega).Adj
        (fkRectStripCoordinateTorusEquiv R
          (fkRectStripVertexEquiv R.width (R.height - 1) u))
        (fkRectStripCoordinateTorusEquiv R
          (fkRectStripVertexEquiv R.width (R.height - 1) v)) ↔
      (fkRectStripSeamGraph R.width_pos (R.height - 1)
        (fkRectConfigurationNonSeamLayerFn R omega)
        (fkRectConfigurationLayer R omega
          (fkRectBoundarySeamRow R))).Adj u v
    rw [fkRectOpenGraph_adj_iff_coordinateSchedule,
      fkRectStripSeamGraph_adj_iff_coordinateEdge]
    constructor
    · rintro ⟨hne, hschedule⟩
      exact ⟨fun h => hne (congrArg
        (fkRectStripVertexEquiv R.width (R.height - 1)) h),
        hschedule⟩
    · rintro ⟨hne, hschedule⟩
      exact ⟨fun h => hne
        ((fkRectStripVertexEquiv R.width (R.height - 1)).injective h),
        hschedule⟩


end
end StatMech.FrontierD
