/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFullSquareBoundaryProjectionGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicMarkedEndpointTraceProjection.Part3
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicFullSquareBoundaryProjectionGeometry.Part2


namespace StatMech.Universality

open Filter Metric Set

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

noncomputable def PhysicalBoundaryProjectionSampling.ofFullSquareProjections
    {N : Nat -> Nat} {mesh : Nat -> Real} {Phi : Complex -> Complex}
    (L : NNReal) (hPhi : LipschitzWith L (fun z => (Phi z).im))
    (hmesh : forall k, 0 <= mesh k)
    (hvertexTrace : forall k x,
      fkIsingSquareFullVertexFixedBoundary (N k) x ->
        (Phi (fullSquareVertexBoundaryProjection
          (N k) (mesh k) x)).im = 0)
    (hfaceTrace : forall k c,
      fkIsingSquareFullFaceFixedBoundary (N k) c ->
        (Phi (fullSquareFaceFixedBoundaryProjection
          (N k) (mesh k) c)).im = 1) :
    PhysicalBoundaryProjectionSampling N mesh Phi where
  lipschitzConstant := L
  imPhi_lipschitz := hPhi
  vertexProjection k x :=
    fullSquareVertexBoundaryProjection (N k) (mesh k) x.1
  faceProjection k c :=
    fullSquareFaceFixedBoundaryProjection (N k) (mesh k) c.1
  vertexProjection_trace k x := hvertexTrace k x.1 x.2
  faceProjection_trace k c := hfaceTrace k c.1 c.2
  vertexProjection_dist_le_mesh k x := by
    rw [fullSquareVertexBoundaryProjection_dist]
    exact hmesh k
  faceProjection_dist_le_mesh k c :=
    fullSquareFaceFixedBoundaryProjection_dist_le
      (N k) (mesh k) (hmesh k) c.1


end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
