/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRobinCompatibility.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicProjectedFullMedialInterpolation.Part5
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareCaratheodory.Part5
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBoundaryLayerConsistency.Part3
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicCalibratedRobinConsistency
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRobinCompatibility.Part2


namespace StatMech.Universality

open Filter Metric Set Topology

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

structure PhysicalRobinConsistencyInputs
    (N : Nat → Nat) (hN : ∀ k, 0 < N k)
    (Phi : Complex → Complex) (mesh laplacianRate : Nat → Real) where
  mesh_nonneg : ∀ k, 0 ≤ mesh k
  laplacian_nonneg : ∀ k, 0 ≤ laplacianRate k
  vertexFixed : ∀ k x, fkIsingSquareFullVertexFixedBoundary (N k) x →
    (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im = 0
  faceFixed : ∀ k c, fkIsingSquareFullFaceFixedBoundary (N k) c →
    (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) c)).im = 1
  vertexFree : ∀ k x,
    ¬ fkIsingSquareFullVertexFixedBoundary (N k) x →
    0 < fkIsingSquareFullVertexGhostMultiplicity (N k) x →
      (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im = 1
  faceFree : ∀ k c,
    ¬ fkIsingSquareFullFaceFixedBoundary (N k) c →
    0 < fkIsingSquareFullFaceGhostMultiplicity (N k) c →
      (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) c)).im = 0
  vertexLaplacian : ∀ k x,
    ¬ fkIsingSquareFullVertexFixedBoundary (N k) x →
      |isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph (N k))
        (fun y ↦ (Phi (fullSquareScaledVertexEmbedding
          (N k) (mesh k) y)).im) x| ≤ laplacianRate k
  faceLaplacian : ∀ k c,
    ¬ fkIsingSquareFullFaceFixedBoundary (N k) c →
      |isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph (N k))
        (fun d ↦ (Phi (fullSquareScaledFaceEmbedding
          (N k) (mesh k) d)).im) c| ≤ laplacianRate k
  mesh_tendsto : Tendsto mesh atTop (nhds 0)
  scaledLaplacian_tendsto : Tendsto
    (fun k ↦ laplacianRate k * (N k : Real) ^ 2) atTop (nhds 0)


structure PhysicalSplitRobinConsistencyInputs
    (N : Nat → Nat) (hN : ∀ k, 0 < N k)
    (Phi : Complex → Complex)
    (mesh bulkRate layerRate : Nat → Real) where
  mesh_nonneg : ∀ k, 0 ≤ mesh k
  bulk_nonneg : ∀ k, 0 ≤ bulkRate k
  layer_nonneg : ∀ k, 0 ≤ layerRate k
  vertexFixed : ∀ k x, fkIsingSquareFullVertexFixedBoundary (N k) x →
    (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im = 0
  faceFixed : ∀ k c, fkIsingSquareFullFaceFixedBoundary (N k) c →
    (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) c)).im = 1
  vertexFree : ∀ k x,
    ¬ fkIsingSquareFullVertexFixedBoundary (N k) x →
    0 < fkIsingSquareFullVertexGhostMultiplicity (N k) x →
      (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im = 1
  faceFree : ∀ k c,
    ¬ fkIsingSquareFullFaceFixedBoundary (N k) c →
    0 < fkIsingSquareFullFaceGhostMultiplicity (N k) c →
      (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) c)).im = 0
  vertexBulk : ∀ k x,
    ¬ fkIsingSquareFullVertexFixedBoundary (N k) x →
    fkIsingSquareFullVertexGhostMultiplicity (N k) x = 0 →
      |isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph (N k))
        (fun y ↦ (Phi (fullSquareScaledVertexEmbedding
          (N k) (mesh k) y)).im) x| ≤ bulkRate k
  faceBulk : ∀ k c,
    ¬ fkIsingSquareFullFaceFixedBoundary (N k) c →
    fkIsingSquareFullFaceGhostMultiplicity (N k) c = 0 →
      |isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph (N k))
        (fun d ↦ (Phi (fullSquareScaledFaceEmbedding
          (N k) (mesh k) d)).im) c| ≤ bulkRate k
  vertexLayer : ∀ k x,
    ¬ fkIsingSquareFullVertexFixedBoundary (N k) x →
    0 < fkIsingSquareFullVertexGhostMultiplicity (N k) x →
      |isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph (N k))
        (fun y ↦ (Phi (fullSquareScaledVertexEmbedding
          (N k) (mesh k) y)).im) x| ≤ layerRate k
  faceLayer : ∀ k c,
    ¬ fkIsingSquareFullFaceFixedBoundary (N k) c →
    0 < fkIsingSquareFullFaceGhostMultiplicity (N k) c →
      |isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph (N k))
        (fun d ↦ (Phi (fullSquareScaledFaceEmbedding
          (N k) (mesh k) d)).im) c| ≤ layerRate k
  scaledBulk_tendsto : Tendsto
    (fun k ↦ bulkRate k * (N k : Real) ^ 2) atTop (nhds 0)
  layer_tendsto : Tendsto layerRate atTop (nhds 0)
  mesh_tendsto : Tendsto mesh atTop (nhds 0)


end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
