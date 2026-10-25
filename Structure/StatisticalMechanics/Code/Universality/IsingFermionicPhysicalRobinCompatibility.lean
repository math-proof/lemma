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
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRobinCompatibility


namespace StatMech.Universality

open Filter Metric Set Topology

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

structure DirectionalFourthOrderHarmonicData
    (f : Complex → Real) (z : Complex) (boundOne boundTwo : Real) : Prop where
  contDiffOne : ContDiff Real 4
    (fun t : Real ↦ f (z + (t : Complex) * (1 + Complex.I)))
  contDiffTwo : ContDiff Real 4
    (fun t : Real ↦ f (z + (t : Complex) * (1 - Complex.I)))
  fourthOne : ∀ t,
    |iteratedDeriv 4
      (fun s : Real ↦ f (z + (s : Complex) * (1 + Complex.I))) t| ≤ boundOne
  fourthTwo : ∀ t,
    |iteratedDeriv 4
      (fun s : Real ↦ f (z + (s : Complex) * (1 - Complex.I))) t| ≤ boundTwo
  harmonic :
    iteratedDeriv 2
        (fun t : Real ↦ f (z + (t : Complex) * (1 + Complex.I))) 0 +
      iteratedDeriv 2
        (fun t : Real ↦ f (z + (t : Complex) * (1 - Complex.I))) 0 = 0


structure PhysicalFourthOrderBulkData
    (N : Nat → Nat) (Phi : Complex → Complex) (mesh : Nat → Real) where
  boundOne : Real
  boundTwo : Real
  boundSum_nonneg : 0 ≤ boundOne + boundTwo
  vertex : ∀ k x,
    ¬ fkIsingSquareFullVertexFixedBoundary (N k) x →
    fkIsingSquareFullVertexGhostMultiplicity (N k) x = 0 →
      DirectionalFourthOrderHarmonicData (fun z ↦ (Phi z).im)
        (fullSquareScaledVertexEmbedding (N k) (mesh k) x)
        boundOne boundTwo
  face : ∀ k c,
    ¬ fkIsingSquareFullFaceFixedBoundary (N k) c →
    fkIsingSquareFullFaceGhostMultiplicity (N k) c = 0 →
      DirectionalFourthOrderHarmonicData (fun z ↦ (Phi z).im)
        (fullSquareScaledFaceEmbedding (N k) (mesh k) c)
        boundOne boundTwo

end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
