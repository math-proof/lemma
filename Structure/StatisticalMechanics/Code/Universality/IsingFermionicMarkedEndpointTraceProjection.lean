/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicMarkedEndpointTraceProjection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBoundaryProjectionSampling.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicMarkedEndpointInputAssembly
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPolynomialEndpointConvergence.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicMarkedEndpointTraceProjection


namespace StatMech.Universality

open Filter Metric Set

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

structure LocalBoundaryTraceProjection
    (Phi : Complex -> Complex) (S : Set Complex) (L : NNReal)
    (sample : Complex) (value mesh : Real) where
  boundaryPoint : Complex
  sample_mem : sample ∈ S
  boundary_mem : boundaryPoint ∈ S
  trace : (Phi boundaryPoint).im = value
  dist_le_mesh : dist sample boundaryPoint <= mesh

end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
