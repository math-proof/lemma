/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/RandomWalkHighDimensional.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.RandomWalkHighDimensionalReduction.Part3
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Structure.StatisticalMechanics.Code.FrontierA.RandomWalkHighDimensional
open Filter Finset Topology
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Lattice


theorem highDimensionalRandomWalk_bound
    {d : ℕ} {betaC epsilon sigma C c : ℝ}
    {twoPoint : ℝ → Site d → ℝ} {xi : ℝ → ℝ}
    (H : HighDimensionalRandomWalkHypotheses
      d betaC epsilon sigma C c twoPoint xi)
    {beta : ℝ} (hbeta : beta ≤ betaC) (x : Site d) :
    twoPoint beta x ≤ latticeOriginDelta d x +
      highDimensionalRandomWalkTail d epsilon sigma C c (xi beta)
        (latticeEuclideanRadius d x) := by
  exact renewal_to_highDimensionalRandomWalk_bound
    (H.transfer beta) d epsilon sigma C c (xi beta)
    (latticeOriginDelta d) (twoPoint beta) (H.effectiveGreen beta)
    (latticeEuclideanRadius d) (H.renewal beta hbeta)
    (H.partial_tendsto beta hbeta) (H.remainder_tendsto beta hbeta)
    (H.effectiveGreen_bound beta hbeta) x

end StatMech.FrontierA
