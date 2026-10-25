/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/RandomWalkHighDimensional.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.RandomWalkHighDimensionalReduction.Part3
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Def.StatisticalMechanics.Code.FrontierA.RandomWalkHighDimensional
open Filter Finset Topology
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Lattice


structure HighDimensionalRandomWalkHypotheses
    (d : ℕ) (betaC epsilon sigma C c : ℝ)
    (twoPoint : ℝ → Site d → ℝ) (xi : ℝ → ℝ) : Type where
  dimension : 2 < d
  epsilon_pos : 0 < epsilon
  sigma_pos : 0 < sigma
  C_pos : 0 < C
  c_pos : 0 < c
  correlationLength_pos : ∀ beta, beta ≤ betaC → 0 < xi beta
  transfer : ℝ → PositiveAdditiveOperator (Site d)
  effectiveGreen : ℝ → Site d → ℝ
  twoPoint_nonneg : ∀ beta x, 0 ≤ twoPoint beta x
  renewal : ∀ beta, beta ≤ betaC → ∀ x,
    twoPoint beta x ≤ latticeOriginDelta d x + transfer beta (twoPoint beta) x
  partial_tendsto : ∀ beta, beta ≤ betaC → ∀ x,
    Tendsto
      (fun n => randomWalkPartial (transfer beta) (latticeOriginDelta d) n x)
      atTop (nhds (effectiveGreen beta x))
  remainder_tendsto : ∀ beta, beta ≤ betaC → ∀ x,
    Tendsto (fun n => randomWalkIterate (transfer beta) n (twoPoint beta) x)
      atTop (nhds 0)
  effectiveGreen_bound : ∀ beta, beta ≤ betaC → ∀ x,
    effectiveGreen beta x ≤ latticeOriginDelta d x +
      highDimensionalRandomWalkTail d epsilon sigma C c (xi beta)
        (latticeEuclideanRadius d x)


end StatMech.FrontierA
