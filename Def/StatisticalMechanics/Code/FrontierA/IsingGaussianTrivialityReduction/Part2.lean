/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianTrivialityReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamImprovementReduction
import Theorem.StatisticalMechanics.Code.FrontierA.RandomWalkHighDimensionalReduction.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianTrivialityReduction
open Filter Finset Topology
open scoped BigOperators


namespace StatMech.FrontierA

def scalarGaussianCumulant (variance : ℝ) (order : ℕ) : ℝ :=
  if order = 2 then variance else 0


def HasScalarMomentCumulantRecurrence
    (moments cumulants : ℕ → ℕ → ℝ) : Prop :=
  (∀ scale, moments scale 0 = 1) ∧
  ∀ scale order,
    moments scale (order + 1) =
      ∑ k ∈ Finset.range (order + 1),
        (order.choose k : ℝ) * cumulants scale (k + 1) *
          moments scale (order - k)


end StatMech.FrontierA
