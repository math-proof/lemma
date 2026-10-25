/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianTrivialityReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamImprovementReduction
import Theorem.StatisticalMechanics.Code.FrontierA.RandomWalkHighDimensionalReduction.Part3
import Def.StatisticalMechanics.Code.FrontierA.IsingGaussianTrivialityReduction.Part2
open Filter Finset Topology
open scoped BigOperators


namespace StatMech.FrontierA

structure ScalarWickMoments (variance : ℝ) (moments : ℕ → ℝ) : Prop where
  moment_zero : moments 0 = 1
  moment_one : moments 1 = 0
  recursion : ∀ n,
    moments (n + 2) = (n + 1 : ℝ) * variance * moments n


end StatMech.FrontierA
