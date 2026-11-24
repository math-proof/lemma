module
public import Theorem.StatisticalMechanics.Code.FrontierA.GrahamImprovementReduction
public import Theorem.StatisticalMechanics.Code.FrontierA.RandomWalkHighDimensionalReduction.Part3
open Filter Finset Topology
open scoped BigOperators


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianTrivialityReduction.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

def scalarFourthCumulant (fourthMoment variance : ℝ) : ℝ :=
  fourthMoment - 3 * variance ^ 2


noncomputable def renormalizedFourPointCoupling
    (fourthMoment variance normalization : ℝ) : ℝ :=
  -scalarFourthCumulant fourthMoment variance / normalization


end StatMech.FrontierA
