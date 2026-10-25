/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianTrivialityReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamImprovementReduction
import Theorem.StatisticalMechanics.Code.FrontierA.RandomWalkHighDimensionalReduction.Part3
import Def.StatisticalMechanics.Code.FrontierA.IsingGaussianTrivialityReduction
open Filter Finset Topology
open scoped BigOperators


namespace StatMech.FrontierA

theorem renormalizedFourPointCoupling_tendsto_zero
    (fourthMoment variance normalization : ℕ → ℝ)
    (normalizationLimit : ℝ)
    (hfourthCumulant : Tendsto
      (fun n => scalarFourthCumulant (fourthMoment n) (variance n))
      atTop (nhds 0))
    (hnormalization : Tendsto normalization atTop (nhds normalizationLimit))
    (hnormalizationLimit : normalizationLimit ≠ 0) :
    Tendsto
      (fun n => renormalizedFourPointCoupling
        (fourthMoment n) (variance n) (normalization n))
      atTop (nhds 0) := by
  have hneg : Tendsto
      (fun n => -scalarFourthCumulant (fourthMoment n) (variance n))
      atTop (nhds (-0)) := hfourthCumulant.neg
  have hdiv := hneg.div hnormalization hnormalizationLimit
  simpa [renormalizedFourPointCoupling] using hdiv


end StatMech.FrontierA
