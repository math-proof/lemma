/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianNewmanBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianMomentConvergence
open Filter MeasureTheory Set Topology


namespace StatMech.FrontierA

open ProbabilityTheory


theorem scalarFourthCumulant_tendsto_zero_of_renormalizedCoupling
    (fourthMoment variance normalization : Nat -> Real)
    (normalizationLimit : Real)
    (hnonzero : forall scale, normalization scale ≠ 0)
    (hcoupling : Tendsto
      (fun scale => renormalizedFourPointCoupling
        (fourthMoment scale) (variance scale) (normalization scale))
      atTop (nhds 0))
    (hnormalization : Tendsto normalization atTop
      (nhds normalizationLimit)) :
    Tendsto
      (fun scale => scalarFourthCumulant
        (fourthMoment scale) (variance scale))
      atTop (nhds 0) := by
  have hproduct := hcoupling.neg.mul hnormalization
  have hidentity :
      (fun scale =>
        -renormalizedFourPointCoupling
            (fourthMoment scale) (variance scale) (normalization scale) *
          normalization scale) =
        fun scale => scalarFourthCumulant
          (fourthMoment scale) (variance scale) := by
    funext scale
    unfold renormalizedFourPointCoupling
    field_simp [hnonzero scale]
  rw [hidentity] at hproduct
  simpa using hproduct


end StatMech.FrontierA
