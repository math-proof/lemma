/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter9/TSPHelper.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Theorem.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter9.TSPHelper
set_option maxHeartbeats 400000


noncomputable section

open MeasureTheory Metric Set Real Filter

namespace TSPHelper

/-- The uniform measure on the unit square is a probability measure. -/
instance uniformOnSquare_isProbabilityMeasure : IsProbabilityMeasure uniformOnSquare :=
  ⟨by rw [show uniformOnSquare = volume.restrict unitSquare from rfl,
          Measure.restrict_apply_univ]; exact volume_unitSquare⟩

/-- The product measure of $k$ i.i.d.\ uniform points in the unit square is a
probability measure. -/
instance iidUniformOnSquare_isProbabilityMeasure (k : ℕ) :
    IsProbabilityMeasure (iidUniformOnSquare k) :=
  Measure.pi.instIsProbabilityMeasure (μ := fun _ => uniformOnSquare)

end TSPHelper
end
