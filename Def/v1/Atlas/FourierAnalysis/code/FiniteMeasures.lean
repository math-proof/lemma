/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/FourierAnalysis/code/FiniteMeasures.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Order.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Integral.Bochner.Set


noncomputable section

open MeasureTheory BoundedContinuousFunction Complex MeasureTheory.Measure

open Filter Topology Metric

open scoped FourierTransform

namespace FourierTransformMeasure

variable {μ : Measure ℝ} [IsFiniteMeasure μ]

def fourierTransformMeasure (μ : Measure ℝ) [IsFiniteMeasure μ] (ξ : ℝ) : ℂ :=
  charFun μ (-ξ)

end FourierTransformMeasure
end
