/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/FourierAnalysis/code/FiniteMeasures.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Topology.Order.Basic
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Def.v1.Atlas.FourierAnalysis.code.FiniteMeasures

public section

noncomputable section

open MeasureTheory BoundedContinuousFunction Complex MeasureTheory.Measure

open Filter Topology Metric

open scoped FourierTransform

namespace FourierTransformMeasure

variable {μ : Measure ℝ} [IsFiniteMeasure μ]

theorem continuous_fourierTransformMeasure :
    Continuous (fourierTransformMeasure μ) :=
  continuous_charFun.comp continuous_neg

theorem norm_fourierTransformMeasure_le (ξ : ℝ) :
    ‖fourierTransformMeasure μ ξ‖ ≤ μ.real Set.univ :=
  norm_charFun_le (-ξ)

end FourierTransformMeasure
end
