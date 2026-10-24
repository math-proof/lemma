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

theorem continuous_fourierTransformMeasure :
    Continuous (fourierTransformMeasure μ) :=
  continuous_charFun.comp continuous_neg

theorem norm_fourierTransformMeasure_le (ξ : ℝ) :
    ‖fourierTransformMeasure μ ξ‖ ≤ μ.real Set.univ :=
  norm_charFun_le (-ξ)

def fourierTransformBCF (μ : Measure ℝ) [IsFiniteMeasure μ] : ℝ →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fourierTransformMeasure μ) continuous_fourierTransformMeasure
    (μ.real Set.univ) norm_fourierTransformMeasure_le

def schwartzFourierTransform (φ : SchwartzMap ℝ ℂ) : ℝ → ℂ :=
  fun y => ∫ ξ, φ ξ * Complex.exp (-(↑y * ↑ξ * Complex.I))

def mulEquiv (c : ℝ) (hc : c ≠ 0) : ℝ ≃L[ℝ] ℝ :=
  ContinuousLinearEquiv.equivOfInverse
    (c • ContinuousLinearMap.id ℝ ℝ) (c⁻¹ • ContinuousLinearMap.id ℝ ℝ)
    (fun x => by
      simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul,
        ← mul_assoc, inv_mul_cancel₀ hc, one_mul])
    (fun x => by
      simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul,
        ← mul_assoc, mul_inv_cancel₀ hc, one_mul])

def WeakConvergenceSmooth (μseq : ℕ → Measure ℝ) (μ : Measure ℝ) : Prop :=
  ∀ f : ℝ → ℝ, (∀ n : ℕ, ContDiff ℝ n f) → HasCompactSupport f →
    Tendsto (fun j => ∫ x, f x ∂(μseq j)) atTop (𝓝 (∫ x, f x ∂μ))
