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
public import Theorem.v1.Atlas.FourierAnalysis.code.FiniteMeasures

@[expose] public section

noncomputable section

open MeasureTheory BoundedContinuousFunction Complex MeasureTheory.Measure

open Filter Topology Metric

open scoped FourierTransform

namespace FourierTransformMeasure

variable {μ : Measure ℝ} [IsFiniteMeasure μ]

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

end FourierTransformMeasure
end
