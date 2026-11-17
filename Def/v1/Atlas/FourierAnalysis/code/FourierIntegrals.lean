/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/FourierAnalysis/code/FourierIntegrals.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Convolution
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.Distribution.TemperedDistribution
public import Mathlib.Analysis.Fourier.LpSpace
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.Analysis.Fourier.FourierTransformDeriv
public import Mathlib.Analysis.Fourier.Inversion
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

@[expose] public section

open MeasureTheory Filter Topology
open scoped Convolution ENNReal NNReal


noncomputable section

namespace ApproxIdentityR

def rescaledKernel (K : ℝ → ℝ) (ε : ℝ) (x : ℝ) : ℝ :=
  (1 / ε) * K (x / ε)

end ApproxIdentityR


namespace CesaroSummation

open ApproxIdentityR Real

def fejerKernelBase (x : ℝ) : ℝ :=
  if x = 0 then (2 * Real.pi)⁻¹
  else 2 * Real.sin (x / 2) ^ 2 / (Real.pi * x ^ 2)

def fejerKernel (N : ℝ) (x : ℝ) : ℝ :=
  N * fejerKernelBase (N * x)

def bookFourier (f : ℝ → ℂ) (ξ : ℝ) : ℂ :=
  ∫ x : ℝ, Complex.exp (-(I * ↑x * ↑ξ)) • f x

def bookFourierInv (g : ℝ → ℂ) (x : ℝ) : ℂ :=
  ((1 : ℂ) / (2 * ↑π)) • ∫ ξ : ℝ, Complex.exp (I * ↑x * ↑ξ) • g ξ

def bookInverseFourier (f : ℝ → ℂ) (x : ℝ) : ℂ := 𝓕⁻ f x

def cesaroMean (f : ℝ → ℂ) (N : ℝ) (x : ℝ) : ℂ :=
  ((1 : ℂ) / (2 * ↑Real.pi)) •
    ∫ ξ : ℝ, Set.indicator (Set.Icc (-N) N)
      (fun ξ => ((1 : ℂ) - ↑|ξ| / ↑N) * (exp (I * ↑x * ↑ξ) * bookFourier f ξ)) ξ

end CesaroSummation
end
