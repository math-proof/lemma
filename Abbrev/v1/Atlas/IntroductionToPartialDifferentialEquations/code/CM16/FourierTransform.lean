/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM16/FourierTransform.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Fourier.Inversion
public import Mathlib.Analysis.Fourier.FourierTransformDeriv
public import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.Analysis.Convolution
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Calculus.Deriv.Pi
public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.Analysis.Calculus.ContDiff.WithLp
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Topology.ContinuousMap.ZeroAtInfty
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
open MeasureTheory Complex Finset SchwartzMap
open scoped FourierTransform RealInnerProductSpace

set_option maxHeartbeats 400000


@[expose] public noncomputable section

namespace FourierAnalysis

/-- A multi-index of dimension `n`: an `n`-tuple $\vec{\alpha} = (\alpha^1, \dots, \alpha^n)$
of non-negative integers, encoded as a function `Fin n → ℕ`. -/
abbrev MultiIndex (n : ℕ) := Fin n → ℕ

end FourierAnalysis
end
