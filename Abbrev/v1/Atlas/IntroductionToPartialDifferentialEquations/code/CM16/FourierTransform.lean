/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM16/FourierTransform.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
open MeasureTheory Complex Finset SchwartzMap
open scoped FourierTransform RealInnerProductSpace

set_option maxHeartbeats 400000


noncomputable section

namespace FourierAnalysis

/-- A multi-index of dimension `n`: an `n`-tuple $\vec{\alpha} = (\alpha^1, \dots, \alpha^n)$
of non-negative integers, encoded as a function `Fin n → ℕ`. -/
abbrev MultiIndex (n : ℕ) := Fin n → ℕ

end FourierAnalysis
end
