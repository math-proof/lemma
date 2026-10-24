/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/SubGaussian.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds
set_option maxHeartbeats 400000

open MeasureTheory ProbabilityTheory Real ENNReal MeasureTheory.Measure Set

namespace SubGaussian

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Definition 9.4.17 ($K$-sub-Gaussian random variable). A real-valued random variable
$X$ is $K$-sub-Gaussian if for every $t \ge 0$,
$\mathbb{P}(|X - \mathbb{E} X| \ge t) \le 2 \exp(-t^2 / K^2)$. -/
def IsSubGaussian (X : Ω → ℝ) (K : ℝ) (μ : Measure Ω) : Prop :=
  ∀ t : ℝ, 0 ≤ t →
    μ {ω | t ≤ |X ω - ∫ ω', X ω' ∂μ|} ≤
      ENNReal.ofReal (2 * exp (-(t ^ 2 / K ^ 2)))

/-- Sub-Gaussian tail bound around an arbitrary center $m$: for every $t \ge 0$,
$\mathbb{P}(|X - m| \ge t) \le 2 \exp(-t^2 / K^2)$. -/
def HasSubGaussianTail (X : Ω → ℝ) (m K : ℝ) (μ : Measure Ω) : Prop :=
  ∀ t : ℝ, 0 ≤ t →
    μ {ω | t ≤ |X ω - m|} ≤ ENNReal.ofReal (2 * exp (-(t ^ 2 / K ^ 2)))

/-- $\mathrm{med}$ is a median of $X$ if $\mathbb{P}(X \ge \mathrm{med}) \ge 1/2$ and
$\mathbb{P}(X \le \mathrm{med}) \ge 1/2$. -/
def IsMedian (X : Ω → ℝ) (med : ℝ) (μ : Measure Ω) [IsProbabilityMeasure μ] : Prop :=
  μ {ω | med ≤ X ω} ≥ ENNReal.ofReal (1/2) ∧
  μ {ω | X ω ≤ med} ≥ ENNReal.ofReal (1/2)
