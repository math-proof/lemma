/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM12/Wave3D.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Def.v1.Atlas.IntroductionToPartialDifferentialEquations.code.CM11.Wave1D
public import Theorem.Real.Atlas.v1.IntroductionToPartialDifferentialEquations.code.CM11.Wave1D
set_option maxHeartbeats 3200000


@[expose] public noncomputable section

open Matrix Real MeasureTheory Filter intervalIntegral

namespace WaveEquation3D

/-- Shorthand for $3$-dimensional Euclidean space $\mathbb{R}^3$ used as the
spatial domain for the wave equation. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

end WaveEquation3D
end
