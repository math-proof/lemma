/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM14/WaveEnergy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Def.v1.Atlas.IntroductionToPartialDifferentialEquations.code.CM14.WaveEnergy
open MeasureTheory Set Finset Classical


@[expose] public noncomputable section

namespace CM14

/-- The $1+n$-dimensional Minkowski spacetime $\mathbb{R} \times \mathbb{R}^n$, with the first
factor interpreted as time. -/
abbrev WaveSpacetime (n : ℕ) := ℝ × (Fin n → ℝ)

/-- A scalar field on spacetime: a function $\phi : \mathbb{R}^{1+n} \to \mathbb{R}$. -/
abbrev WaveScalarField (n : ℕ) := WaveSpacetime n → ℝ

/-- A spacetime vector field: a function $X$ assigning to each $p \in \mathbb{R}^{1+n}$ a vector
$X(p) \in \mathbb{R}^{n+1}$ indexed by spacetime indices. -/
abbrev SpacetimeVectorField (n : ℕ) := WaveSpacetime n → Fin (n + 1) → ℝ

end CM14
end
