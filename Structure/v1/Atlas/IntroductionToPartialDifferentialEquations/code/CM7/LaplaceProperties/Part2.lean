/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM7/LaplaceProperties.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Tactic
public import Def.v1.Atlas.IntroductionToPartialDifferentialEquations.code.CM7.LaplaceProperties
open Set Metric MeasureTheory Topology Filter


public noncomputable section

namespace CM7

/-- A function $u : \mathbb{R}^n \to \mathbb{R}$ is harmonic on an open set $\Omega$ if it
is $C^2$ on $\Omega$ and satisfies Laplace's equation $\Delta u(x) = 0$ for all $x \in \Omega$. -/
structure IsHarmonic {n : ℕ} (u : (Fin n → ℝ) → ℝ) (Ω : Set (Fin n → ℝ)) : Prop where
  contDiffOn : ContDiffOn ℝ 2 u Ω
  laplacian_eq_zero : ∀ x ∈ Ω, Laplacian n u x = 0

end CM7
end
