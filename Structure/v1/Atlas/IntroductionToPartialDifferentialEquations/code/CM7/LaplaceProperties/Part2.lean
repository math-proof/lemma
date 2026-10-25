/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM7/LaplaceProperties.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Connected.Clopen
import Mathlib.Tactic
import Def.v1.Atlas.IntroductionToPartialDifferentialEquations.code.CM7.LaplaceProperties
open Set Metric MeasureTheory Topology Filter


noncomputable section

namespace CM7

/-- A function $u : \mathbb{R}^n \to \mathbb{R}$ is harmonic on an open set $\Omega$ if it
is $C^2$ on $\Omega$ and satisfies Laplace's equation $\Delta u(x) = 0$ for all $x \in \Omega$. -/
structure IsHarmonic {n : ℕ} (u : (Fin n → ℝ) → ℝ) (Ω : Set (Fin n → ℝ)) : Prop where
  contDiffOn : ContDiffOn ℝ 2 u Ω
  laplacian_eq_zero : ∀ x ∈ Ω, Laplacian n u x = 0

end CM7
end
