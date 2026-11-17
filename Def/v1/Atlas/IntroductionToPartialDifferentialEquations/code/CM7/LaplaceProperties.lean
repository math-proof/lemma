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
public import Structure.v1.Atlas.IntroductionToPartialDifferentialEquations.code.CM7.LaplaceProperties

@[expose] public section

open Set Metric MeasureTheory Topology Filter


noncomputable section

namespace CM7

/-- The Laplacian $\Delta u(x) = \sum_{i=1}^n \partial_i^2 u(x)$ of a function
$u : \mathbb{R}^n \to \mathbb{R}$, defined using iterated Fréchet derivatives applied to the
standard basis vectors $e_i$. -/
noncomputable def Laplacian (n : ℕ) (u : (Fin n → ℝ) → ℝ) : (Fin n → ℝ) → ℝ :=
  fun x => ∑ i : Fin n, fderiv ℝ (fun y => fderiv ℝ u y (Pi.single i 1)) x (Pi.single i 1)

end CM7
end
