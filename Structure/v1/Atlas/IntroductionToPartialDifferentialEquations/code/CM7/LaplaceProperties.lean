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
open Set Metric MeasureTheory Topology Filter


public noncomputable section

namespace CM7

/-- A `PDEDomain` in $\mathbb{R}^n$ is a connected open subset, the natural setting in
which to pose boundary-value problems for PDEs. -/
structure PDEDomain (n : ℕ) where
  carrier : Set (Fin n → ℝ)
  isOpen : IsOpen carrier
  isConnected : IsConnected carrier

end CM7
end
