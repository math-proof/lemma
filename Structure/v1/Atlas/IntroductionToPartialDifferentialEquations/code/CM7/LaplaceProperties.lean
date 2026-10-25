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
open Set Metric MeasureTheory Topology Filter


noncomputable section

namespace CM7

/-- A `PDEDomain` in $\mathbb{R}^n$ is a connected open subset, the natural setting in
which to pose boundary-value problems for PDEs. -/
structure PDEDomain (n : ℕ) where
  carrier : Set (Fin n → ℝ)
  isOpen : IsOpen carrier
  isConnected : IsConnected carrier

end CM7
end
