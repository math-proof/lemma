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
import Structure.v1.Atlas.IntroductionToPartialDifferentialEquations.code.CM7.LaplaceProperties
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
