/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/HeatEquationProp1116.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Distribution.TemperedDistribution
public import Mathlib.Analysis.Distribution.Support
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Constructions.Pi
public import Def.v1.Atlas.DifferentialAnalysis.code.DifferentialOperators.Part2
public import Theorem.Real.Atlas.v1.DifferentialAnalysis.code.DifferentialOperators
public import Theorem.Real.Atlas.v1.DifferentialAnalysis.code.SchwartzPartition
public import Theorem.Real.Atlas.v1.DifferentialAnalysis.code.SchwartzCutoffConvergence
public import Theorem.Real.Atlas.v1.DifferentialAnalysis.code.DistributionSupport
public import Theorem.Real.Atlas.v1.DifferentialAnalysis.code.SmoothingOperators
public import Theorem.v1.Atlas.DifferentialAnalysis.code.SchwartzPartition
public import Def.v1.Atlas.DifferentialAnalysis.code.SchwartzCutoffConvergence
public import Theorem.v1.Atlas.DifferentialAnalysis.code.DistributionSupport
public import Def.v1.Atlas.DifferentialAnalysis.code.SmoothingOperators


@[expose] public noncomputable section

open scoped SchwartzMap

open TemperedDistribution LineDeriv Distribution

namespace HeatEquation

variable (n : ℕ)

/-- Space-time `ℝ^(n+1)` for the heat equation, with the time coordinate at index `0` and
spatial coordinates at indices `1, …, n`. -/
abbrev SpaceTime := EuclideanSpace ℝ (Fin (n + 1))

end HeatEquation
end
