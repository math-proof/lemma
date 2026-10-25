/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/HeatEquationProp1116.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Analysis.Distribution.Support
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Constructions.Pi
import Def.v1.Atlas.DifferentialAnalysis.code.DifferentialOperators.Part2
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.DifferentialOperators
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.SchwartzPartition
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.SchwartzCutoffConvergence
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.DistributionSupport
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.SmoothingOperators
import Theorem.v1.Atlas.DifferentialAnalysis.code.SchwartzPartition
import Def.v1.Atlas.DifferentialAnalysis.code.SchwartzCutoffConvergence
import Theorem.v1.Atlas.DifferentialAnalysis.code.DistributionSupport
import Def.v1.Atlas.DifferentialAnalysis.code.SmoothingOperators


noncomputable section

open scoped SchwartzMap

open TemperedDistribution LineDeriv Distribution

namespace HeatEquation

variable (n : ℕ)

/-- Space-time `ℝ^(n+1)` for the heat equation, with the time coordinate at index `0` and
spatial coordinates at indices `1, …, n`. -/
abbrev SpaceTime := EuclideanSpace ℝ (Fin (n + 1))

end HeatEquation
end
