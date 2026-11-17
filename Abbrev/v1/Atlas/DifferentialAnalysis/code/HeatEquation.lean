/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/HeatEquation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Distribution.TemperedDistribution
public import Mathlib.Analysis.InnerProductSpace.PiL2


@[expose] public noncomputable section

open scoped SchwartzMap

open TemperedDistribution LineDeriv

namespace DifferentialOperators

variable (n : ℕ)

/-- The `(n + 1)`-dimensional spacetime `ℝ^{1+n}`, with the first coordinate
playing the role of time and the remaining `n` coordinates the spatial ones. -/
abbrev SpaceTime := EuclideanSpace ℝ (Fin (n + 1))

end DifferentialOperators
end
