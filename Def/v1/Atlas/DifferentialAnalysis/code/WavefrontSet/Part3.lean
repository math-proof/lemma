module
public import Mathlib.Analysis.Distribution.TemperedDistribution
public import Mathlib.Analysis.Distribution.Support
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.Fourier.Convolution
public import Def.v1.Atlas.DifferentialAnalysis.code.DifferentialOperators.Part2
public import Theorem.Real.Atlas.v1.DifferentialAnalysis.code.DifferentialOperators
public import Theorem.Real.Atlas.v1.DifferentialAnalysis.code.HormanderFundamental
public import Def.v1.Atlas.DifferentialAnalysis.code.HormanderFundamental
public import Theorem.v1.Atlas.DifferentialAnalysis.code.WavefrontSet


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSet.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
noncomputable section

open scoped SchwartzMap FourierTransform

open MeasureTheory Set

namespace ConeSupport

variable {n : ℕ}

/-- The closed unit ball in `ℝⁿ`, used as a compactification of Euclidean space for
defining the scattering wavefront set. -/
def ClosedBall : Type := {x : EuclideanSpace ℝ (Fin n) // ‖x‖ ≤ 1}

end ConeSupport
end
