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
public import Instance.v1.Atlas.DifferentialAnalysis.code.WavefrontSet.Part2


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

/-- Computing the underlying vector of `-p`: it is `-p.val`. -/
@[simp]
theorem ClosedBall.neg_val (p : ClosedBall n) : (-p).val = -p.val := rfl

/-- The antipodal map is an involution: `-(-p) = p`. -/
@[simp]
theorem ClosedBall.neg_neg (p : ClosedBall n) : -(-p) = p := by
  apply Subtype.ext
  simp [ClosedBall.neg_val]

end ConeSupport
end
