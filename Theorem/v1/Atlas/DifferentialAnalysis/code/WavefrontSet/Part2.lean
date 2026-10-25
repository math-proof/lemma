/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSet.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Analysis.Distribution.Support
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Fourier.Convolution
import Def.v1.Atlas.DifferentialAnalysis.code.DifferentialOperators.Part2
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.DifferentialOperators
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.HormanderFundamental
import Def.v1.Atlas.DifferentialAnalysis.code.HormanderFundamental
import Instance.v1.Atlas.DifferentialAnalysis.code.WavefrontSet.Part2


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
