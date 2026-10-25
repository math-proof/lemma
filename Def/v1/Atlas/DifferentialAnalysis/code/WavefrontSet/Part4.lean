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
import Instance.v1.Atlas.DifferentialAnalysis.code.WavefrontSet


noncomputable section

open scoped SchwartzMap FourierTransform

open MeasureTheory Set

namespace ConeSupport

variable {n : ℕ}

/-- The set of pairs `(p, q)` in `ClosedBall × ClosedBall` for which at least one factor
lies on the boundary sphere. -/
def BoundaryProd : Set (ClosedBall n × ClosedBall n) :=
  {pq | ‖pq.1.val‖ = 1 ∨ ‖pq.2.val‖ = 1}

/-- Antipodal map on the closed ball. -/
def ClosedBall.neg (p : ClosedBall n) : ClosedBall n :=
  ⟨-p.val, by rw [norm_neg]; exact p.property⟩

end ConeSupport
end
