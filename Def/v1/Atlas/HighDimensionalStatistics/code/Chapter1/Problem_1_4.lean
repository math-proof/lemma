/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter1/Problem_1_4.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.HighDimensionalStatistics.code.Chapter1.Def_1_2
import Lemma.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter1.Def_1_2
import Mathlib
open MeasureTheory Real ProbabilityTheory


noncomputable section

namespace Problem_1_4

/-- The operator (spectral) norm of an `n × m` real matrix viewed as a
continuous linear map between Euclidean spaces. -/
def matrixOpNorm {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) : ℝ :=
  ‖(Matrix.toEuclideanLin A).toContinuousLinearMap‖

end Problem_1_4
end
