/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/ContinuumBeck.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.ProjectionTheory.code.DeltaRegular
open MeasureTheory Set Metric Classical DeltaRegular
open scoped ENNReal NNReal


noncomputable section

namespace ContinuumBeck

/-- Shorthand for the Euclidean plane `ℝ²`. -/
abbrev E2 := EuclideanSpace ℝ (Fin 2)

end ContinuumBeck
end
