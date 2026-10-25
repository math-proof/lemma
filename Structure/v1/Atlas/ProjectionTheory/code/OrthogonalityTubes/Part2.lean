/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/OrthogonalityTubes.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.v1.Atlas.ProjectionTheory.code.OrthogonalityTubes.Part2


noncomputable section

namespace OrthogonalityTubes

open MeasureTheory

/-- An oriented rectangle in $\mathbb{R}^2$ of given width and length, parameterised by a
centre and a unit direction (the axis of the rectangle). -/
structure Rectangle (width length : ℝ) where
  center : EuclideanSpace ℝ (Fin 2)
  direction : EuclideanSpace ℝ (Fin 2)
  direction_unit : ‖direction‖ = 1

end OrthogonalityTubes
end
