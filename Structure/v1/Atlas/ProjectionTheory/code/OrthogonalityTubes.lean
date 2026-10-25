/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/OrthogonalityTubes.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.v1.Atlas.ProjectionTheory.code.OrthogonalityTubes


noncomputable section

namespace OrthogonalityTubes

open MeasureTheory

/-- A *tube* of length $R$ in $\mathbb{R}^2$: an oriented $1 \times R$ rectangle parameterised
by a centre point and a unit direction vector. -/
structure Tube (R : ℝ) where
  center : EuclideanSpace ℝ (Fin 2)
  direction : EuclideanSpace ℝ (Fin 2)
  direction_unit : ‖direction‖ = 1

end OrthogonalityTubes
end
