/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/GGGHMW.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.v1.Atlas.ProjectionTheory.code.DeltaRegular
open MeasureTheory Metric Set DeltaRegular
open scoped ENNReal NNReal


namespace RestrictedProjection

/-- The unit sphere $S^2 \subset \mathbb{R}^3$. -/
noncomputable abbrev S2 : Set (EuclideanSpace ℝ (Fin 3)) :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

end RestrictedProjection
