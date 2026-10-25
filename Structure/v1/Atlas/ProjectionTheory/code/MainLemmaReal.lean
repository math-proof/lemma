/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/MainLemmaReal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Abbrev.v1.Atlas.ProjectionTheory.code.MainLemmaReal
open MeasureTheory Metric Set


noncomputable section

namespace FrequencyDecomposition

/-- A $1 \times R$ tube in $\mathbb{R}^2$: an oriented rectangle of length $R \geq 1$
and width $1$, specified by its center and direction angle. -/
structure Tube where
  center : ℝ2
  direction : ℝ
  R : ℝ
  hR : 1 ≤ R

/-- A generic axis-aligned-along-direction rectangle in $\mathbb{R}^2$, with arbitrary
`halfWidth` and `halfLength`, used to contain bundles of $1 \times R$ tubes. -/
structure WideTube where
  center : ℝ2
  direction : ℝ
  halfWidth : ℝ
  halfLength : ℝ

end FrequencyDecomposition
end
