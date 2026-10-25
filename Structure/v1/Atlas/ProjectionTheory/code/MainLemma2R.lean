/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/MainLemma2R.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Def.v1.Atlas.ProjectionTheory.code.MainLemma2R


noncomputable section

open MeasureTheory Metric Set Finset

open scoped Classical InnerProductSpace

namespace ProjectionTheory

/-- A $1 \times R$ tube in $\mathbb{R}^2$: a long, thin rectangle with unit direction
vector, length `R ≥ 1`, and width $1$. -/
structure Tube where
  R : ℝ
  center : EuclideanSpace ℝ (Fin 2)
  direction : EuclideanSpace ℝ (Fin 2)
  direction_unit : ‖direction‖ = 1
  hR : 1 ≤ R

end ProjectionTheory
end
