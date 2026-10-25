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
import Structure.v1.Atlas.ProjectionTheory.code.MainLemma2R.Part2


noncomputable section

open MeasureTheory Metric Set Finset

open scoped Classical InnerProductSpace

namespace ProjectionTheory

/-- The index type of a `TubeCollection` is a `Fintype`. -/
instance (S : TubeCollection) : Fintype S.ι := S.hι

end ProjectionTheory
end
