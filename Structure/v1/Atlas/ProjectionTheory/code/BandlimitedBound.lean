/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/BandlimitedBound.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Convolution
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.Fourier.FourierTransform
import Def.v1.Atlas.ProjectionTheory.code.BandlimitedBound
open MeasureTheory Function Set Metric
open scoped Convolution


noncomputable section

namespace BandlimitedBound

variable {d : ℕ}

/-- A non-negative integrable majorant `ψ` at scale `r > 0`, used as an approximate
identity in the bandlimited bound. -/
structure IsApproxIdentityMajorant (ψ : EuclideanSpace ℝ (Fin d) → ℝ) (r : ℝ) : Prop where
  nonneg : ∀ x, 0 ≤ ψ x
  integrable : Integrable ψ (volume : Measure (EuclideanSpace ℝ (Fin d)))
  pos_scale : 0 < r

end BandlimitedBound
end
