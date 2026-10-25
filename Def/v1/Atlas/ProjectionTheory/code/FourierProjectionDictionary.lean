/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/FourierProjectionDictionary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
open MeasureTheory VectorFourier


noncomputable section

namespace FourierProjection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

section WithMeasure

variable [MeasurableSpace E]

/-- Projection of `f : E → ℂ` onto a subspace `V ⊂ E`, defined by integrating out
the orthogonal directions: `(π_V f)(y) = ∫_{V^⊥} f(y + z) dμ_perp(z)`. -/
def subspaceProjection (V : Submodule ℝ E)
    (μ_perp : Measure ↥(Vᗮ))
    (f : E → ℂ) (y : ↥V) : ℂ :=
  ∫ z : ↥(Vᗮ), f ((y : E) + (z : E)) ∂μ_perp

end WithMeasure
end FourierProjection
end
