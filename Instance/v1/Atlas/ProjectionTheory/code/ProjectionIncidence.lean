/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/ProjectionIncidence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Structure.v1.Atlas.ProjectionTheory.code.ProjectionIncidence


noncomputable section

open scoped Classical

namespace ProjectionIncidence

/-- A point `p ∈ ℝ²` belongs to a line `l : Line2` iff it lies in the underlying
affine subspace. -/
instance : Membership (Fin 2 → ℝ) Line2 where
  mem l p := p ∈ l.carrier

end ProjectionIncidence
end
