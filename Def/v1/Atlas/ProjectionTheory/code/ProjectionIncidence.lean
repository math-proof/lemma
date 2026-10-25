/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/ProjectionIncidence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Instance.v1.Atlas.ProjectionTheory.code.ProjectionIncidence


noncomputable section

open scoped Classical

namespace ProjectionIncidence

/-- The number of incidences `I(X, L) = #{(x, ℓ) ∈ X × L : x ∈ ℓ}` between a finite
set of points `X ⊆ ℝ²` and a finite set of lines `L`. -/
def incidenceCount (X : Finset (Fin 2 → ℝ)) (L : Finset Line2) : ℕ :=
  ((X ×ˢ L).filter fun p => p.1 ∈ p.2).card

end ProjectionIncidence
end
