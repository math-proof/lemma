/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/SzemerediTrotter.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.v1.Atlas.ProjectionTheory.code.SzemerediTrotter
open Finset Real


noncomputable section

namespace ProjectionTheory

/-- The line through $p_0$ in direction $\theta \in [0, \pi)$: the fiber of $\pi_\theta$
passing through $p_0$, packaged as a `Line2`. -/
def mkProjLine (θ : ℝ) (hθ : 0 ≤ θ ∧ θ < Real.pi) (p₀ : Fin 2 → ℝ) :
    SzemerediTrotter.Line2 where
  carrier := AffineSubspace.mk' p₀ (LinearMap.ker (projR2Lin θ))
  dim_eq := by rw [AffineSubspace.direction_mk']; exact projR2Lin_ker_finrank θ hθ
  nonempty := ⟨p₀, by simp [AffineSubspace.mem_mk', sub_self]⟩

end ProjectionTheory
end
