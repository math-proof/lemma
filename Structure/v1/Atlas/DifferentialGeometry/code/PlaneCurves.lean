/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialGeometry/code/PlaneCurves.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.v1.Atlas.DifferentialGeometry.code.PlaneCurves


noncomputable section

namespace PlaneCurves

structure IsRegularCurve (c : ℝ → EuclideanSpace ℝ (Fin 2)) (S : Set ℝ) : Prop where
  smooth : ContDiff ℝ ⊤ c
  deriv_ne_zero : ∀ t ∈ S, deriv c t ≠ 0

end PlaneCurves
end
