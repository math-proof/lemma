/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialGeometry/code/PlaneCurves.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.v1.Atlas.DifferentialGeometry.code.PlaneCurves.Part2


noncomputable section

namespace PlaneCurves

lemma J_smul (a : ℝ) (v : EuclideanSpace ℝ (Fin 2)) : J (a • v) = a • J v := by
  ext i; fin_cases i <;> simp [smul_eq_mul]

lemma J_add (v w : EuclideanSpace ℝ (Fin 2)) : J (v + w) = J v + J w := by
  ext i; fin_cases i <;> simp; ring

end PlaneCurves
end
