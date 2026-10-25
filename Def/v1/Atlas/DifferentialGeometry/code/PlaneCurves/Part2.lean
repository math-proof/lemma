/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialGeometry/code/PlaneCurves.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Structure.v1.Atlas.DifferentialGeometry.code.PlaneCurves


noncomputable section

namespace PlaneCurves

def curvature (c : ℝ → EuclideanSpace ℝ (Fin 2)) (t : ℝ) : ℝ :=
  det2 (deriv c t) (deriv (deriv c) t) / ‖deriv c t‖ ^ 3

def J (v : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm ![- v 1, v 0]

end PlaneCurves
end
