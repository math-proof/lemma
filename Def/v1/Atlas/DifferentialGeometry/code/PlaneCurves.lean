/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialGeometry/code/PlaneCurves.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib

@[expose] public section

noncomputable section

namespace PlaneCurves

def det2 (v w : EuclideanSpace ℝ (Fin 2)) : ℝ := v 0 * w 1 - v 1 * w 0

end PlaneCurves
end
