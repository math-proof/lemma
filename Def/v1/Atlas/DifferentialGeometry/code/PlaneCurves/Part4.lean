/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialGeometry/code/PlaneCurves.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Abbrev.v1.Atlas.DifferentialGeometry.code.PlaneCurves


noncomputable section

namespace PlaneCurves

def hessianVec (F : R2 → ℝ) (x v : R2) : R2 :=
  fderiv ℝ (fun y => gradient F y) x v

end PlaneCurves
end
