/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialGeometry/code/PlaneCurves.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import Def.v1.Atlas.DifferentialGeometry.code.PlaneCurves.Part3


@[expose] public noncomputable section

namespace PlaneCurves

abbrev R2 := EuclideanSpace ℝ (Fin 2)

end PlaneCurves
end
