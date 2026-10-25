/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/LindebergHybrid.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.BooleanFunctions.code.InvarianceDefs


noncomputable section

open MeasureTheory Measure Finset BigOperators ENNReal

namespace BooleanFourier

def rademacherMeasure : Measure ℝ :=
  (2 : ℝ≥0∞)⁻¹ • Measure.dirac (-1 : ℝ) + (2 : ℝ≥0∞)⁻¹ • Measure.dirac (1 : ℝ)

end BooleanFourier
end
