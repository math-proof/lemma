/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/LindebergHybrid.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Structure.v1.Atlas.BooleanFunctions.code.InvarianceDefs

@[expose] public section

noncomputable section

open MeasureTheory Measure Finset BigOperators ENNReal

namespace BooleanFourier

def rademacherMeasure : Measure ℝ :=
  (2 : ENNReal)⁻¹ • Measure.dirac (-1 : ℝ) + (2 : ENNReal)⁻¹ • Measure.dirac (1 : ℝ)

end BooleanFourier
end
