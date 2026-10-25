/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/LindebergHybrid.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.BooleanFunctions.code.InvarianceDefs
import Def.v1.Atlas.BooleanFunctions.code.LindebergHybrid


noncomputable section

open MeasureTheory Measure Finset BigOperators ENNReal

namespace BooleanFourier

instance rademacherMeasure_isFiniteMeasure : IsFiniteMeasure rademacherMeasure := by
  constructor
  simp only [rademacherMeasure, Measure.coe_add, Pi.add_apply, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply]
  simp

instance rademacherMeasure_sigmaFinite : SigmaFinite rademacherMeasure :=
  @IsFiniteMeasure.toSigmaFinite _ _ rademacherMeasure _

end BooleanFourier
end
