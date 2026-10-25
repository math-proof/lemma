/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Certificate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.StatisticalMechanics.Code.Exact3D.RG.Part2
import Def.StatisticalMechanics.Code.Exact3D.Certificate


namespace StatMech

namespace Exact3D

namespace RGCertificate

theorem predictedExponent_pos {ι : Type*} {M : CriticalModel ι}
    (C : RGCertificate M) :
    0 < C.predictedExponent := by
  unfold predictedExponent predictedNu thermalEigenvalue scale
  exact div_pos (Real.log_pos C.R.scale.toReal_gt_one)
    (Real.log_pos C.fixedPointData.thermal_gt_one)


end RGCertificate
end Exact3D
end StatMech
