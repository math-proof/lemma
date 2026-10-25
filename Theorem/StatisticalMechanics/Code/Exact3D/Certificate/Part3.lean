/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Certificate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.StatisticalMechanics.Code.Exact3D.RG.Part2
import Def.StatisticalMechanics.Code.Exact3D.Certificate.Part3


namespace StatMech

namespace Exact3D

namespace RGCertificate

theorem linearizationEnclosure_of_thermal_gt_one {ι : Type*}
    {M : CriticalModel ι} (C : RGCertificate M) :
    C.LinearizationEnclosure := by
  simpa [LinearizationEnclosure, thermalEigenvalue] using
    Real.log_pos C.fixedPointData.thermal_gt_one


end RGCertificate
end Exact3D
end StatMech
