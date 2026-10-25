/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Certificate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.StatisticalMechanics.Code.Exact3D.RG.Part2
import Def.StatisticalMechanics.Code.Exact3D.Certificate.Part2


namespace StatMech

namespace Exact3D

namespace RGCertificate

@[simp] theorem retarget_predictedExponent {ι κ : Type*}
    {M : CriticalModel ι} (C : RGCertificate M) (N : CriticalModel κ) :
    (C.retarget N).predictedExponent = C.predictedExponent := by
  rfl


end RGCertificate
end Exact3D
end StatMech
