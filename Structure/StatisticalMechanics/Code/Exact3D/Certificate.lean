/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Certificate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.StatisticalMechanics.Code.Exact3D.RG.Part2


namespace StatMech

namespace Exact3D

structure RGCertificate {ι : Type*} (M : CriticalModel ι) where
  H : EffectiveHamiltonian
  R : BlockSpinMap H
  fixedPointData : RGFixedPointData H R

end Exact3D
end StatMech
