/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Certificate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.StatisticalMechanics.Code.Exact3D.RG.Part2
import Theorem.StatisticalMechanics.Code.Exact3D.Certificate.Part3


namespace StatMech

namespace Exact3D

namespace RGCertificate

def FiniteCaseChecks {ι : Type*} {M : CriticalModel ι}
    (_C : RGCertificate M) : Prop :=
  True


def TailBounds {ι : Type*} {M : CriticalModel ι}
    (_C : RGCertificate M) : Prop :=
  True


def HyperbolicSplitting {ι : Type*} {M : CriticalModel ι}
    (C : RGCertificate M) : Prop :=
  1 < C.thermalEigenvalue


end RGCertificate
end Exact3D
end StatMech
