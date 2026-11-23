/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Certificate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import Def.StatisticalMechanics.Code.Exact3D.RG.Part2
public import Theorem.StatisticalMechanics.Code.Exact3D.Certificate

@[expose] public section

namespace StatMech

namespace Exact3D

namespace RGCertificate

def retarget {ι κ : Type*} {M : CriticalModel ι}
    (C : RGCertificate M) (N : CriticalModel κ) : RGCertificate N where
  H := C.H
  R := C.R
  fixedPointData := C.fixedPointData

end RGCertificate
end Exact3D
end StatMech
