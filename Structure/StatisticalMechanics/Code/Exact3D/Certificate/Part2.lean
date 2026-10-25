/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Certificate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.StatisticalMechanics.Code.Exact3D.RG.Part2
import Theorem.StatisticalMechanics.Code.Exact3D.Certificate.Part5


namespace StatMech

namespace Exact3D

namespace RGCertificate

structure Valid {ι : Type*} {M : CriticalModel ι}
    (C : RGCertificate M) (correlationLength : ℝ → ℝ) : Prop where
  finiteCaseChecks : FiniteCaseChecks C
  tailBounds : TailBounds C
  fixedPointEnclosure : FixedPointEnclosure C
  linearizationEnclosure : LinearizationEnclosure C
  hyperbolicSplitting : HyperbolicSplitting C
  orbitEntry : OrbitEntry C
  bridge : RGToExponentBridge C correlationLength


end RGCertificate
end Exact3D
end StatMech
