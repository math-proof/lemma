/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackage.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.Certificate.Part6
import Theorem.StatisticalMechanics.Code.Exact3D.FixedPointSkeleton.Part23
import Theorem.StatisticalMechanics.Code.Exact3D.FiniteDimensionalRG.Part15
import Theorem.StatisticalMechanics.Code.Exact3D.FiniteSupportCertificateConsequences
import Theorem.StatisticalMechanics.Code.Exact3D.TailSummabilitySkeleton.Part5
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace RGCertificate

structure FiniteChecks {ι : Type*} {M : CriticalModel ι}
    (C : RGCertificate M) : Prop where
  finiteCaseChecks : C.FiniteCaseChecks
  tailBounds : C.TailBounds
  fixedPointEnclosure : C.FixedPointEnclosure
  linearizationEnclosure : C.LinearizationEnclosure
  hyperbolicSplitting : C.HyperbolicSplitting
  orbitEntry : C.OrbitEntry


end RGCertificate
end Exact3D
end StatMech
