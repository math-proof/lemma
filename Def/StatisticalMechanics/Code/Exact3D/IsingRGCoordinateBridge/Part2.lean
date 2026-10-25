/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.StatisticalMechanics.Code.Exact3D.IsingAnalyticBridgeTarget.Part17
import Theorem.StatisticalMechanics.Code.Exact3D.LatticeRG.Part17
import Theorem.StatisticalMechanics.Code.Exact3D.IsingRGCoordinateBridge


namespace StatMech

namespace Exact3D

namespace IsingRGCoordinateScaffold

variable {C : RGCertificate Ising3DModel}


def LengthCovariance (S : IsingRGCoordinateScaffold C) : Prop :=
  ∀ β, β ∈ S.leftCriticalInterval →
    S.renormalizedBeta β ∈ S.leftCriticalInterval ∧
      S.correlationLength (S.renormalizedBeta β) =
        S.correlationLength β / S.latticeRG.kernel.scale.toReal


def CoordinateRGCovariance (S : IsingRGCoordinateScaffold C) : Prop :=
  ∀ β, β ∈ S.leftCriticalInterval →
    C.R.map (S.coordinate β) = S.coordinate (S.renormalizedBeta β)


def MicroscopicOrbitEntry (S : IsingRGCoordinateScaffold C) : Prop :=
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
    S.coordinate β ∈ S.rgNeighborhood


end IsingRGCoordinateScaffold
end Exact3D
end StatMech
