/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyCertificateExample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.StableKeyCertificate.Part10


namespace StatMech

namespace Exact3D

namespace BoundedPolymerCase

namespace StableKeyCertificateExample

open StatMech.Lattice


def zeroInterval : RatInterval :=
  RatInterval.point 0


def rowOfKey {maxDegree maxRange : ℕ}
    (k : StableKey maxDegree maxRange) :
    StableKeyIntervalRow maxDegree maxRange :=
  StableKeyIntervalRow.ofKey (fun _ => zeroInterval) k


end StableKeyCertificateExample
end BoundedPolymerCase
end Exact3D
end StatMech
