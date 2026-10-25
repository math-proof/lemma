/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyCertificateExample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.StableKeyCertificate.Part10
import Theorem.StatisticalMechanics.Code.Exact3D.StableKeyCertificateExample


namespace StatMech

namespace Exact3D

namespace BoundedPolymerCase

namespace StableKeyCertificateExample

open StatMech.Lattice


noncomputable def rawRows (d R maxDegree maxRange : ℕ) :
    List (StableKeyIntervalRow maxDegree maxRange) :=
  StableKeyIntervalRow.rowsOfKeys
    ((exhaustiveTable d R maxDegree maxRange).image stableKey)
    (fun _ => zeroInterval)


noncomputable def minimalCubicRows (d R maxDegree maxRange : ℕ) :
    List (StableKeyIntervalRow maxDegree maxRange) :=
  StableKeyIntervalRow.rowsOfKeys
    ((exhaustiveCubicClassTable d R maxDegree maxRange).image
      minimalCubicStableKey)
    (fun _ => zeroInterval)


end StableKeyCertificateExample
end BoundedPolymerCase
end Exact3D
end StatMech
