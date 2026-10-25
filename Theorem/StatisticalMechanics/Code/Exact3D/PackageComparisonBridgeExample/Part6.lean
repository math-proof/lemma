/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridgeExample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.PackageComparisonBridge
import Theorem.StatisticalMechanics.Code.Exact3D.FiniteWitnessPackageExample.Part6
import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailContractionExample.Part58
import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailWitnessPackageExample.Part7
import Def.StatisticalMechanics.Code.Exact3D.PackageComparisonBridgeExample.Part6


namespace StatMech

namespace Exact3D

namespace PackageComparisonBridgeExample

open FiniteWitnessPackageExample

open FinitePlusTailContractionExample

open InfiniteTailWitnessPackageExample


theorem zeroStableKeyTableWitnessCorrelationLength_eventually_pos :
    ∀ᶠ β in nhdsWithin (ToyCriticalModel exampleScale 3).betaC
        (Set.Iio (ToyCriticalModel exampleScale 3).betaC),
      0 < zeroStableKeyTableWitnessCorrelationLength β :=
  Filter.Eventually.of_forall fun _ => Real.exp_pos _


theorem zeroStableKeyTableWitnessCorrelationLength_exact_power :
    ∀ᶠ β in nhdsWithin (ToyCriticalModel exampleScale 3).betaC
        (Set.Iio (ToyCriticalModel exampleScale 3).betaC),
      zeroStableKeyTableWitnessCorrelationLength β =
        Real.exp
          (-zeroStableKeyTableWitnessPackage.certificate.predictedExponent *
            Real.log ((ToyCriticalModel exampleScale 3).betaC - β)) :=
  Filter.Eventually.of_forall fun _ => by
    rfl


theorem zeroStableKeyTableWitnessBridge :
    zeroStableKeyTableWitnessPackage.certificate.RGToExponentBridge
      zeroStableKeyTableWitnessCorrelationLength :=
  RGCertificate.rgToExponentBridge_of_eventually_exact_power
    zeroStableKeyTableWitnessPackage.certificate
    zeroStableKeyTableWitnessCorrelationLength
    zeroStableKeyTableWitnessCorrelationLength_exact_power


end PackageComparisonBridgeExample
end Exact3D
end StatMech
