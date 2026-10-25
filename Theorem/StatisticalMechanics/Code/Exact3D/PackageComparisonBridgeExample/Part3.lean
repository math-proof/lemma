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
import Def.StatisticalMechanics.Code.Exact3D.PackageComparisonBridgeExample.Part3


namespace StatMech

namespace Exact3D

namespace PackageComparisonBridgeExample

open FiniteWitnessPackageExample

open FinitePlusTailContractionExample

open InfiniteTailWitnessPackageExample


theorem doubledGeometricTailCorrelationLength_comparable :
    ∀ᶠ β in nhdsWithin (ToyCriticalModel exampleScale 3).betaC
        (Set.Iio (ToyCriticalModel exampleScale 3).betaC),
      (2 : ℝ) * geometricTailCorrelationLength β ≤
          doubledGeometricTailCorrelationLength β ∧
        doubledGeometricTailCorrelationLength β ≤
          (2 : ℝ) * geometricTailCorrelationLength β :=
  Filter.Eventually.of_forall fun _ => by
    simp [doubledGeometricTailCorrelationLength]


theorem geometricTailWitness_bridge_doubled_by_package_comparison :
    geometricTailWitnessPackage.certificate.RGToExponentBridge
      doubledGeometricTailCorrelationLength :=
  geometricTailWitnessPackage.rgToExponentBridge_of_eventually_const_mul_le_le
    geometricTailWitnessBridge
    geometricTailCorrelationLength_eventually_pos
    (by norm_num : (0 : ℝ) < 2)
    (by norm_num : (0 : ℝ) < 2)
    doubledGeometricTailCorrelationLength_comparable


theorem geometricTailWitness_valid_doubled_by_package_comparison :
    geometricTailWitnessPackage.certificate.Valid
      doubledGeometricTailCorrelationLength :=
  geometricTailWitnessPackage.valid_of_eventually_const_mul_le_le
    geometricTailWitnessBridge
    geometricTailCorrelationLength_eventually_pos
    (by norm_num : (0 : ℝ) < 2)
    (by norm_num : (0 : ℝ) < 2)
    doubledGeometricTailCorrelationLength_comparable


theorem geometricTailWitness_hasCriticalNu_doubled_by_package_comparison :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      doubledGeometricTailCorrelationLength
      geometricTailWitnessPackage.certificate.predictedExponent :=
  geometricTailWitnessPackage.hasCriticalNu_of_eventually_const_mul_le_le
    geometricTailWitnessBridge
    geometricTailCorrelationLength_eventually_pos
    (by norm_num : (0 : ℝ) < 2)
    (by norm_num : (0 : ℝ) < 2)
    doubledGeometricTailCorrelationLength_comparable


end PackageComparisonBridgeExample
end Exact3D
end StatMech
