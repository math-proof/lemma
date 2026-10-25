/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageAnalyticBridgeExample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.WitnessAnalyticBridge
import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailAnalyticBridge
import Theorem.StatisticalMechanics.Code.Exact3D.TableClosedBallAnalyticBridge
import Theorem.StatisticalMechanics.Code.Exact3D.PackagePowerLawBridgeExample
import Def.StatisticalMechanics.Code.Exact3D.PackageAnalyticBridgeExample.Part3


namespace StatMech

namespace Exact3D

namespace PackageAnalyticBridgeExample

open PackageComparisonBridgeExample

open PackagePowerLawBridgeExample

open FiniteWitnessPackageExample

open FinitePlusTailContractionExample

open InfiniteTailWitnessPackageExample

open InfiniteTailTableClosedBallRGPackage


theorem geometricTailWitness_bridge_from_analyticInputs :
    geometricTailWitnessPackage.certificate.RGToExponentBridge
      geometricTailCorrelationLength :=
  geometricTailWitnessPackage.rgToExponentBridge_of_analyticBridgeInputs
    geometricTailAnalyticBridgeInputs


theorem geometricTailWitness_bridge_from_analyticInputs_congr_pred :
    geometricTailWitnessPackage.certificate.RGToExponentBridge
      geometricTailCorrelationLength :=
  geometricTailWitnessPackage
    |>.rgToExponentBridge_of_analyticBridgeInputs_congr_predictedExponent
      (D := geometricTailWitnessPackage.certificate)
      rfl
      geometricTailAnalyticBridgeInputs


theorem geometricTailWitness_valid_from_analyticInputs_congr_pred :
    geometricTailWitnessPackage.certificate.Valid
      geometricTailCorrelationLength :=
  geometricTailWitnessPackage
    |>.valid_of_analyticBridgeInputs_congr_predictedExponent
      (D := geometricTailWitnessPackage.certificate)
      rfl
      geometricTailAnalyticBridgeInputs


theorem geometricTailWitness_hasCriticalNu_from_analyticInputs_congr_pred :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      geometricTailCorrelationLength
      geometricTailWitnessPackage.certificate.predictedExponent :=
  geometricTailWitnessPackage
    |>.hasCriticalNu_of_analyticBridgeInputs_congr_predictedExponent
      (D := geometricTailWitnessPackage.certificate)
      rfl
      geometricTailAnalyticBridgeInputs


theorem geometricTailWitness_valid_from_analyticInputs :
    geometricTailWitnessPackage.certificate.Valid
      geometricTailCorrelationLength :=
  geometricTailWitnessPackage.valid_of_analyticBridgeInputs
    geometricTailAnalyticBridgeInputs


theorem geometricTailWitness_hasCriticalNu_from_analyticInputs :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      geometricTailCorrelationLength
      geometricTailWitnessPackage.certificate.predictedExponent :=
  geometricTailWitnessPackage.hasCriticalNu_of_analyticBridgeInputs
    geometricTailAnalyticBridgeInputs


end PackageAnalyticBridgeExample
end Exact3D
end StatMech
