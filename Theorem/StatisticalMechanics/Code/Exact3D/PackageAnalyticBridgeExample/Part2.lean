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
import Def.StatisticalMechanics.Code.Exact3D.PackageAnalyticBridgeExample.Part2


namespace StatMech

namespace Exact3D

namespace PackageAnalyticBridgeExample

open PackageComparisonBridgeExample

open PackagePowerLawBridgeExample

open FiniteWitnessPackageExample

open FinitePlusTailContractionExample

open InfiniteTailWitnessPackageExample

open InfiniteTailTableClosedBallRGPackage


theorem contributionSplitWitness_bridge_from_analyticInputs :
    contributionSplitWitnessPackage.certificate.RGToExponentBridge
      contributionSplitWitnessCorrelationLength :=
  contributionSplitWitnessPackage.rgToExponentBridge_of_analyticBridgeInputs
    contributionSplitWitnessAnalyticBridgeInputs


theorem contributionSplitWitness_bridge_from_analyticInputs_congr_pred :
    contributionSplitWitnessPackage.certificate.RGToExponentBridge
      contributionSplitWitnessCorrelationLength :=
  contributionSplitWitnessPackage
    |>.rgToExponentBridge_of_analyticBridgeInputs_congr_predictedExponent
      (D := contributionSplitWitnessPackage.certificate)
      rfl
      contributionSplitWitnessAnalyticBridgeInputs


theorem contributionSplitWitness_valid_from_analyticInputs_congr_pred :
    contributionSplitWitnessPackage.certificate.Valid
      contributionSplitWitnessCorrelationLength :=
  contributionSplitWitnessPackage
    |>.valid_of_analyticBridgeInputs_congr_predictedExponent
      (D := contributionSplitWitnessPackage.certificate)
      rfl
      contributionSplitWitnessAnalyticBridgeInputs


theorem contributionSplitWitness_hasCriticalNu_from_analyticInputs_congr_pred :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      contributionSplitWitnessCorrelationLength
      contributionSplitWitnessPackage.certificate.predictedExponent :=
  contributionSplitWitnessPackage
    |>.hasCriticalNu_of_analyticBridgeInputs_congr_predictedExponent
      (D := contributionSplitWitnessPackage.certificate)
      rfl
      contributionSplitWitnessAnalyticBridgeInputs


theorem contributionSplitWitness_valid_from_analyticInputs :
    contributionSplitWitnessPackage.certificate.Valid
      contributionSplitWitnessCorrelationLength :=
  contributionSplitWitnessPackage.valid_of_analyticBridgeInputs
    contributionSplitWitnessAnalyticBridgeInputs


theorem contributionSplitWitness_hasCriticalNu_from_analyticInputs :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      contributionSplitWitnessCorrelationLength
      contributionSplitWitnessPackage.certificate.predictedExponent :=
  contributionSplitWitnessPackage.hasCriticalNu_of_analyticBridgeInputs
    contributionSplitWitnessAnalyticBridgeInputs


end PackageAnalyticBridgeExample
end Exact3D
end StatMech
