module
public import Theorem.StatisticalMechanics.Code.Exact3D.WitnessAnalyticBridge
public import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailAnalyticBridge
public import Theorem.StatisticalMechanics.Code.Exact3D.TableClosedBallAnalyticBridge
public import Theorem.StatisticalMechanics.Code.Exact3D.PackagePowerLawBridgeExample
public import Def.StatisticalMechanics.Code.Exact3D.PackageAnalyticBridgeExample.Part4


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageAnalyticBridgeExample.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Exact3D

namespace PackageAnalyticBridgeExample

open PackageComparisonBridgeExample

open PackagePowerLawBridgeExample

open FiniteWitnessPackageExample

open FinitePlusTailContractionExample

open InfiniteTailWitnessPackageExample

open InfiniteTailTableClosedBallRGPackage


theorem contributionSplitInfiniteTail_bridge_from_analyticInputs :
    contributionSplitAsInfiniteTailPackage.certificate.RGToExponentBridge
      contributionSplitInfiniteTailCorrelationLength :=
  contributionSplitAsInfiniteTailPackage.rgToExponentBridge_of_analyticBridgeInputs
    contributionSplitInfiniteTailAnalyticBridgeInputs


theorem contributionSplitInfiniteTail_bridge_from_analyticInputs_congr_pred :
    contributionSplitAsInfiniteTailPackage.certificate.RGToExponentBridge
      contributionSplitInfiniteTailCorrelationLength :=
  contributionSplitAsInfiniteTailPackage
    |>.rgToExponentBridge_of_analyticBridgeInputs_congr_predictedExponent
      (D := contributionSplitAsInfiniteTailPackage.certificate)
      rfl
      contributionSplitInfiniteTailAnalyticBridgeInputs


theorem contributionSplitInfiniteTail_valid_from_analyticInputs_congr_pred :
    contributionSplitAsInfiniteTailPackage.certificate.Valid
      contributionSplitInfiniteTailCorrelationLength :=
  contributionSplitAsInfiniteTailPackage
    |>.valid_of_analyticBridgeInputs_congr_predictedExponent
      (D := contributionSplitAsInfiniteTailPackage.certificate)
      rfl
      contributionSplitInfiniteTailAnalyticBridgeInputs


theorem
    contributionSplitInfiniteTail_hasCriticalNu_from_analyticInputs_congr_pred :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      contributionSplitInfiniteTailCorrelationLength
      contributionSplitAsInfiniteTailPackage.certificate.predictedExponent :=
  contributionSplitAsInfiniteTailPackage
    |>.hasCriticalNu_of_analyticBridgeInputs_congr_predictedExponent
      (D := contributionSplitAsInfiniteTailPackage.certificate)
      rfl
      contributionSplitInfiniteTailAnalyticBridgeInputs


theorem contributionSplitInfiniteTail_valid_from_analyticInputs :
    contributionSplitAsInfiniteTailPackage.certificate.Valid
      contributionSplitInfiniteTailCorrelationLength :=
  contributionSplitAsInfiniteTailPackage.valid_of_analyticBridgeInputs
    contributionSplitInfiniteTailAnalyticBridgeInputs


theorem contributionSplitInfiniteTail_hasCriticalNu_from_analyticInputs :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      contributionSplitInfiniteTailCorrelationLength
      contributionSplitAsInfiniteTailPackage.certificate.predictedExponent :=
  contributionSplitAsInfiniteTailPackage.hasCriticalNu_of_analyticBridgeInputs
    contributionSplitInfiniteTailAnalyticBridgeInputs


end PackageAnalyticBridgeExample
end Exact3D
end StatMech
