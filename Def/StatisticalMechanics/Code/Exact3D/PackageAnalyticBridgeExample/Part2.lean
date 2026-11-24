module
public import Theorem.StatisticalMechanics.Code.Exact3D.WitnessAnalyticBridge
public import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailAnalyticBridge
public import Theorem.StatisticalMechanics.Code.Exact3D.TableClosedBallAnalyticBridge
public import Theorem.StatisticalMechanics.Code.Exact3D.PackagePowerLawBridgeExample
public import Theorem.StatisticalMechanics.Code.Exact3D.PackageAnalyticBridgeExample


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


noncomputable def contributionSplitWitnessAnalyticBridgeInputs :
    RGCertificate.AnalyticBridgeInputs
      contributionSplitWitnessPackage.certificate
      contributionSplitWitnessCorrelationLength True True True True :=
  RGCertificate.AnalyticBridgeInputs.of_eventually_exact_power
    contributionSplitWitnessCorrelationLength_exact_power


end PackageAnalyticBridgeExample
end Exact3D
end StatMech
