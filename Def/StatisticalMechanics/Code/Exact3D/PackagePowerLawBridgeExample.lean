module
public import Theorem.StatisticalMechanics.Code.Exact3D.WitnessPowerLawBridge
public import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailPowerLawBridge
public import Theorem.StatisticalMechanics.Code.Exact3D.TableClosedBallPowerLawBridge
public import Theorem.StatisticalMechanics.Code.Exact3D.PackageComparisonBridgeExample.Part7


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Exact3D

namespace PackagePowerLawBridgeExample

open PackageComparisonBridgeExample

open FiniteWitnessPackageExample

open FinitePlusTailContractionExample

open InfiniteTailWitnessPackageExample


noncomputable def contributionSplitWitnessPowerLawCorrelationLength
    (β : ℝ) : ℝ :=
  Real.exp
    (-contributionSplitWitnessPackage.certificate.predictedExponent *
      Real.log ((ToyCriticalModel exampleScale 3).betaC - β))


end PackagePowerLawBridgeExample
end Exact3D
end StatMech
