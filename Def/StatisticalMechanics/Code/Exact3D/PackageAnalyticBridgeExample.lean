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


namespace StatMech

namespace Exact3D

namespace PackageAnalyticBridgeExample

open PackageComparisonBridgeExample

open PackagePowerLawBridgeExample

open FiniteWitnessPackageExample

open FinitePlusTailContractionExample

open InfiniteTailWitnessPackageExample

open InfiniteTailTableClosedBallRGPackage


noncomputable def contributionSplitWitnessCorrelationLength (β : ℝ) : ℝ :=
  Real.exp
    (-contributionSplitWitnessPackage.certificate.predictedExponent *
      Real.log ((ToyCriticalModel exampleScale 3).betaC - β))


end PackageAnalyticBridgeExample
end Exact3D
end StatMech
