module
public import Theorem.StatisticalMechanics.Code.Exact3D.WitnessReparameterizationBridge
public import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailReparameterizationBridge
public import Theorem.StatisticalMechanics.Code.Exact3D.TableClosedBallReparameterizationBridge
public import Theorem.StatisticalMechanics.Code.Exact3D.FiniteWitnessPackageExample.Part6
public import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailContractionExample.Part58
public import Theorem.StatisticalMechanics.Code.Exact3D.PackageComparisonBridgeExample.Part7
public import Theorem.StatisticalMechanics.Code.Exact3D.PackageReparameterizationBridgeExample


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Exact3D

namespace PackageReparameterizationBridgeExample

open FiniteWitnessPackageExample

open FinitePlusTailContractionExample

open InfiniteTailWitnessPackageExample

open PackageComparisonBridgeExample

open FiniteWitnessPackage

open FinitePlusTailHyperbolicSplitting


noncomputable def halfThirdScalingLinearReparam (β : ℝ) : ℝ :=
  LeftCriticalReparam.linearMap
    halfThirdScalingModel halfThirdScalingModel 2 β


noncomputable def halfThirdScalingReparameterizedLength (β : ℝ) : ℝ :=
  halfThirdScalingCorrelationLength (halfThirdScalingLinearReparam β)


end PackageReparameterizationBridgeExample
end Exact3D
end StatMech
