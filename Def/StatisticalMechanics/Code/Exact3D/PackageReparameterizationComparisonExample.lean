module
public import Theorem.StatisticalMechanics.Code.Exact3D.PackageReparameterizationBridgeExample.Part6
public import Theorem.StatisticalMechanics.Code.Exact3D.PackageComparisonBridge


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationComparisonExample.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Exact3D

namespace PackageReparameterizationComparisonExample

open FinitePlusTailContractionExample

open FiniteWitnessPackageExample

open PackageReparameterizationBridgeExample

open FinitePlusTailHyperbolicSplitting

open InfiniteTailTableClosedBallRGPackage


noncomputable def halfThirdScalingDoubledReparameterizedLength (β : ℝ) : ℝ :=
  halfThirdScalingDoublePrefactor β *
    halfThirdScalingReparameterizedLength β


end PackageReparameterizationComparisonExample
end Exact3D
end StatMech
