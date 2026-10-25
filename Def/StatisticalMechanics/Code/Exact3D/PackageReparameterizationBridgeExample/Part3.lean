/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.WitnessReparameterizationBridge
import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailReparameterizationBridge
import Theorem.StatisticalMechanics.Code.Exact3D.TableClosedBallReparameterizationBridge
import Theorem.StatisticalMechanics.Code.Exact3D.FiniteWitnessPackageExample.Part6
import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailContractionExample.Part58
import Theorem.StatisticalMechanics.Code.Exact3D.PackageComparisonBridgeExample.Part7
import Theorem.StatisticalMechanics.Code.Exact3D.PackageReparameterizationBridgeExample.Part2


namespace StatMech

namespace Exact3D

namespace PackageReparameterizationBridgeExample

open FiniteWitnessPackageExample

open FinitePlusTailContractionExample

open InfiniteTailWitnessPackageExample

open PackageComparisonBridgeExample

open FiniteWitnessPackage

open FinitePlusTailHyperbolicSplitting


noncomputable def toyLinearReparam (β : ℝ) : ℝ :=
  LeftCriticalReparam.linearMap
    (ToyCriticalModel exampleScale 3) (ToyCriticalModel exampleScale 3) 2 β


end PackageReparameterizationBridgeExample
end Exact3D
end StatMech
