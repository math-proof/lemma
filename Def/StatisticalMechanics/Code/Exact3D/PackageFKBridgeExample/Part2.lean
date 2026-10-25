/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageFKBridgeExample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.CriticalExponentCriteria
import Theorem.StatisticalMechanics.Code.Exact3D.FKFinitePlusTailBridge
import Theorem.StatisticalMechanics.Code.Exact3D.FKTableClosedBallBridge
import Theorem.StatisticalMechanics.Code.Exact3D.FKWitnessBridge
import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailContractionExample.Part58
import Theorem.StatisticalMechanics.Code.Exact3D.FiniteWitnessPackageExample.Part6
import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailWitnessPackageExample.Part7
import Theorem.StatisticalMechanics.Code.Exact3D.PackageExponentMatchingExample
import Theorem.StatisticalMechanics.Code.Exact3D.PackageFKBridgeExample


namespace StatMech

namespace Exact3D

namespace PackageFKBridgeExample

open FiniteWitnessPackageExample

open FinitePlusTailContractionExample

open InfiniteTailWitnessPackageExample

open PackageExponentMatchingExample

variable
  (TFKM :
    FKMassPowerLawToIsingAnalyticRGToExponentTarget
      (halfThirdScalingRGCertificate.retarget Ising3DModel))


noncomputable def blockRGFKComposedIsingCorrelationLength (β : ℝ) : ℝ :=
  blockRGFKToyCorrelationLength (IsingFK.pOfBeta β)


end PackageFKBridgeExample
end Exact3D
end StatMech
