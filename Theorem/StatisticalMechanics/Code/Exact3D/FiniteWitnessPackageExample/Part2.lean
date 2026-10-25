/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackageExample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FiniteWitnessPackage.Part9
import Theorem.StatisticalMechanics.Code.Exact3D.TailSummabilityExample
import Def.StatisticalMechanics.Code.Exact3D.ToyRG.Part4
import Theorem.StatisticalMechanics.Code.Exact3D.Hierarchical.Part4
import Def.StatisticalMechanics.Code.Exact3D.FiniteWitnessPackageExample.Part2
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace FiniteWitnessPackageExample

theorem contributionSplitWitnessPackage_finiteChecks :
    contributionSplitWitnessPackage.certificate.FiniteChecks :=
  contributionSplitWitnessPackage.finiteChecks


theorem contributionSplitWitnessPackage_finiteCaseChecks :
    contributionSplitWitnessPackage.certificate.FiniteCaseChecks :=
  contributionSplitWitnessPackage.finiteCaseChecks


theorem contributionSplitWitnessPackage_tailBounds :
    contributionSplitWitnessPackage.certificate.TailBounds :=
  contributionSplitWitnessPackage.tailBounds


theorem contributionSplitWitnessPackage_fixedPointEnclosure :
    contributionSplitWitnessPackage.certificate.FixedPointEnclosure :=
  contributionSplitWitnessPackage.fixedPointEnclosure


theorem contributionSplitWitnessPackage_linearizationEnclosure :
    contributionSplitWitnessPackage.certificate.LinearizationEnclosure :=
  contributionSplitWitnessPackage.linearizationEnclosure


theorem contributionSplitWitnessPackage_hyperbolicSplitting :
    contributionSplitWitnessPackage.certificate.HyperbolicSplitting :=
  contributionSplitWitnessPackage.hyperbolicSplitting


theorem contributionSplitWitnessPackage_orbitEntry :
    contributionSplitWitnessPackage.certificate.OrbitEntry :=
  contributionSplitWitnessPackage.orbitEntry


theorem contributionSplitWitnessPackage_predictedExponent_eq :
    contributionSplitWitnessPackage.certificate.predictedExponent =
      Real.log exampleScale.toReal / Real.log 3 := by
  rfl


theorem contributionSplitWitnessPackage_valid_of_bridge
    (correlationLength : ℝ → ℝ)
    (hbridge :
      contributionSplitWitnessPackage.certificate.RGToExponentBridge
        correlationLength) :
    contributionSplitWitnessPackage.certificate.Valid correlationLength :=
  contributionSplitWitnessPackage.valid_of_bridge hbridge


theorem contributionSplitWitnessPackage_hasCriticalNu_of_bridge
    (correlationLength : ℝ → ℝ)
    (hbridge :
      contributionSplitWitnessPackage.certificate.RGToExponentBridge
        correlationLength) :
    HasCriticalNu (ToyCriticalModel exampleScale 3) correlationLength
      contributionSplitWitnessPackage.certificate.predictedExponent :=
  contributionSplitWitnessPackage.hasCriticalNu_of_bridge hbridge


theorem contributionSplitWitnessPackage_rgToExponentBridge_of_hasCriticalNu
    (correlationLength : ℝ → ℝ)
    (hν :
      HasCriticalNu (ToyCriticalModel exampleScale 3) correlationLength
        contributionSplitWitnessPackage.certificate.predictedExponent) :
    contributionSplitWitnessPackage.certificate.RGToExponentBridge
      correlationLength :=
  contributionSplitWitnessPackage.rgToExponentBridge_of_hasCriticalNu hν


theorem contributionSplitWitnessPackage_valid_of_hasCriticalNu
    (correlationLength : ℝ → ℝ)
    (hν :
      HasCriticalNu (ToyCriticalModel exampleScale 3) correlationLength
        contributionSplitWitnessPackage.certificate.predictedExponent) :
    contributionSplitWitnessPackage.certificate.Valid correlationLength :=
  contributionSplitWitnessPackage.valid_of_hasCriticalNu hν


end FiniteWitnessPackageExample
end Exact3D
end StatMech
