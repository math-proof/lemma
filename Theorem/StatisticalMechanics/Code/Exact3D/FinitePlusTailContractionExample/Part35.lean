/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.AnalyticBridgeTarget.Part3
import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailBlockRG.Part5
import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailClosedBallRG.Part5
import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailGeneratedTablePackageExample.Part5
import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailTableClosedBallRGPackage.Part6
import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailStableKeyPackageExample.Part7
import Def.StatisticalMechanics.Code.Exact3D.FinitePlusTailContractionExample.Part36


namespace StatMech

namespace Exact3D

namespace FinitePlusTailContractionExample

open InfiniteTailStableKeyPackageExample

open InfiniteTailGeneratedTablePackageExample

open InfiniteTailTableClosedBallRGPackage


theorem zeroTableClosedBallRGPackage_replacedTableWitness_thermal_eq :
    zeroTableClosedBallRGPackage_replacedTableWitness.closedBallRG.thermal =
      3 :=
  rfl


theorem zeroTableClosedBallRGPackage_replacedTableWitness_budget_eq_two :
    zeroTableClosedBallRGPackage_replacedTableWitness.tableCertifiedTotalBound =
      2 := by
  rw [zeroTableClosedBallRGPackage_replacedTableWitness]
  rw [InfiniteTailTableClosedBallRGPackage.with_tableWitness_tableCertifiedTotalBound]
  exact
    rawRowsZeroInfiniteTailPackage_replacedTailEnvelope_budget_eq_two
      (d := 1) tableClosedBallCouplingCutoff


@[simp] theorem zeroTableClosedBallRGPackage_replacedTableWitness_certificate_eq
    (scale : BlockScale) :
    zeroTableClosedBallRGPackage_replacedTableWitness.certificate scale =
      zeroTableClosedBallRGPackage_radiusFiveResidualTwo.certificate scale :=
  rfl


theorem zeroTableClosedBallRGPackage_replacedTableWitness_predictedExponent_eq :
    (zeroTableClosedBallRGPackage_replacedTableWitness.certificate
      FiniteWitnessPackageExample.exampleScale).predictedExponent =
        predictedNu FiniteWitnessPackageExample.exampleScale 3 :=
  by
    simpa [
      zeroTableClosedBallRGPackage_replacedTableWitness_thermal_eq
    ] using
      InfiniteTailTableClosedBallRGPackage.certificate_predictedExponent_eq
        zeroTableClosedBallRGPackage_replacedTableWitness
        FiniteWitnessPackageExample.exampleScale


end FinitePlusTailContractionExample
end Exact3D
end StatMech
