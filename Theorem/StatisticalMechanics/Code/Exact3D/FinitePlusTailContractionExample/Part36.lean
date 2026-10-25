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
import Def.StatisticalMechanics.Code.Exact3D.FinitePlusTailContractionExample.Part37


namespace StatMech

namespace Exact3D

namespace FinitePlusTailContractionExample

open InfiniteTailStableKeyPackageExample

open InfiniteTailGeneratedTablePackageExample

open InfiniteTailTableClosedBallRGPackage


theorem
    zeroTableClosedBallRGPackage_replacedTableWitnessAsResidual_residual_eq_two :
    zeroTableClosedBallRGPackage_replacedTableWitnessAsResidual.closedBallResidual =
      2 := by
  rw [zeroTableClosedBallRGPackage_replacedTableWitnessAsResidual]
  rw [with_tableWitness_as_closedBallResidual_closedBallResidual]
  exact
    rawRowsZeroInfiniteTailPackage_replacedTailEnvelope_budget_eq_two
      (d := 1) tableClosedBallCouplingCutoff


theorem zeroTableClosedBallRGPackage_replacedTableWitnessAsResidual_radius_eq :
    zeroTableClosedBallRGPackage_replacedTableWitnessAsResidual.closedBallRadius =
      5 := by
  rw [zeroTableClosedBallRGPackage_replacedTableWitnessAsResidual]
  rw [with_tableWitness_as_closedBallResidual_closedBallRadius]
  exact zeroTableClosedBallRGPackage_radiusFive_radius_eq


theorem
    zeroTableClosedBallRGPackage_replacedTableWitnessAsResidual_contraction_c_eq :
    (zeroTableClosedBallRGPackage_replacedTableWitnessAsResidual.closedBallContraction).c =
      (1 : ℝ) / 2 := by
  rw [zeroTableClosedBallRGPackage_replacedTableWitnessAsResidual]
  rw [with_tableWitness_as_closedBallResidual_closedBallContraction]
  exact zeroTableClosedBallRGPackage_radiusFive_contraction_c_eq


theorem zeroTableClosedBallRGPackage_replacedTableWitnessAsResidual_thermal_eq :
    zeroTableClosedBallRGPackage_replacedTableWitnessAsResidual.closedBallRG.thermal =
      3 :=
  rfl


theorem
    zeroTableClosedBallRGPackage_replacedTableWitnessAsResidual_budget_eq_two :
    zeroTableClosedBallRGPackage_replacedTableWitnessAsResidual.tableCertifiedTotalBound =
      2 := by
  rw [zeroTableClosedBallRGPackage_replacedTableWitnessAsResidual]
  rw [with_tableWitness_as_closedBallResidual_tableCertifiedTotalBound]
  exact
    rawRowsZeroInfiniteTailPackage_replacedTailEnvelope_budget_eq_two
      (d := 1) tableClosedBallCouplingCutoff


@[simp] theorem
    zeroTableClosedBallRGPackage_replacedTableWitnessAsResidual_certificate_eq
    (scale : BlockScale) :
    zeroTableClosedBallRGPackage_replacedTableWitnessAsResidual.certificate scale =
      zeroTableClosedBallRGPackage_radiusFive.certificate scale :=
  rfl


end FinitePlusTailContractionExample
end Exact3D
end StatMech
