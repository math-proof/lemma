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
import Def.StatisticalMechanics.Code.Exact3D.FinitePlusTailContractionExample.Part39


namespace StatMech

namespace Exact3D

namespace FinitePlusTailContractionExample

open InfiniteTailStableKeyPackageExample

open InfiniteTailGeneratedTablePackageExample

open InfiniteTailTableClosedBallRGPackage


theorem generatedStableKeyReplacedTableClosedBallRGPackage_residual_eq_two :
    generatedStableKeyReplacedTableClosedBallRGPackage.closedBallResidual =
      2 := by
  rw [generatedStableKeyReplacedTableClosedBallRGPackage]
  rw [with_tableWitness_as_closedBallResidual_closedBallResidual]
  exact generatedStableKeyReplacedInfiniteTailPackage_budget_eq_two


theorem generatedStableKeyReplacedTableClosedBallRGPackage_thermal_eq :
    generatedStableKeyReplacedTableClosedBallRGPackage.closedBallRG.thermal =
      3 :=
  rfl


theorem generatedStableKeyReplacedTableClosedBallRGPackage_radius_eq :
    generatedStableKeyReplacedTableClosedBallRGPackage.closedBallRadius =
      5 := by
  rw [generatedStableKeyReplacedTableClosedBallRGPackage]
  rw [with_tableWitness_as_closedBallResidual_closedBallRadius]
  exact zeroTableClosedBallRGPackage_radiusFive_radius_eq


theorem generatedStableKeyReplacedTableClosedBallRGPackage_contraction_c_eq :
    generatedStableKeyReplacedTableClosedBallRGPackage.closedBallContraction.c =
      (1 : ℝ) / 2 := by
  rw [generatedStableKeyReplacedTableClosedBallRGPackage]
  rw [with_tableWitness_as_closedBallResidual_closedBallContraction]
  exact zeroTableClosedBallRGPackage_radiusFive_contraction_c_eq


theorem generatedStableKeyReplacedTableClosedBallRGPackage_budget_eq_two :
    generatedStableKeyReplacedTableClosedBallRGPackage.tableCertifiedTotalBound =
      2 := by
  rw [generatedStableKeyReplacedTableClosedBallRGPackage]
  rw [with_tableWitness_as_closedBallResidual_tableCertifiedTotalBound]
  exact generatedStableKeyReplacedInfiniteTailPackage_budget_eq_two


theorem
    generatedStableKeyReplacedTableClosedBallRGPackage_budget_eq_residual :
    generatedStableKeyReplacedTableClosedBallRGPackage.tableCertifiedTotalBound =
      generatedStableKeyReplacedTableClosedBallRGPackage.closedBallResidual := by
  rw [generatedStableKeyReplacedTableClosedBallRGPackage_budget_eq_two,
    generatedStableKeyReplacedTableClosedBallRGPackage_residual_eq_two]


theorem
    generatedStableKeyReplacedTableClosedBallRGPackage_tailTotalTsum_le_residual :
    generatedStableKeyReplacedTableClosedBallRGPackage.tailTotalTsum ≤
      generatedStableKeyReplacedTableClosedBallRGPackage.closedBallResidual :=
  generatedStableKeyReplacedTableClosedBallRGPackage.tailTotalTsum_le_closedBallResidual


theorem
    generatedStableKeyReplacedTableClosedBallRGPackage_tailTotalTsum_radius :
    generatedStableKeyReplacedTableClosedBallRGPackage.tailTotalTsum +
        generatedStableKeyReplacedTableClosedBallRGPackage.closedBallContraction.c *
      generatedStableKeyReplacedTableClosedBallRGPackage.closedBallRadius ≤
      generatedStableKeyReplacedTableClosedBallRGPackage.closedBallRadius :=
  InfiniteTailTableClosedBallRGPackage.tailTotalTsum_plus_mul_radius_le_radius
    generatedStableKeyReplacedTableClosedBallRGPackage


@[simp] theorem generatedStableKeyReplacedTableClosedBallRGPackage_certificate_eq
    (scale : BlockScale) :
    generatedStableKeyReplacedTableClosedBallRGPackage.certificate scale =
      zeroTableClosedBallRGPackage_radiusFive.certificate scale :=
  rfl


theorem
    generatedStableKeyReplacedTableClosedBallRGPackage_predictedExponent_eq :
    (generatedStableKeyReplacedTableClosedBallRGPackage.certificate
      FiniteWitnessPackageExample.exampleScale).predictedExponent =
        predictedNu FiniteWitnessPackageExample.exampleScale 3 :=
  by
    simpa using
      InfiniteTailTableClosedBallRGPackage.certificate_predictedExponent_eq
        generatedStableKeyReplacedTableClosedBallRGPackage
        FiniteWitnessPackageExample.exampleScale


end FinitePlusTailContractionExample
end Exact3D
end StatMech
