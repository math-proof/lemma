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
import Def.StatisticalMechanics.Code.Exact3D.FinitePlusTailContractionExample.Part53


namespace StatMech

namespace Exact3D

namespace FinitePlusTailContractionExample

open InfiniteTailStableKeyPackageExample

open InfiniteTailGeneratedTablePackageExample

open InfiniteTailTableClosedBallRGPackage


theorem genBoundedCaseReplacedPackage_residual_eq_two :
    genBoundedCaseReplacedPackage.closedBallResidual = 2 := by
  rw [genBoundedCaseReplacedPackage]
  rw [with_tableWitness_as_closedBallResidual_closedBallResidual]
  exact genBoundedCaseReplacedInfiniteTailPackage_budget_eq_two


theorem genBoundedCaseReplacedPackage_thermal_eq :
    genBoundedCaseReplacedPackage.closedBallRG.thermal = 3 :=
  rfl


theorem genBoundedCaseReplacedPackage_radius_eq :
    genBoundedCaseReplacedPackage.closedBallRadius = 5 := by
  rw [genBoundedCaseReplacedPackage]
  rw [with_tableWitness_as_closedBallResidual_closedBallRadius]
  exact genBoundedCaseRadiusFive_radius_eq


theorem genBoundedCaseReplacedPackage_contraction_c_eq :
    genBoundedCaseReplacedPackage.closedBallContraction.c = (1 : ℝ) / 2 := by
  rw [genBoundedCaseReplacedPackage]
  rw [with_tableWitness_as_closedBallResidual_closedBallContraction]
  exact genBoundedCaseRadiusFive_contraction_c_eq


theorem genBoundedCaseReplacedPackage_budget_eq_two :
    genBoundedCaseReplacedPackage.tableCertifiedTotalBound = 2 := by
  rw [genBoundedCaseReplacedPackage]
  rw [with_tableWitness_as_closedBallResidual_tableCertifiedTotalBound]
  exact genBoundedCaseReplacedInfiniteTailPackage_budget_eq_two


theorem genBoundedCaseReplacedPackage_budget_eq_residual :
    genBoundedCaseReplacedPackage.tableCertifiedTotalBound =
      genBoundedCaseReplacedPackage.closedBallResidual := by
  rw [genBoundedCaseReplacedPackage_budget_eq_two,
    genBoundedCaseReplacedPackage_residual_eq_two]


theorem genBoundedCaseReplacedPackage_tailTotalTsum_le_residual :
    genBoundedCaseReplacedPackage.tailTotalTsum ≤
      genBoundedCaseReplacedPackage.closedBallResidual :=
  genBoundedCaseReplacedPackage.tailTotalTsum_le_closedBallResidual


theorem genBoundedCaseReplacedPackage_tailTotalTsum_radius :
    genBoundedCaseReplacedPackage.tailTotalTsum +
        genBoundedCaseReplacedPackage.closedBallContraction.c *
      genBoundedCaseReplacedPackage.closedBallRadius ≤
      genBoundedCaseReplacedPackage.closedBallRadius :=
  InfiniteTailTableClosedBallRGPackage.tailTotalTsum_plus_mul_radius_le_radius
    genBoundedCaseReplacedPackage


@[simp] theorem genBoundedCaseReplacedPackage_certificate_eq
    (scale : BlockScale) :
    genBoundedCaseReplacedPackage.certificate scale =
      genBoundedCaseRadiusFive.certificate scale :=
  rfl


theorem genBoundedCaseReplacedPackage_predictedExponent_eq :
    (genBoundedCaseReplacedPackage.certificate
      FiniteWitnessPackageExample.exampleScale).predictedExponent =
        predictedNu FiniteWitnessPackageExample.exampleScale 3 :=
  by
    simpa using
      InfiniteTailTableClosedBallRGPackage.certificate_predictedExponent_eq
        genBoundedCaseReplacedPackage
        FiniteWitnessPackageExample.exampleScale


end FinitePlusTailContractionExample
end Exact3D
end StatMech
