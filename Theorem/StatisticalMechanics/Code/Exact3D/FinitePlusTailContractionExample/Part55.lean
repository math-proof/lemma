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
import Def.StatisticalMechanics.Code.Exact3D.FinitePlusTailContractionExample.Part56


namespace StatMech

namespace Exact3D

namespace FinitePlusTailContractionExample

open InfiniteTailStableKeyPackageExample

open InfiniteTailGeneratedTablePackageExample

open InfiniteTailTableClosedBallRGPackage


theorem genCubicClassReplacedPackage_residual_eq_two :
    genCubicClassReplacedPackage.closedBallResidual = 2 := by
  rw [genCubicClassReplacedPackage]
  rw [with_tableWitness_as_closedBallResidual_closedBallResidual]
  exact genCubicClassReplacedInfiniteTailPackage_budget_eq_two


theorem genCubicClassReplacedPackage_thermal_eq :
    genCubicClassReplacedPackage.closedBallRG.thermal = 3 :=
  rfl


theorem genCubicClassReplacedPackage_radius_eq :
    genCubicClassReplacedPackage.closedBallRadius = 5 := by
  rw [genCubicClassReplacedPackage]
  rw [with_tableWitness_as_closedBallResidual_closedBallRadius]
  exact genCubicClassRadiusFive_radius_eq


theorem genCubicClassReplacedPackage_contraction_c_eq :
    genCubicClassReplacedPackage.closedBallContraction.c = (1 : ℝ) / 2 := by
  rw [genCubicClassReplacedPackage]
  rw [with_tableWitness_as_closedBallResidual_closedBallContraction]
  exact genCubicClassRadiusFive_contraction_c_eq


theorem genCubicClassReplacedPackage_budget_eq_two :
    genCubicClassReplacedPackage.tableCertifiedTotalBound = 2 := by
  rw [genCubicClassReplacedPackage]
  rw [with_tableWitness_as_closedBallResidual_tableCertifiedTotalBound]
  exact genCubicClassReplacedInfiniteTailPackage_budget_eq_two


theorem genCubicClassReplacedPackage_budget_eq_residual :
    genCubicClassReplacedPackage.tableCertifiedTotalBound =
      genCubicClassReplacedPackage.closedBallResidual := by
  rw [genCubicClassReplacedPackage_budget_eq_two,
    genCubicClassReplacedPackage_residual_eq_two]


theorem genCubicClassReplacedPackage_tailTotalTsum_le_residual :
    genCubicClassReplacedPackage.tailTotalTsum ≤
      genCubicClassReplacedPackage.closedBallResidual :=
  genCubicClassReplacedPackage.tailTotalTsum_le_closedBallResidual


theorem genCubicClassReplacedPackage_tailTotalTsum_radius :
    genCubicClassReplacedPackage.tailTotalTsum +
        genCubicClassReplacedPackage.closedBallContraction.c *
      genCubicClassReplacedPackage.closedBallRadius ≤
      genCubicClassReplacedPackage.closedBallRadius :=
  InfiniteTailTableClosedBallRGPackage.tailTotalTsum_plus_mul_radius_le_radius
    genCubicClassReplacedPackage


@[simp] theorem genCubicClassReplacedPackage_certificate_eq
    (scale : BlockScale) :
    genCubicClassReplacedPackage.certificate scale =
      genCubicClassRadiusFive.certificate scale :=
  rfl


theorem genCubicClassReplacedPackage_predictedExponent_eq :
    (genCubicClassReplacedPackage.certificate
      FiniteWitnessPackageExample.exampleScale).predictedExponent =
        predictedNu FiniteWitnessPackageExample.exampleScale 3 :=
  by
    simpa using
      InfiniteTailTableClosedBallRGPackage.certificate_predictedExponent_eq
        genCubicClassReplacedPackage
        FiniteWitnessPackageExample.exampleScale


end FinitePlusTailContractionExample
end Exact3D
end StatMech
