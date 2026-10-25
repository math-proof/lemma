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
import Def.StatisticalMechanics.Code.Exact3D.FinitePlusTailContractionExample.Part44


namespace StatMech

namespace Exact3D

namespace FinitePlusTailContractionExample

open InfiniteTailStableKeyPackageExample

open InfiniteTailGeneratedTablePackageExample

open InfiniteTailTableClosedBallRGPackage


theorem genMinCubicKeyReplacedTableClosedBallRGPackage_residual_eq_two :
    genMinCubicKeyReplacedTableClosedBallRGPackage.closedBallResidual =
      2 := by
  rw [genMinCubicKeyReplacedTableClosedBallRGPackage]
  rw [with_tableWitness_as_closedBallResidual_closedBallResidual]
  exact genMinCubicKeyReplacedInfiniteTailPackage_budget_eq_two


theorem genMinCubicKeyReplacedTableClosedBallRGPackage_thermal_eq :
    genMinCubicKeyReplacedTableClosedBallRGPackage.closedBallRG.thermal =
      3 :=
  rfl


theorem genMinCubicKeyReplacedTableClosedBallRGPackage_radius_eq :
    genMinCubicKeyReplacedTableClosedBallRGPackage.closedBallRadius =
      5 := by
  rw [genMinCubicKeyReplacedTableClosedBallRGPackage]
  rw [with_tableWitness_as_closedBallResidual_closedBallRadius]
  exact zeroTableClosedBallRGPackage_radiusFive_radius_eq


theorem genMinCubicKeyReplacedTableClosedBallRGPackage_contraction_c_eq :
    genMinCubicKeyReplacedTableClosedBallRGPackage.closedBallContraction.c =
      (1 : ℝ) / 2 := by
  rw [genMinCubicKeyReplacedTableClosedBallRGPackage]
  rw [with_tableWitness_as_closedBallResidual_closedBallContraction]
  exact zeroTableClosedBallRGPackage_radiusFive_contraction_c_eq


theorem genMinCubicKeyReplacedTableClosedBallRGPackage_budget_eq_two :
    genMinCubicKeyReplacedTableClosedBallRGPackage.tableCertifiedTotalBound =
      2 := by
  rw [genMinCubicKeyReplacedTableClosedBallRGPackage]
  rw [with_tableWitness_as_closedBallResidual_tableCertifiedTotalBound]
  exact genMinCubicKeyReplacedInfiniteTailPackage_budget_eq_two


theorem genMinCubicKeyReplacedTableClosedBallRGPackage_budget_eq_residual :
    genMinCubicKeyReplacedTableClosedBallRGPackage.tableCertifiedTotalBound =
      genMinCubicKeyReplacedTableClosedBallRGPackage.closedBallResidual := by
  rw [genMinCubicKeyReplacedTableClosedBallRGPackage_budget_eq_two,
    genMinCubicKeyReplacedTableClosedBallRGPackage_residual_eq_two]


theorem genMinCubicKeyReplacedTableClosedBallRGPackage_tailTsum_le_residual :
    genMinCubicKeyReplacedTableClosedBallRGPackage.tailTotalTsum ≤
      genMinCubicKeyReplacedTableClosedBallRGPackage.closedBallResidual :=
  genMinCubicKeyReplacedTableClosedBallRGPackage.tailTotalTsum_le_closedBallResidual


theorem genMinCubicKeyReplacedTableClosedBallRGPackage_tailTsum_radius :
    genMinCubicKeyReplacedTableClosedBallRGPackage.tailTotalTsum +
        genMinCubicKeyReplacedTableClosedBallRGPackage.closedBallContraction.c *
      genMinCubicKeyReplacedTableClosedBallRGPackage.closedBallRadius ≤
      genMinCubicKeyReplacedTableClosedBallRGPackage.closedBallRadius :=
  InfiniteTailTableClosedBallRGPackage.tailTotalTsum_plus_mul_radius_le_radius
    genMinCubicKeyReplacedTableClosedBallRGPackage


@[simp] theorem genMinCubicKeyReplacedTableClosedBallRGPackage_certificate_eq
    (scale : BlockScale) :
    genMinCubicKeyReplacedTableClosedBallRGPackage.certificate scale =
      zeroTableClosedBallRGPackage_radiusFive.certificate scale :=
  rfl


theorem genMinCubicKeyReplacedTableClosedBallRGPackage_predictedExponent_eq :
    (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate
      FiniteWitnessPackageExample.exampleScale).predictedExponent =
        predictedNu FiniteWitnessPackageExample.exampleScale 3 :=
  by
    simpa using
      InfiniteTailTableClosedBallRGPackage.certificate_predictedExponent_eq
        genMinCubicKeyReplacedTableClosedBallRGPackage
        FiniteWitnessPackageExample.exampleScale


end FinitePlusTailContractionExample
end Exact3D
end StatMech
