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
import Def.StatisticalMechanics.Code.Exact3D.FinitePlusTailContractionExample.Part8


namespace StatMech

namespace Exact3D

namespace FinitePlusTailContractionExample

open InfiniteTailStableKeyPackageExample

open InfiniteTailGeneratedTablePackageExample

open InfiniteTailTableClosedBallRGPackage


theorem halfThirdScalingBlockBoundsComponentClosedBallCertificate_exists_fixedPoint
    {radius : ℝ} (hradius : 0 ≤ radius) :
    ∃ p : FinitePlusTailState 1 ℕ,
      halfThirdScalingBlockBounds.map p = p ∧
        FinitePlusTailState.ClosedBall zeroState radius p := by
  simpa [halfThirdScalingBlockBoundsComponentClosedBallCertificate,
    FinitePlusTailClosedBallContractionCertificate.fixedPoint] using
    (halfThirdScalingBlockBoundsComponentClosedBallCertificate
      hradius).exists_fixedPoint


theorem halfThirdScalingBlockBoundsComponentClosedBallCertificate_fixedPoint_isFixed
    {radius : ℝ} (hradius : 0 ≤ radius) :
    halfThirdScalingBlockBounds.map
      (halfThirdScalingBlockBoundsComponentClosedBallCertificate
        hradius).fixedPoint =
      (halfThirdScalingBlockBoundsComponentClosedBallCertificate
        hradius).fixedPoint := by
  simpa [halfThirdScalingBlockBoundsComponentClosedBallCertificate] using
    FinitePlusTailBlockBounds.toClosedBallCertificateOfComponentResiduals_fixedPoint_isFixed
      halfThirdScalingBlockBounds
      (c := (1 : ℝ) / 2)
      (by norm_num)
      (by norm_num)
      halfThirdScalingBlockBounds_finite_column
      halfThirdScalingBlockBounds_tail_column
      zeroState
      hradius
      halfThirdScalingBlockBounds_zero_finiteResidual
      halfThirdScalingBlockBounds_zero_tailResidual
      (by nlinarith)


theorem halfThirdScalingBlockBoundsFiniteResidualVectorClosedBallCertificate_fixedPoint_isFixed
    {radius : ℝ} (hradius : 0 ≤ radius) :
    halfThirdScalingBlockBounds.map
      (halfThirdScalingBlockBoundsFiniteResidualVectorClosedBallCertificate
        hradius).fixedPoint =
      (halfThirdScalingBlockBoundsFiniteResidualVectorClosedBallCertificate
        hradius).fixedPoint := by
  simpa [halfThirdScalingBlockBoundsFiniteResidualVectorClosedBallCertificate] using
    FinitePlusTailBlockBounds.toClosedBallCertificateOfFiniteResidualVector_fixedPoint_isFixed
      halfThirdScalingBlockBounds
      (c := (1 : ℝ) / 2)
      (by norm_num)
      (by norm_num)
      halfThirdScalingBlockBounds_finite_column
      halfThirdScalingBlockBounds_tail_column
      zeroState
      hradius
      halfThirdScalingBlockBounds_zero_finiteResidual_mem
      halfThirdScalingBlockBounds_zero_tailResidual
      (by
        rw [halfThirdScalingBlockBounds_zero_finiteResidual_absSum]
        nlinarith)


theorem halfThirdScalingCertificate_iterate_mem_thermalStableCone
    {thermal η t : ℝ} {s : FinitePlusTailState 1 ℕ}
    (hη : 0 ≤ η)
    (hdom : ((1 : ℝ) / 2) ≤ |thermal|)
    (hs : FinitePlusTailState.ThermalStableCone η t s)
    (k : ℕ) :
    FinitePlusTailState.ThermalStableCone η (thermal ^ k * t)
      (halfThirdScalingCertificate.iterate k s) :=
  halfThirdScalingCertificate.iterate_mem_thermalStableCone_of_c_le_abs_thermal
    halfThirdScalingCertificate_map_origin hη
    (by simpa [halfThirdScalingCertificate_c_eq] using hdom) hs k


end FinitePlusTailContractionExample
end Exact3D
end StatMech
