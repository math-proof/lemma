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
import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailContractionExample.Part56


namespace StatMech

namespace Exact3D

namespace FinitePlusTailContractionExample

open InfiniteTailStableKeyPackageExample

open InfiniteTailGeneratedTablePackageExample

open InfiniteTailTableClosedBallRGPackage


noncomputable def tailHalfMap (x : FinitePlusTailState 1 ℕ) : SummableTail ℕ :=
  SummableTail.scale ((1 : ℝ) / 2) x.tail


noncomputable def zeroFiniteBlockTailHalfCertificate :
    FinitePlusTailLipschitzCertificate 1 ℕ :=
  FinitePlusTailLipschitzCertificate.ofColumnSumFiniteBlock
    FiniteContraction.ZeroLinearExample.columnSumContraction
    FiniteContraction.ZeroLinearExample.matrix_mem_intervals
    tailHalfMap
    (finiteToTail := 0)
    (tailToTail := (1 : ℝ) / 2)
    (c := (1 : ℝ) / 2)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by
      norm_num [FiniteContraction.ZeroLinearExample.columnSumContraction])
    (by norm_num)
    (by
      intro x y
      simpa [tailHalfMap, FinitePlusTailState.tailDist] using
        le_of_eq (SummableTail.dist_scale ((1 : ℝ) / 2) x.tail y.tail))


end FinitePlusTailContractionExample
end Exact3D
end StatMech
